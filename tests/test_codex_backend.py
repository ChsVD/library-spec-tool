import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
import uuid

from stage1.codex_backend import (BackendError, CodexModel, DISABLED_FEATURES,
    classify_failure, failure_details, isolated_command, minimal_environment, model_preferences,
    parse_events, subprocess_text)


class CodexTests(unittest.TestCase):
    def test_model_whitelist(self):
        with tempfile.TemporaryDirectory() as directory:
            (Path(directory) / 'config.toml').write_text('model="configured"\nmodel_reasoning_effort="low"\nsecret="DO_NOT_COPY"\n')
            self.assertEqual(model_preferences(directory), {'model': 'configured', 'model_reasoning_effort': 'low'})

    @unittest.skipUnless(sys.platform == 'linux' and shutil.which('bwrap') and shutil.which('codex'), 'requires local Codex runtime')
    def test_explicit_model_and_effort_override_config(self):
        with tempfile.TemporaryDirectory() as directory:
            (Path(directory) / 'auth.json').write_text('{}')
            (Path(directory) / 'config.toml').write_text('model="gpt-6-astra"\nmodel_reasoning_effort="low"\n')
            model = CodexModel('gpt-6.1-sol', codex_home=directory, reasoning_effort='high')
            self.assertEqual(model.model, 'gpt-6.1-sol')
            self.assertEqual(model.effort, 'high')
            self.assertEqual(model.metadata()['reasoning_effort_source'], 'explicit')
            self.assertIn('model_reasoning_effort="high"', model.arguments())
            self.assertEqual(CodexModel(codex_home=directory).effort, 'low')

    def test_minimal_environment(self):
        with patch.dict(os.environ, {'OPENAI_API_KEY': 'secret', 'OPENAI_BASE_URL': 'bad',
                                     'CODEX_HOME': '/bad', 'HTTPS_PROXY': 'transport'}, clear=True):
            env = minimal_environment()
        self.assertNotIn('OPENAI_API_KEY', env)
        self.assertNotIn('OPENAI_BASE_URL', env)
        self.assertEqual(env['CODEX_HOME'], '/home/stage1/.codex')
        self.assertEqual(env['HTTPS_PROXY'], 'transport')

    def test_mounts_do_not_expose_projects_or_home(self):
        args = isolated_command('/usr/local/bin/codex', '/home/user/.codex/auth.json', [])
        mounts = [args[i+1:i+3] for i, v in enumerate(args) if v in ('--ro-bind', '--bind')]
        self.assertNotIn(['/home', '/home'], mounts)
        self.assertFalse(any('Projects' in source for source, _ in mounts))
        self.assertIn(['/home/user/.codex/auth.json', '/home/stage1/.codex/auth.json'], mounts)
        self.assertNotIn('--bind', args)

    def test_native_capabilities_disabled(self):
        model = object.__new__(CodexModel)
        model.model, model.effort = 'configured', 'low'
        args = model.arguments()
        self.assertIn('--ignore-user-config', args)
        self.assertIn('mcp_servers={}', args)
        self.assertIn('web_search="disabled"', args)
        self.assertIn('project_doc_max_bytes=0', args)
        self.assertTrue({'shell_tool', 'plugins', 'apps', 'multi_agent', 'hooks'} <= set(DISABLED_FEATURES))

    def events(self, item_type='agent_message', complete=True):
        rows = [{'type': 'item.completed', 'item': {'type': item_type, 'text': '{"tool":"checkpoint","note":"ok"}'}}]
        if complete:
            rows.append({'type': 'turn.completed'})
        return '\n'.join(json.dumps(row) for row in rows)

    def test_event_parser_requires_completed_text_and_no_native_calls(self):
        result, _ = parse_events(self.events())
        self.assertEqual(json.loads(result)['tool'], 'checkpoint')
        for stream in [self.events(complete=False), self.events('command_execution'),
                       json.dumps({'type': 'turn.failed', 'error': {'message': 'secret'}})]:
            with self.assertRaises(BackendError):
                parse_events(stream)

    def test_failure_classification_redacts_raw_text(self):
        for raw in ['401 token=SECRET', 'bwrap: SECRET', '429 SECRET', 'connection SECRET', 'unknown feature SECRET']:
            result = classify_failure('', raw, 1)
            self.assertNotIn('SECRET', result)

    def test_terminal_error_overrides_unrelated_timeout_warning(self):
        stream=json.dumps({'type':'turn.failed','error':{'message':'context_length_exceeded'}})
        self.assertIn('request size/context',classify_failure(stream,'models listing timed out',1))
    def test_normal_model_prose_cannot_classify_unknown_failure(self):
        stream=json.dumps({'type':'item.completed','item':{'type':'agent_message','text':'401 connection quota secret'}})
        stream+='\n'+json.dumps({'type':'turn.failed','error':{'message':'unknown error'}})
        self.assertIn('Codex failed',classify_failure(stream,'',1))
    def test_failure_signals_are_allowlisted_and_separate(self):
        stream=json.dumps({'type':'turn.failed','error':{'message':'stream disconnected; unexpected status code: 502 https://secret.invalid?token=SECRET'}})
        details=failure_details(stream,'models listing timed out SECRET',1)
        self.assertEqual(details['terminal_http_status_codes'],['502'])
        self.assertIn('stream disconnected',details['terminal_signals'])
        self.assertNotIn('timed out',details['terminal_signals'])
        self.assertIn('timed out',details['stderr_signals'])
        self.assertNotIn('SECRET',json.dumps(details));self.assertNotIn('secret.invalid',json.dumps(details))
    def test_successful_native_notice_not_terminal_error(self):
        stream=json.dumps({'type':'item.completed','item':{'type':'error','message':'Code Mode is unavailable because code-mode host is disabled.'}})
        stream+='\n'+self.events()
        parse_events(stream)
        self.assertEqual(failure_details(stream,'timed out',0)['terminal_event_types'],[])

    @unittest.skipUnless(sys.platform == 'linux', 'requires process groups')
    def test_process_timeout_reaps_group(self):
        with self.assertRaisesRegex(BackendError, 'timed out'):
            subprocess_text([sys.executable, '-c', 'import time; time.sleep(30)'], '', .15, minimal_environment())

    @unittest.skipUnless(sys.platform == 'linux' and shutil.which('bwrap'), 'requires bubblewrap')
    def test_bwrap_visibility_and_timeout_descendants(self):
        with tempfile.TemporaryDirectory() as directory:
            auth = Path(directory) / 'auth.json'
            auth.write_text('{}')  # Fake credential file; test never reads real credentials.
            hidden = Path(directory) / 'outside'
            hidden.write_text('must remain outside')
            program = 'import os,json; print(json.dumps([os.path.exists(' + repr(str(hidden)) + '),os.path.exists("/home/stage1/.codex/auth.json")]))'
            code, stdout, stderr = subprocess_text(isolated_command('/usr/bin/python3', auth, ['-c', program]), '', 10, minimal_environment())
            self.assertEqual(code, 0)
            self.assertEqual(json.loads(stdout), [False, True])
            marker = 'stage1-timeout-' + uuid.uuid4().hex
            child = 'import time; time.sleep(30)'
            parent = 'import subprocess,time; subprocess.Popen(["/usr/bin/python3","-c",' + repr(child) + ',' + repr(marker) + ']); time.sleep(30)'
            command = isolated_command('/usr/bin/python3', auth, ['-c', parent, marker])
            with self.assertRaisesRegex(BackendError, 'timed out'):
                subprocess_text(command, '', .4, minimal_environment())
            time.sleep(.1)
            remaining = []
            for path in Path('/proc').glob('[0-9]*/cmdline'):
                try:
                    if marker.encode() in path.read_bytes():
                        remaining.append(path.parent.name)
                except OSError:
                    pass
            self.assertEqual(remaining, [], 'bwrap session descendants survived timeout')


if __name__ == '__main__':
    unittest.main()
