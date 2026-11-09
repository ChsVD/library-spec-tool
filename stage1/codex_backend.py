"""Codex CLI text backend, isolated from project files with bubblewrap.

The existing auth file is mounted read-only for the CLI; its contents are never
read, copied, or parsed by this module. Reader remains the only project reader.
"""
import json
import os
import re
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tomllib


class BackendError(RuntimeError):
    """A deliberately sanitized, actionable backend diagnostic."""
    def __init__(self, message, *, details=None):
        super().__init__(message)
        self.details = details



class BackendProtocolError(BackendError):
    """Only completed model text, never raw CLI stdout/stderr or login data."""
    def __init__(self, response, error):
        super().__init__('Codex final response is not one JSON action object. Retry with the task contract.')
        self.response = response[:8000]
        self.original_chars = len(response)
        self.parse_error = {'message':getattr(error,'msg','JSON action must be an object'),
                            'line':getattr(error,'lineno',None),'column':getattr(error,'colno',None),
                            'position':getattr(error,'pos',None)}


class BackendTimeout(BackendError):
    """A confirmed subprocess deadline, distinct from connection/auth failures."""


DISABLED_FEATURES = (
    'shell_tool', 'shell_snapshot', 'apps', 'plugins', 'remote_plugin', 'hooks',
    'browser_use', 'browser_use_external', 'browser_use_full_cdp_access',
    'computer_use', 'in_app_browser', 'multi_agent', 'multi_agent_v2',
    'code_mode', 'code_mode_host', 'view_image', 'image_generation',
    'memories', 'skill_search', 'skill_mcp_dependency_install',
    'workspace_dependencies', 'goals', 'sleep_tool', 'tool_suggest',
)


def model_preferences(home):
    """Return only the non-secret model and effort whitelist, never provider/auth."""
    path = Path(home) / 'config.toml'
    if not path.is_file():
        return {}
    try:
        data = tomllib.loads(path.read_text(encoding='utf-8'))
    except (OSError, ValueError):
        raise BackendError('Codex configuration cannot be parsed; repair config.toml before running this adapter.') from None
    return {key: data[key] for key in ('model', 'model_reasoning_effort')
            if isinstance(data.get(key), str)}


def isolated_command(codex, auth_file, arguments):
    """Only runtime files, TLS/DNS configuration, and the exact auth file mounted."""
    command = [shutil.which('bwrap') or 'bwrap', '--die-with-parent', '--unshare-all',
               '--share-net', '--new-session', '--ro-bind', '/usr', '/usr',
               '--symlink', 'usr/bin', '/bin', '--symlink', 'usr/lib', '/lib',
               '--symlink', 'usr/lib64', '/lib64', '--proc', '/proc', '--dev', '/dev',
               '--tmpfs', '/tmp', '--dir', '/work', '--dir', '/home/stage1/.codex',
               '--ro-bind', str(auth_file), '/home/stage1/.codex/auth.json',
               '--ro-bind', '/etc/ssl/certs', '/etc/ssl/certs']
    for filename in ('resolv.conf', 'hosts', 'nsswitch.conf'):
        path = '/etc/' + filename
        if Path(path).exists():
            command += ['--ro-bind', path, path]
    command += ['--chdir', '/work', '--', codex, *arguments]
    return command


def minimal_environment():
    # Only explicit standard proxy transport settings; no provider/auth/tool overrides.
    env = {'PATH': '/usr/local/bin:/usr/bin:/bin', 'HOME': '/home/stage1',
            'CODEX_HOME': '/home/stage1/.codex', 'LANG': 'C.UTF-8',
            'SSL_CERT_FILE': '/etc/ssl/certs/ca-certificates.crt'}
    for key in ('HTTP_PROXY', 'HTTPS_PROXY', 'NO_PROXY', 'http_proxy', 'https_proxy', 'no_proxy'):
        if os.environ.get(key):
            env[key] = os.environ[key]
    return env


def subprocess_text(command, text, timeout, env):
    """Kill and reap the complete process group on timeout or cancellation."""
    process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, text=True, encoding='utf-8',
                               env=env, cwd='/', start_new_session=True)
    try:
        stdout, stderr = process.communicate(text, timeout=timeout)
    except BaseException as exc:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.communicate()
        if isinstance(exc, subprocess.TimeoutExpired):
            raise BackendTimeout('Codex timed out; its process group was stopped. Increase the time budget or check connectivity.') from None
        raise
    return process.returncode, stdout, stderr


FAILURE_PHRASES = (
    'stream disconnected', 'error sending request', 'error decoding response body',
    'connection reset', 'connection refused', 'connection closed', 'timed out',
    'dns', 'tls', 'certificate', 'unexpected eof', 'bad gateway', 'service unavailable',
    'internal server error', 'too many requests', 'usage limit', 'rate limit', 'quota',
    'unauthorized', 'forbidden', 'refresh token', 'refresh_token', 'read-only file system',
    'context_length_exceeded', 'context window', 'request too large', 'payload too large',
    'invalid request', 'websocket', 'retries exhausted', 'before completion',
)


def terminal_errors(stdout):
    """Only terminal CLI errors; exclude ordinary model text and nonfatal notices."""
    result=[]
    for line in stdout.splitlines():
        try: event=json.loads(line)
        except ValueError: continue
        if isinstance(event,dict) and event.get('type') in ('error','turn.failed'):
            result.append(event)
    return result


def failure_details(stdout, stderr, code):
    """Persist fixed allowlisted signals, never raw messages, URLs or credentials."""
    events=terminal_errors(stdout)
    terminal=json.dumps(events).lower()
    def signals(text):return [p for p in FAILURE_PHRASES if p in text.lower()]
    def statuses(text):
        return sorted(set(re.findall(r'(?:status(?: code)?|http(?:/\d(?:\.\d)?)?)[: =]+([45]\d\d)\b',text.lower())))
    return {'exit_code':code,'terminal_event_types':[e['type'] for e in events],
            'terminal_signals':signals(terminal),'stderr_signals':signals(stderr),
            'terminal_http_status_codes':statuses(terminal),'stderr_http_status_codes':statuses(stderr)}


def classify_failure(stdout, stderr, code):
    """Classify transient raw diagnostics in memory; never persist raw stderr."""
    events = terminal_errors(stdout)
    # A terminal error takes precedence over unrelated startup warnings or model prose.
    diagnostic = (json.dumps(events) if events else stderr).lower()
    if 'bwrap:' in diagnostic:
        return 'Bubblewrap isolation failed. Check WSL/Linux namespace support; no unsandboxed fallback is used.'
    if any(word in diagnostic for word in ('401', 'unauthorized', 'refresh token', 'refresh_token', 'not logged in', 'authentication', 'read-only file system')):
        return 'Codex authentication or refresh failed. Run codex login in the normal WSL environment, then retry; auth is read-only here.'
    if any(word in diagnostic for word in ('429', 'usage limit', 'rate limit', 'quota')):
        return 'Codex usage limit reached. Wait for reset or check the signed-in account limits.'
    if any(word in diagnostic for word in ('context_length_exceeded', 'context window', 'request too large', 'payload too large')):
        return 'Codex request size/context limit rejected the request. Reduce the supplied context; this is not a connection diagnosis.'
    if any(word in diagnostic for word in ('timed out', 'dns', 'connection', 'network', 'failed to connect', 'stream disconnected')):
        return 'Codex connection failed. Check WSL DNS/TLS and standard HTTP(S) proxy access; custom provider overrides are not inherited.'
    if any(word in diagnostic for word in ('unknown feature', 'unexpected argument', 'config', 'unknown field')):
        return 'Codex CLI configuration is incompatible. This backend was tested with 0.154.0; inspect supported flags/features before updating the adapter.'
    if 'model' in diagnostic and any(word in diagnostic for word in ('not found', 'not supported', 'unavailable')):
        return 'The configured Codex model is unavailable for this account. Select an available model in Codex or pass --model.'
    return f'Codex failed (exit {code}). Check codex login status and CLI compatibility; raw diagnostics withheld to avoid credential leakage.'


def parse_events(stdout):
    messages, event_types = [], []
    for line in stdout.splitlines():
        try:
            event = json.loads(line)
        except ValueError:
            continue
        kind = event.get('type')
        event_types.append(kind)
        if kind in ('turn.failed', 'error'):
            raise BackendError(classify_failure(stdout, '', 1), details=failure_details(stdout, '', 1))
        if kind == 'item.completed':
            item = event.get('item', {})
            if item.get('type') == 'agent_message':
                messages.append(item.get('text', ''))
            elif item.get('type') == 'error' and item.get('message', '').startswith(
                    'Code Mode is unavailable because code-mode host is disabled.'):
                # Expected fail-closed notice in CLI 0.154.0 when disabling this runtime.
                continue
            elif item.get('type') not in ('reasoning', 'todo_list'):
                # Additional diagnostic only. Isolation/configuration enforce the boundary.
                raise BackendError('Codex emitted an unexpected native tool event. Analysis stopped; review CLI compatibility.')
    if 'turn.completed' not in event_types:
        raise BackendError('Codex stream ended without turn.completed; partial text is not accepted.')
    if not messages:
        raise BackendError('Codex returned no final text message; check CLI event compatibility.')
    answer = messages[-1].strip()
    try:
        action = json.loads(answer)
        if not isinstance(action, dict):
            raise ValueError()
    except ValueError as exc:
        raise BackendProtocolError(answer,exc) from None
    return answer, event_types


class CodexModel:
    def __init__(self, model=None, codex_home=None, reasoning_effort=None):
        if sys.platform != 'linux' or not shutil.which('bwrap'):
            raise BackendError('Codex backend requires Linux/WSL and bwrap; no weaker fallback is enabled.')
        self.codex = shutil.which('codex')
        if not self.codex or not Path(self.codex).resolve().is_relative_to('/usr'):
            raise BackendError('Install/use the existing Codex CLI under /usr (including /usr/local); custom executable locations are not mounted.')
        home = Path(codex_home) if codex_home else Path.home() / '.codex'
        self.auth_file = (home / 'auth.json').resolve()
        if not self.auth_file.is_file():
            raise BackendError('No file-based WSL Codex login found. Run codex login in WSL; desktop/keyring-only authentication is not supported by this adapter.')
        preferences = model_preferences(home)
        self.model = model or preferences.get('model')
        self.effort = reasoning_effort or preferences.get('model_reasoning_effort')
        self.effort_source = 'explicit' if reasoning_effort else 'codex_config_whitelist' if self.effort else 'codex_cli_default'
        self.model_source = 'explicit' if model else 'codex_config_whitelist' if self.model else 'codex_cli_default'
        self.last_event_types = []

    def arguments(self):
        args = ['exec', '--ignore-user-config', '--ignore-rules', '--ephemeral',
                '--skip-git-repo-check', '--json', '--color', 'never', '--sandbox', 'read-only',
                '-C', '/work', '-c', 'web_search="disabled"', '-c', 'mcp_servers={}',
                '-c', 'project_doc_max_bytes=0', '-c', 'model_provider="openai"',
                '-c', 'forced_login_method="chatgpt"', '-c', 'history.persistence="none"',
                '-c', 'analytics.enabled=false', '-c', 'feedback.enabled=false']
        for feature in DISABLED_FEATURES:
            args += ['--disable', feature]
        if self.model:
            args += ['--model', self.model]
        if self.effort:
            args += ['-c', 'model_reasoning_effort=' + json.dumps(self.effort)]
        return args + ['-']

    def __call__(self, messages, timeout):
        prompt = ('You are a text-only stage-1 analysis engine. Return exactly one JSON action object. '
                  'Do not invoke native tools. The orchestrator executes Reader actions. '
                  'The following JSON contains the complete conversation; system content is the task, '
                  'user content after it is tool feedback, assistant content is prior actions.\n' +
                  json.dumps(messages, ensure_ascii=False))
        command = isolated_command(self.codex, self.auth_file, self.arguments())
        code, stdout, stderr = subprocess_text(command, prompt, timeout, minimal_environment())
        if code != 0:
            raise BackendError(classify_failure(stdout, stderr, code), details=failure_details(stdout, stderr, code))
        answer, self.last_event_types = parse_events(stdout)
        return answer

    def metadata(self):
        return {'backend': 'codex', 'codex_executable': self.codex, 'model': self.model or 'codex_cli_default',
                'model_source': self.model_source, 'reasoning_effort': self.effort,
                'reasoning_effort_source': self.effort_source,
                'authentication': 'existing WSL ChatGPT login; read-only auth mount',
                'isolation': 'bubblewrap minimal filesystem; no project mounts',
                'disabled_features': list(DISABLED_FEATURES)}
