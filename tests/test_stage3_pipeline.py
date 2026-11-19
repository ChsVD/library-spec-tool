"""Regression tests for production Stage 3 audit, recovery, and source receipts."""

import json
from pathlib import Path
import shutil
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

from stage3.evidence import load_evidence
from stage3.exchange import Limits, NeedBudget, ReadTools, encode, exchange
from stage3.index import build_index
from stage3.pipeline import run


ROOT = Path(__file__).resolve().parents[1]
STAGE2 = ROOT / "runs/minimal-simplex-v2-20261118/stage2-link-evidence-clarified/stage2.json"


def action(tool, **fields):
    return json.dumps({"tool": tool, **fields}, ensure_ascii=False)


def report(need_id, **fields):
    return action("finish", report={"need_id": need_id, **fields})


def candidate(need_id, source_id, *, item_ids=("local",), items=None, references=(), condition="前提待查"):
    if items is None:
        items = [{"id": "local", "kind": "lemma", "title": "同一公共引理", "body": "结论只在已确认参数下成立。",
                  "source_ids": [], "depends_on": []}]
    return report(
        need_id, items=items, item_ids=list(item_ids), evidence_ids=[source_id],
        references=list(references), disposition="adaptation" if references else "new_content",
        coverage="partial", scope="允许讨论局部关系。", call_ids=[], object_mapping=[],
        conditions=[condition], remaining=["调用条件仍需单独核对。"],
        search={"status": "unnecessary", "reason": "已检查目标材料。"},
    )


def review(need_id, *, findings=()):
    return report(need_id, decision="revise" if findings else "accept", coverage="partial",
                  reason="逐处核对了前提。", upstream_questions=[],
                  checks={"direction": "pass", "target_conditions": "error" if findings else "gap",
                          "dependencies": "pass", "content": "pass"}, findings=list(findings))


class Stage3Pipeline(unittest.TestCase):
    def setUp(self):
        self.evidence = load_evidence(STAGE2)
        self.ids = list(self.evidence.needs)[:2]
        self.directory = TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.output = Path(self.directory.name) / "output"

    def launch(self, factory, **options):
        return run(stage2_result=STAGE2, output=self.output, model_factory=factory,
                   limits=Limits(max_requests=10), **options)

    def test_batch_and_compaction_keep_complete_original_excerpts(self):
        class VerboseIndex:
            def list_files(self, **options):
                return {"files": [{"id": f"file-{i}", "path": "repo/" + 200 * "x" + str(i),
                                   "role": "reference", "configuration": "z" * 30_000,
                                   "fragment": {"line": 1, "snippet": "frag" * 1000}}
                                  for i in range(20)], "offset": 0, "total": 100}

            def read_entry(self, ident):
                return {"id": ident, "file_id": "source", "path": "sample.v", "start_line": 1,
                        "end_line": 1, "file_sha256": "digest", "text": "exact raw excerpt"}

        limits = Limits(context_chars=12_000, max_requests=8)
        trace = {"actions": [], "delivered": [], "model_requests": 0, "target_read_chars": 0,
                 "reference_read_chars": 0, "protocol_errors": []}
        tools = ReadTools(VerboseIndex(), self.evidence, {}, NeedBudget(limits), trace)

        def model(messages, timeout):
            self.assertLessEqual(len(encode(messages)), limits.context_chars)
            if trace["model_requests"] == 1:
                return action("batch", actions=[{"tool": "list_files"},
                                                {"tool": "read_entry", "entry_id": "right"}])
            if trace["model_requests"] == 2:
                first, second = json.loads(messages[-1]["content"])["results"]
                self.assertNotIn("configuration", first["result"]["files"][0])
                self.assertEqual(second["result"]["text"], "exact raw excerpt")
            if trace.get("context_compactions"):
                memories = [json.loads(message["content"]) for message in messages[2:] if
                            message["role"] == "user" and "prior_original_excerpts" in message["content"]]
                self.assertEqual(memories[-1]["prior_original_excerpts"][0]["text"], "exact raw excerpt")
                return report(self.ids[0])
            return action("list_files")

        response = exchange(model, "writer", "Writer", {}, tools, lambda result, _: result)
        self.assertEqual(response["need_id"], self.ids[0])
        self.assertEqual(tools.budget.reads, 1)
        self.assertGreater(trace["context_compactions"], 0)

    def test_large_initial_packet_keeps_full_calls_accessible(self):
        # Select the largest call context from the frozen generic handoff.
        need = max(self.evidence.needs.values(), key=lambda value: len(value["calls"]))
        expected = need["calls"][0]

        def models(role, need_id):
            def model(messages, timeout):
                data = json.loads(messages[1]["content"])
                if role == "review":
                    record, = data["candidate_call_records"]
                    self.assertEqual(record["checks"], expected["checks"])
                    self.assertEqual(record["site"], expected["site"])
                    return review(need_id)
                self.assertNotIn("calls", data["target_material"])
                self.assertEqual(data["available_context"]["calls"], len(need["calls"]))
                if len(messages) == 2:
                    return action("list_context", category="calls", limit=1)
                if len(messages) == 4:
                    result = json.loads(messages[-1]["content"])
                    self.assertEqual(len(result["items"]), 1)
                    self.assertEqual(result["next_offset"], 1)
                    return action("read_context", category="calls", record_id=expected["call_id"])
                result = json.loads(messages[-1]["content"])
                self.assertEqual(result["record"]["checks"], expected["checks"])
                value = json.loads(candidate(need_id, data["target_sources"][0]["id"]))
                value["report"]["call_ids"] = [expected["call_id"]]
                return json.dumps(value, ensure_ascii=False)
            return model

        state = self.launch(models, need_ids=[need["id"]])
        self.assertEqual(state["uses"][need["id"]]["status"], "accepted")

    def test_revision_and_resume_preserve_distinct_uses_of_a_shared_item(self):
        def models(role, need_id):
            def model(messages, timeout):
                self.assertEqual(len(messages), 2)
                data = json.loads(messages[1]["content"])
                source_id = data["target_sources"][0]["id"]
                if role == "write":
                    if need_id == self.ids[0] and "previous_review" not in data:
                        return candidate(need_id, source_id, condition="unknown 已证明调用兼容。")
                    if need_id == self.ids[0]:
                        self.assertEqual(data["previous_review"]["review"]["decision"], "revise")
                    return candidate(need_id, source_id, condition=f"适用位置条件 {need_id}")
                self.assertNotIn("previous_review", data)
                condition, = data["candidate"]["conditions"]
                if condition == "unknown 已证明调用兼容。":
                    return review(need_id, findings=[{"quote": condition, "source_ids": [source_id],
                                                      "request": "保留调用条件未确认。"}])
                return review(need_id)
            return model

        first = self.launch(models, need_ids=self.ids, max_needs=1)
        self.assertEqual(list(first["uses"]), self.ids[:1])
        self.assertEqual(first["uses"][self.ids[0]]["usage"]["model_requests"], 4)
        second = self.launch(models, need_ids=self.ids, resume=True)
        self.assertEqual(len(second["items"]), 1)
        a, b = (second["uses"][ident] for ident in self.ids)
        self.assertEqual(a["item_ids"], b["item_ids"])
        self.assertNotEqual(a["conditions"], b["conditions"])
        self.assertEqual([row["review"]["decision"] for row in a["attempts"]], ["revise", "accept"])
        self.assertEqual(a["target_validation"], "not_run")
        markdown = (self.output / "stage3.md").read_text(encoding="utf-8")
        self.assertIn("同一公共引理", markdown)
        self.assertIn("调用条件仍需单独核对", markdown)

    def test_resume_revalidates_already_accepted_snapshot_files(self):
        original_stage1 = Path(json.loads(STAGE2.read_bytes())["stage1_result"])
        copy = Path(self.directory.name) / "stage1-copy"
        shutil.copytree(original_stage1.parent / "project", copy / "project")
        relocated = copy / original_stage1.name
        shutil.copy2(original_stage1, relocated)
        target = self.ids[0]

        def models(role, ident):
            def model(messages, timeout):
                if role == "write":
                    source = json.loads(messages[1]["content"])["target_sources"][0]
                    return candidate(ident, source["id"])
                return review(ident)
            return model

        first = self.launch(models, stage1_result=relocated, need_ids=[target])
        self.assertEqual(first["uses"][target]["status"], "accepted")
        accepted_source = first["uses"][target]["evidence"][0]
        file = copy / accepted_source["path"]
        correct = file.read_bytes()
        file.write_bytes(correct + b"\n/* file changed after commit */\n")
        no_model = lambda *_: self.fail("resume should reject before starting a new model")
        with self.assertRaisesRegex(ValueError, "resume cannot reuse committed evidence"):
            self.launch(no_model, stage1_result=relocated, need_ids=[target], resume=True)
        self.assertEqual(json.loads((self.output / "stage3.json").read_bytes()), first)
        file.write_bytes(correct)
        self.assertEqual(self.launch(no_model, stage1_result=relocated, need_ids=[target], resume=True), first)

    def test_revision_receives_writer_and_reviewer_sources_without_another_read(self):
        root = Path(self.directory.name)
        (root / "facts.v").write_text("Lemma alpha : True.\nLemma beta : True.\n", encoding="utf-8")
        manifest = {"libraries": [{"id": "proofs", "root": str(root), "role": "reference"}]}
        index = build_index(manifest)
        file_id = index.list_files()["files"][0]["id"]
        entries = index.list_entries(file_id)["entries"]
        alpha, beta = (row["id"] for row in entries)
        target = self.ids[0]

        def draft(need_id, source_id, references, condition):
            value = json.loads(candidate(need_id, source_id, condition=condition,
                                         references=[{"entry_id": ident, "usage": "核对条件。"}
                                                     for ident in references]))
            value["report"]["search"] = {"status": "searched", "reason": "查看两项候选。"}
            return json.dumps(value, ensure_ascii=False)

        def models(role, need_id):
            def model(messages, timeout):
                data = json.loads(messages[1]["content"])
                source_id = data["target_sources"][0]["id"]
                if role == "write":
                    if "previous_review" in data:
                        sources = data["previous_review"]["cited_sources"]
                        self.assertEqual({source["id"] for source in sources}, {alpha, beta})
                        self.assertTrue(all(source["text"].startswith("Lemma ") for source in sources))
                        return draft(need_id, source_id, [alpha, beta], "新证据下的条件")
                    if len(messages) == 2:
                        return action("list_entries", file_id=file_id)
                    if len(messages) == 4:
                        return action("read_entry", entry_id=alpha)
                    return draft(need_id, source_id, [alpha], "漏了一个条件")
                if data["candidate"]["conditions"] == ["新证据下的条件"]:
                    return review(need_id)
                if len(messages) == 2:
                    return action("read_entry", entry_id=beta)
                return review(need_id, findings=[{"quote": "漏了一个条件", "source_ids": [beta],
                                                  "request": "纳入第二条依据。"}])
            return model

        result = run(stage2_result=STAGE2, output=self.output, model_factory=models,
                     reference_manifest=manifest, need_ids=[target], limits=Limits(max_reads=2))
        row = result["uses"][target]
        self.assertEqual(row["status"], "accepted")
        self.assertEqual([citation["entry_id"] for citation in row["references"]], [alpha, beta])
        self.assertEqual(row["usage"]["reference_read_deliveries"], 2)
        self.assertGreater(row["usage"]["forwarded_reference_chars"], row["usage"]["reference_read_chars"])
        self.assertEqual(len(row["search"]["scope"]), 1)

    def test_unread_references_and_read_failure_remain_retryable(self):
        root = Path(self.directory.name)
        (root / "facts.v").write_text("Lemma sample : True.\nProof. exact I. Qed.\n", encoding="utf-8")
        manifest = {"libraries": [{"id": "proofs", "root": str(root), "role": "reference"}]}
        index = build_index(manifest)
        file_id = index.list_files()["files"][0]["id"]
        entry_id = index.list_entries(file_id)["entries"][0]["id"]
        target = self.ids[0]

        def failing_models(role, need_id):
            self.assertEqual(role, "write")

            def model(messages, timeout):
                source_id = json.loads(messages[1]["content"])["target_sources"][0]["id"]
                if len(messages) == 2:
                    return action("read_entry", entry_id=entry_id)
                return candidate(need_id, source_id,
                                 references=[{"entry_id": entry_id, "usage": "用于核对。"}])
            return model

        with (patch("stage3.index.build_index", return_value=index),
              patch.object(index, "read_entry", side_effect=OSError("input temporarily unavailable"))):
            first = self.launch(failing_models, reference_manifest=manifest, need_ids=[target])
        use = first["uses"][target]
        self.assertEqual(use["status"], "retryable")
        self.assertEqual(use["usage"]["read_errors"][0]["location"]["start_line"], 1)
        self.assertIn("was not delivered", use["failure"]["reason"])
        self.assertFalse(first["items"])

        def healthy_models(role, need_id):
            def model(messages, timeout):
                data = json.loads(messages[1]["content"])
                source_id = data["target_sources"][0]["id"]
                if role == "review":
                    self.assertEqual([value["id"] for value in data["cited_sources"]], [entry_id])
                    return review(need_id)
                if len(messages) == 2:
                    return action("read_entry", entry_id=entry_id)
                return candidate(need_id, source_id,
                                 references=[{"entry_id": entry_id, "usage": "用于核对。"}])
            return model

        final = self.launch(healthy_models, reference_manifest=manifest, need_ids=[target], resume=True)
        row = final["uses"][target]
        self.assertEqual(row["status"], "accepted")
        self.assertEqual(row["previous_attempts"][0]["status"], "retryable")
        self.assertIn("Lemma sample", final["sources"][entry_id]["text"])
        (root / "facts.v").write_text("Lemma changed : True.\n", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "resume inputs"):
            self.launch(healthy_models, reference_manifest=manifest, need_ids=[target], resume=True)
