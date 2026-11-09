import json
import tempfile
import unittest
from pathlib import Path
from stage1.reader import Reader
from stage1.task import run_task, Budgets
from stage1.contracts import check_evidence
from stage3.read_materials import SourcePreparation
from stage4.materials import local_context, prepare


class MaterialDeliveryTests(unittest.TestCase):
    def setUp(self):
        tmp=tempfile.TemporaryDirectory();self.addCleanup(tmp.cleanup)
        self.base=Path(tmp.name);self.root=self.base/"input";self.root.mkdir()
        (self.root/"a.c").write_text('int a;\nint b;\n')
        self.reader=Reader(self.root,self.base/"reads.jsonl")

    def task(self,name,model,validator=lambda *_:[],**kwargs):
        return run_task(self.root,self.base/name,model,"test",validator,role="extract",
            task_id=name,budgets=kwargs.pop("budgets",Budgets(calls=8,seconds=30,
                context_chars=60000,reserve_seconds=0,reserve_chars=1000)),
            **kwargs)

    def test_single_file_search_paginates_without_skipping_matches_or_credit(self):
        (self.root/"many.h").write_text("\n".join("needle "+str(i)+"x"*400 for i in range(65)))
        action={"tool":"search","path":"many.h","query":"needle","limit":7}
        found=[]
        while action:
            result=self.reader.execute(action)
            self.assertNotIn("error",result)
            self.assertLessEqual(len(result["matches"]),7)
            self.assertTrue(all(len(x["text"])<=160 for x in result["matches"]))
            found.extend(x["line"] for x in result["matches"])
            action=result["next_action"]
        self.assertEqual(found,list(range(1,66)))
        self.assertEqual(self.reader.reads,{})

    def test_batch_delivers_evidence_and_keeps_partial_errors_explicit(self):
        actions=iter([
            {"tool":"batch","actions":[{"tool":"read","path":"a.c","start":1,"count":1},
                                      {"tool":"read","path":"../outside","start":1,"count":1},
                                      {"tool":"read","path":"a.c","start":2,"count":1}]},
            {"tool":"finish","report":{}}])
        def model(messages,timeout):
            if len(messages)>1:
                feedback=json.loads(messages[-1]["content"])
                self.assertIn("error",feedback["results"][1]["result"])
            return json.dumps(next(actions))
        result=self.task("batch",model,lambda _,r,a:check_evidence([{"path":"a.c","start":1,"end":2}],r))
        self.assertEqual(result["status"],"task_completed",result)
        self.assertEqual(result["calls"],2)

    def test_batch_respects_child_tool_permissions(self):
        actions=iter([{"tool":"batch","actions":[{"tool":"read","path":"a.c","start":1,"count":1}]},
                      {"tool":"finish","report":{}}])
        def validator(_,reader,reads):
            self.assertEqual(reader.reads,{})
            return []
        result=self.task("permissions",lambda *_args,**_kw:json.dumps(next(actions)),validator,
                         allowed_tools={"batch","finish","search"})
        self.assertEqual(result["status"],"task_completed")
        self.assertFalse((self.base/"permissions"/"reads.jsonl").exists())

    def test_oversize_batch_does_not_credit_undelivered_reads(self):
        (self.root/"large.c").write_text("x"*15000+"\n"+"y"*15000+"\n")
        result=self.reader.execute({"tool":"batch","actions":[
            {"tool":"read","path":"large.c","start":1,"count":1},
            {"tool":"read","path":"large.c","start":2,"count":1}]})
        self.assertTrue(result["not_delivered"])
        self.assertEqual(self.reader.reads,{})
        self.assertIn("error",self.reader.execute({"tool":"batch","actions":[{"tool":"batch","actions":[]}]}))

    def test_task_budget_withholds_batch_and_rolls_back_evidence(self):
        (self.root/"large.c").write_text("x"*5000+"\n")
        captured=[]
        def factory(root,log):
            reader=Reader(root,log);captured.append(reader);return reader
        result=self.task("budget",lambda *_args,**_kw:json.dumps({"tool":"batch","actions":[
            {"tool":"read","path":"large.c","start":1,"count":1}]}),
            budgets=Budgets(calls=2,seconds=30,context_chars=5000,reserve_chars=2000,
                            reserve_calls=0,reserve_seconds=0),reader_factory=factory)
        self.assertEqual(captured[0].reads,{})
        self.assertTrue(list((self.base/"budget").glob("withheld-feedback-*")))

    def test_resume_restores_batch_delivery_and_checks_original_hash(self):
        action={"tool":"batch","actions":[{"tool":"read","path":"a.c","start":1,"count":2}]}
        first=self.task("first",lambda *_args,**_kw:json.dumps(action),
            budgets=Budgets(calls=1,seconds=30,context_chars=10000,reserve_chars=0,
                            reserve_calls=0,reserve_seconds=0))
        self.assertEqual(first["status"],"budget_exhausted")
        second=self.task("second",lambda *_args,**_kw:json.dumps({"tool":"finish","report":{}}),
            lambda _,r,a:check_evidence([{"path":"a.c","start":1,"end":2}],r),
            resume_from=self.base/"first")
        self.assertEqual(second["status"],"task_completed")
        (self.root/"a.c").write_text("changed\n")
        with self.assertRaisesRegex(ValueError,"evidence changed"):
            self.task("third",lambda *_:None,resume_from=self.base/"first")

    def test_static_support_delivers_conditional_macros_types_and_missing_include(self):
        (self.root/"a.c").write_text('#include "types.h"\nword f(word x){return OUTER(x);}\n')
        (self.root/"types.h").write_text(
            '#include "missing.h"\ntypedef unsigned int word;\n#ifdef UNRELATED_TYPE\ntypedef int unrelated;\n#endif\n'
            '#ifdef MODE\n#define INNER(x) ((x)+1)\n#else\n#define INNER(x) ((x)+2)\n#endif\n'
            '#define OUTER(x) \\n INNER(x)\n')
        node={"id":"f","source":{"path":"a.c","start":2,"end":2},
              "code":"word f(word x){return OUTER(x);}"}
        pack=SourcePreparation(self.root).prepare([node])
        text="\n".join(x["text"] for x in pack["source_fragments"])
        self.assertIn("typedef unsigned int word;",text)
        self.assertNotIn("typedef int unrelated;",text)
        self.assertNotIn("UNRELATED_TYPE",text)
        self.assertIn("((x)+1)",text);self.assertIn("((x)+2)",text)
        self.assertIn("#ifdef MODE",text);self.assertIn(" INNER(x)",text)
        self.assertTrue(any(x.get("header")=="missing.h" for x in pack["unknowns"]))
        for x in pack["source_fragments"]:
            lines,sha=self.reader.lines(x["path"])
            self.assertEqual(x["sha256"],sha)
            self.assertEqual(x["text"],"\n".join(lines[x["start"]-1:x["end"]]))

    def test_task_view_keeps_conditions_and_indexes_other_background(self):
        upstream={"kind":"reviewed_reference_drafts","conditions":{"f":[{"id":"scope","condition":"keep me"}],
            "g":[{"id":"scope","condition":"other"}]},
            "demand_conditions":{"parent":[{"id":"scope","condition":"caller assumption"}]},
            "unknown_calls":[{"caller":"f","reason":"indirect"},{"reason":"global"},{"caller":"g","reason":"elsewhere"}],
            "inventory_gaps":[{"path":"platform.asm","reason":"configuration unknown"}],
            "demand_context":[{"id":"parent","spec":{"suggested_spec":"long unrelated full spec"*300,
                "assumptions":"caller assumption","callee_requirements":[{"callee_id":"f","requirement":"return carry"}]}}],
            "boundary_context":[],"boundary_edges":[]}
        graph={"edges":{"e":{"id":"e","caller":"parent","callee":"f"}}}
        view,cards=local_context(upstream,graph,{"f"})
        self.assertEqual(view["conditions"],{"f":upstream["conditions"]["f"]})
        self.assertEqual(view["demand_conditions"],upstream["demand_conditions"])
        self.assertEqual(len(view["unknown_calls"]),2)
        self.assertEqual(view["inventory_gaps"]["status"],"unresolved_global_scope")
        self.assertEqual(view["demand_context"][0]["assumptions"],"caller assumption")
        self.assertNotIn("suggested_spec",view["demand_context"][0])
        ref=view["demand_context"][0]["full_context"]
        self.assertEqual(cards[ref],upstream["demand_context"][0])
        self.assertLess(len(json.dumps(view)),len(json.dumps(upstream)))

    def test_stage3_preparation_is_delivered_before_first_model_call(self):
        node={"id":"f","source":{"path":"a.c","start":1,"end":1},"code":"int a;"}
        spec={"assumptions":"scope","suggested_spec":"exact result"}
        artifacts,actions=prepare("extract",{"edges":{}},{"f":node},
            {"conditions":{"f":[{"id":"a","condition":"scope"}]}},{"spec":spec},
            source_preparation=SourcePreparation(self.root))
        def model(messages,timeout):
            self.assertTrue(any('"id": "spec"' in m["content"] for m in messages))
            self.assertTrue(any('"text": "int a;"' in m["content"] for m in messages))
            return json.dumps({"tool":"finish","report":{}})
        result=self.task("prepared",model,lambda _,r,reads:
            check_evidence([node["source"]],r) or ([] if "spec" in reads else ["spec missing"]),
            artifacts=artifacts,required_inputs=actions)
        self.assertEqual(result["status"],"task_completed",result)
        self.assertEqual(result["calls"],1)

    def test_reference_writer_and_reviewer_have_separate_supplement_reads(self):
        from stage3.read_materials import ReadingModel
        for role in ("writer","reviewer"):
            folder=self.base/role;folder.mkdir()
            calls=[]
            def model(messages,timeout):
                calls.append(1)
                if len(calls)==1:
                    self.assertEqual(len(messages),2)
                    return json.dumps({"tool":"batch","actions":[
                        {"tool":"read","path":"a.c","start":1,"count":2}]})
                self.assertIn("int a;",messages[-1]["content"])
                return json.dumps({"tool":"finish","report":{}})
            wrapper=ReadingModel(model,self.root,folder,20000)
            result=wrapper([{"role":"system","content":"test"},{"role":"user","content":"assigned"}],timeout=10)
            self.assertEqual(json.loads(result)["tool"],"finish")
            self.assertEqual(len(calls),2)
            self.assertTrue((folder/"reads.jsonl").exists())

    def test_reference_optional_material_budget_does_not_deliver_or_credit(self):
        from stage3.read_materials import ReadingModel
        from stage1.codex_backend import BackendError
        (self.root/"big.c").write_text("x"*7000+"\n")
        folder=self.base/"optional-budget";folder.mkdir()
        wrapper=ReadingModel(lambda *_args,**_kw:json.dumps(
            {"tool":"read","path":"big.c","start":1,"count":1}),self.root,folder,10000)
        with self.assertRaisesRegex(BackendError,"read budget"):
            wrapper([{"role":"system","content":"test"},{"role":"user","content":"assigned"}],timeout=10)
        self.assertEqual(wrapper.reader.reads,{})
        self.assertTrue((folder/"withheld-1.json").exists())

    def test_stage3_large_mandatory_spec_stops_before_model(self):
        node={"id":"f","source":{"path":"a.c","start":1,"end":1},"code":"int a;"}
        artifacts,actions=prepare("extract",{"edges":{}},{"f":node},{},
                                  {"spec":{"suggested_spec":"x"*20000}})
        result=self.task("mandatory-budget",lambda *_args,**_kw:self.fail("model must not start"),
            artifacts=artifacts,required_inputs=actions,
            budgets=Budgets(calls=8,seconds=30,context_chars=10000,
                            reserve_seconds=0,reserve_chars=1000))
        self.assertEqual(result["status"],"needs_material")
        self.assertEqual(result["calls"],0)

    def test_default_stage2_entry_delivers_support_to_writer_and_independent_review(self):
        from tests.test_reference_specs import ReferenceTests
        from tests.test_reference_review import review_row
        from stage3.reference import run
        helper=ReferenceTests();self.addCleanup(helper.doCleanups)
        root,out,manifest=helper.setup_input("#define STEP(x) ((x)+1)\nint f(int x){return STEP(x);}")
        seen=[]
        writer=helper.factory([])
        def factory(ident):
            def model(messages,timeout):
                assignment=json.loads(messages[1]["content"])
                text="".join(x["text"] for f in assignment["prepared_sources"]["source_files"] for x in f["fragments"])
                self.assertIn("#define STEP(x)",text)
                seen.append(ident)
                if "review" in ident:
                    return json.dumps({"tool":"finish","report":{"functions":[review_row(n["id"])
                        for n in assignment["assigned"]]}})
                return writer(ident)(messages,timeout)
            return model
        result=run(root,out,manifest,{},factory,graph_backend="lexical")
        self.assertTrue(all(n["status"]=="reference_draft" for n in result["nodes"].values()))
        self.assertTrue(any("review" in ident for ident in seen))

    def test_compact_preparation_round_trip_keeps_all_source_and_include_sites(self):
        from stage3.read_materials import compact_preparation
        pack={"policy":1,"coverage":"unknown","source_fragments":[
            {"path":"h.h","sha256":"hash","start":1,"end":2,"text":"one"},
            {"path":"h.h","sha256":"hash","start":5,"end":5,"text":"two"}],
            "unknowns":[{"header":"missing.h","including":"a.c","reason":"missing"},
                        {"header":"missing.h","including":"b.c","reason":"missing"},
                        {"reason":"nonliteral include","including":"a.c"}]}
        compact=compact_preparation(pack)
        restored=[{"path":f["path"],"sha256":f["sha256"],**x}
                  for f in compact["source_files"] for x in f["fragments"]]
        self.assertEqual(restored,pack["source_fragments"])
        self.assertEqual(compact["unresolved_includes"]["items"],
                         [{"header":"missing.h","including":["a.c","b.c"]}])
        self.assertEqual(compact["other_unknowns"],[pack["unknowns"][-1]])
