"""Versioned writing guidance and structural checks, not semantic verification."""
import json
from pathlib import Path
from stage2.graph import digest

DEFAULT_CATALOG = Path(__file__).with_name("DOMAIN_CONCERNS.json")
PROMPT = """
每次书写或修订自然语言规约前，先依据本次实现、调用关系和材料进行简短情景分析，再据此书写。
writing_guidance 是可更新的通用要求和领域目录/关注点，不是正确性基准。由你根据实际情景选择零个或多个领域，
不按库名机械分类，不强套目录的全部关注点；目录未覆盖的情景可用 custom.<名称> 补充，并在 unknowns 说明材料缺口。
每个函数输出中，在 suggested_spec 之前增加 scenario_analysis：
{"situation":"当前职责、输入输出和调用情景的简短概括",
 "selected_domains":["目录中的领域id"],"selection_reason":"为何适用；没有适用领域时说明",
 "focus":[{"topic":"general.inputs 或 integer_array.bounds 或 custom.自定义名",
           "basis":"给定实现、调用点或材料中的具体依据，未提供的材料不得声称已读",
           "application":"该事项如何影响规约，或为什么不适用、需要后续哪种检查",
           "status":"applicable/not_applicable/unknown"}],
 "unknowns":["尚未确定的具体事项，没有则 []"]}
通用要求的每个 general.<id> 都要有一项简短说明；所选领域至少选取一个实际相关关注点，
无关关注点无需逐项抄写。可组合多个领域。情景分析是书写依据，不是独立审核、已验证结论或内部推理记录。
分析后按既定自然规约模板书写，明确参数、单位、入口状态、结果和资源，保留不确定性。
影响契约成立或覆盖范围的 unknowns 也必须写入 assumptions，不能只留在情景分析中而在下游丢失。
不能把领域提示自动变成前置条件或安全性保证。统一数组谓词、析取或命名分支应根据证据选择，
当前环境的表达式翻译、资源自动匹配和实际调用结果留给后续实测，不得在自然规约阶段宣称已通过。
"""


def load_catalog(path=None):
    value=json.loads(Path(path or DEFAULT_CATALOG).read_text(encoding="utf-8-sig"))
    if not isinstance(value,dict) or value.get("version") != 1:
        raise ValueError("unsupported domain catalog version")
    def entries(rows, label, fields):
        if not isinstance(rows,list) or not rows:
            raise ValueError(label+" must be a nonempty list")
        seen=set()
        for row in rows:
            if not isinstance(row,dict) or any(not isinstance(row.get(k),str) or not row[k].strip() for k in fields):
                raise ValueError("invalid "+label+" entry")
            ident=row["id"]
            if ident in seen or "." in ident or not ident.replace("_","").replace("-","").isalnum():
                raise ValueError("duplicate/invalid "+label+" id")
            seen.add(ident)
    entries(value.get("general_requirements"),"general requirements",("id","title","guidance"))
    entries(value.get("domains"),"domains",("id","title","when_relevant"))
    for domain in value["domains"]:
        if domain["id"] in ("general","custom"):
            raise ValueError("reserved domain id")
        entries(domain.get("points"),"domain points",("id","guidance"))
    return value


def policy(catalog):
    return {"version":1,"catalog_digest":digest(catalog),"prompt_digest":digest(PROMPT)}


def validate_scenarios(records,catalog):
    general={"general."+r["id"] for r in catalog["general_requirements"]}
    domains={d["id"]:{d["id"]+"."+p["id"] for p in d["points"]} for d in catalog["domains"]}
    for row in records:
        analysis=row.get("scenario_analysis")
        if not isinstance(analysis,dict) or any(not isinstance(analysis.get(k),str) or not analysis[k].strip()
                                                for k in ("situation","selection_reason")):
            raise ValueError("scenario_analysis needs situation and selection_reason before specification writing")
        chosen=analysis.get("selected_domains")
        if not isinstance(chosen,list) or any(not isinstance(d,str) or d not in domains for d in chosen) or len(chosen)!=len(set(chosen)):
            raise ValueError("scenario selected_domains must be unique catalog IDs")
        focus=analysis.get("focus")
        if not isinstance(focus,list):raise ValueError("scenario focus must be a list")
        topics=set();allowed=general|set().union(*(domains[d] for d in chosen))
        for item in focus:
            if (not isinstance(item,dict) or any(not isinstance(item.get(k),str) or not item[k].strip()
                for k in ("topic","basis","application")) or item.get("status") not in ("applicable","not_applicable","unknown")):
                raise ValueError("scenario focus needs topic, basis, application and applicability status")
            topic=item["topic"]
            if topic in topics or (topic not in allowed and not (topic.startswith("custom.") and topic[7:].strip())):
                raise ValueError("duplicate or unknown scenario topic")
            topics.add(topic)
        if not general <= topics or any(not domains[d]&topics for d in chosen):
            raise ValueError("scenario must address general requirements and selected domains")
        unknowns=analysis.get("unknowns")
        if not isinstance(unknowns,list) or any(not isinstance(x,str) or not x.strip() for x in unknowns):
            raise ValueError("scenario unknowns must be a list of nonempty text")
    return records
