def scenario(assignment):
    return {"situation":"Fixture scalar computation and its supplied callers",
            "selected_domains":[],"selection_reason":"General requirements suffice for this fixture",
            "focus":[{"topic":"general."+r["id"],"basis":"Supplied fixture source and call graph",
                      "application":"Preserve the fixture contract and record missing evidence",
                      "status":"applicable"} for r in assignment["writing_guidance"]["general_requirements"]],
            "unknowns":[]}
