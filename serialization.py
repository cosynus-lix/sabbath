"""
Read/write results in libsmt.
"""

import json

from pysmt.smtlib.parser import SmtLibParser

from barrier.lzz.serialization import (
    _get_smt_vars,
    _get_smt_formula,
    _get_smt_formula_pred,
    fromStringFormula, readVar,
    parse_dyn_sys
)


def importSynthesis(problem_json, env):
    """

    """

    parser = SmtLibParser(env)

    dyn_systems = [None,None]
    dyn_systems[0],_,_ = parse_dyn_sys(env, problem_json["sys_m0"], True, True)
    dyn_systems[1],_,_ = parse_dyn_sys(env, problem_json["sys_m1"], True, True)

    all_vars = []
    vars_decl_str = None
    for l in [problem_json["sys_m0"]["varsDecl"],problem_json["sys_m1"]["varsDecl"]]:
        for var_decl in l:
            app = []
            readVar(parser, var_decl, app)
            if not app[0] in all_vars:
                all_vars += app
                vars_decl_str = var_decl if vars_decl_str is None else "%s\n%s" % (vars_decl_str, var_decl)

    theta = fromStringFormula(parser, vars_decl_str, problem_json["theta"]).args()[0]
    reference_values = []
    for json_r in problem_json["reference_values"]:
        r = fromStringFormula(parser, vars_decl_str, json_r).args()[0]
        reference_values.append(r)

    if "lyapunov_m0" in problem_json:
        lyapunov_m0 = fromStringFormula(parser, vars_decl_str, problem_json["lyapunov_m0"]).args()[0]
    else:
        lyapunov_m0 = None

    if "lyapunov_m1" in problem_json:
        lyapunov_m1 = fromStringFormula(parser, vars_decl_str, problem_json["lyapunov_m1"]).args()[0]
    else:
        lyapunov_m1 = None

    if "assumption" in problem_json:
        assumption =  fromStringFormula(parser, vars_decl_str, problem_json["assumption"])
    else:
        assumption = None

    return (dyn_systems,
            theta,
            reference_values,
            lyapunov_m0,
            lyapunov_m1,
            assumption)


def serializeSynthesis(outstream,
                       dyn_systems,
                       theta,
                       reference_values,
                       lyapunov_m0,
                       lyapunov_m1,
                       assumption,
                       env):
    """
    Writes invar_problem problem on outstream
    """
    cont_vars_0_smt = [_get_smt_vars(v, env) for v in dyn_systems[0].states()]
    cont_vars_1_smt = [_get_smt_vars(v, env) for v in dyn_systems[1].states()]
    json_data = {
        "sys_m0" : {
            "contVars" : cont_vars_0_smt,
            "varsDecl" : cont_vars_0_smt + [_get_smt_vars(v, env) for v in dyn_systems[0].inputs()],
            "vectorField": [_get_smt_formula_pred(dyn_systems[0].get_ode(v), env) for v in dyn_systems[0].states()],
        },
        "sys_m1" : {
            "contVars" : cont_vars_1_smt,
            "varsDecl" : cont_vars_1_smt + [_get_smt_vars(v, env) for v in dyn_systems[1].inputs()],
            "vectorField": [_get_smt_formula_pred(dyn_systems[1].get_ode(v), env) for v in dyn_systems[1].states()],
        },
        "theta" : _get_smt_formula_pred(theta, env),
        "reference_values" : [_get_smt_formula_pred(v, env) for v in reference_values]
    }

    if not lyapunov_m0 is None:
        json_data["lyapunov_m0"] = _get_smt_formula_pred(lyapunov_m0, env)

    if not lyapunov_m1 is None:
        json_data["lyapunov_m1"] = _get_smt_formula_pred(lyapunov_m1, env)

    if not assumption is None:
        json_data["assumption"] = _get_smt_formula(assumption, env)

    json.dump(json_data, outstream)
