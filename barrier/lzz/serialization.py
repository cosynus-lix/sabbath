""" Import LZZ and invariant problem

Example of json file already containing an invariant to check:
{
  "varsDecl": ["(declare-fun _x () Real)", "(declare-fun _y () Real)"],
  "contVars": ["(declare-fun _x () Real)", "(declare-fun _y () Real)"],
  "candidate": "(<= (+ (* _x (* _x (* _x (* _x 1)))) (* 2 (* _y (* _y 1)))) 10)",
  "constraints": "(and true (<= (+ (* _x (* _x (* _x (* _x 1)))) (* 2 (* _y (* _y 1)))) 10))",
  "name": "MIT astronautics Lyapunov",
  "vectorField": ["(= (- _y (* (* _x (* _x (* _x (* _x (* _x (* _x (* _x 1))))))) (- (+ (* _x (* _x (* _x (* _x 1)))) (* 2 (* _y (* _y 1)))) 10))) 0)", "(= (- (- (* _x (* _x (* _x 1)))) (* (* 3 (* _y (* _y (* _y (* _y (* _y 1)))))) (- (+ (* _x (* _x (* _x (* _x 1)))) (* 2 (* _y (* _y 1)))) 10))) 0)"]
}

Example of json file containing an invariant verification problem
[{
  "antecedent": "(and (<= (* _x (* _x 1)) (/ 1 2)) (<= (* _y (* _y 1)) (/ 1 3)))",
  "consequent": "(> (+ (* (+ (- 2) _x) (* (+ (- 2) _x) 1)) (* (+ (- 3) _y) (* (+ (- 3) _y) 1))) (/ 1 4))",
  "constraints": "true",
  "contVars": ["(declare-fun _y () Real)", "(declare-fun _x () Real)"],
  "name": "MIT astronautics Lyapunov",
  "predicates": [],
  "varsDecl": ["(declare-fun _x () Real)", "(declare-fun _y () Real)"],
  "vectorField": ["(= (- (- (* _x (* _x (* _x 1)))) (* (* 3 (* _y (* _y (* _y (* _y (* _y 1)))))) (- (+ (* _x (* _x (* _x (* _x 1)))) (* 2 (* _y (* _y 1)))) 10))) 0)", "(= (- _y (* (* _x (* _x (* _x (* _x (* _x (* _x (* _x 1))))))) (- (+ (* _x (* _x (* _x (* _x 1)))) (* 2 (* _y (* _y 1)))) 10))) 0)"]
}]


"""

import json
from io import StringIO

from pysmt.smtlib.parser import SmtLibParser
import pysmt.smtlib.commands as smtcmd
from pysmt.shortcuts import Real

from barrier.system import DynSystem

def fromString(parser, string):
    output = StringIO()

    # Does not support ^ symbol
    # for pow now.
    assert(string.find("^") < 0)

    output.write(string)
    output.seek(0)
    script = parser.get_script(output)
    return script

def fromStringFormula(parser, vars_decl_str, string):
    smt_script = "(set-logic QF_NRA)\n" +  vars_decl_str + "\n" + ("(assert %s)" % string)
    script = fromString(parser, smt_script)
    return script.get_last_formula()

def readVar(parser, var_decl, all_vars):
    s = fromString(parser, var_decl)
    assert(len(s.commands) == 1)

    for cmd in s.commands:
        if cmd.name == smtcmd.DECLARE_FUN:
            all_vars.append(cmd.args[0])
        elif cmd.name == smtcmd.DEFINE_FUN:
            (var, formals, typename, body) = cmd.args

def parse_dyn_sys(env, problem_json, is_lzz = False):
    parser = SmtLibParser(env)

    # Read all the variables
    all_vars = []
    vars_decl_str = None
    for var_decl in problem_json["varsDecl"]:
        readVar(parser, var_decl, all_vars)
        vars_decl_str = var_decl if vars_decl_str is None else "%s\n%s" % (vars_decl_str, var_decl)

    # Read the continuous variables
    cont_vars = []
    for var_decl in problem_json["contVars"]:
        readVar(parser, var_decl, cont_vars)

    if (not is_lzz):
        # Antecedent
        antecedent = fromStringFormula(parser, vars_decl_str, problem_json["antecedent"])
        # Consequent
        consequent = fromStringFormula(parser, vars_decl_str, problem_json["consequent"])

        predicates = []
        for pred_json in problem_json["predicates"]:
            pred_eq_0 = fromStringFormula(parser, vars_decl_str, pred_json)
            pred = pred_eq_0.args()[0]
            predicates.append(pred)
    else:
        # Invariant candidate
        candidate = fromStringFormula(parser, vars_decl_str, problem_json["candidate"])

    # Invariant of the dynamical system
    invar = fromStringFormula(parser, vars_decl_str, problem_json["constraints"])

    # Discrete variables (e.g., parameters) that are not in the
    # continuous variables become (discrete) inputs.
    input_vars = []
    for var in all_vars:
        if not var in cont_vars:
            input_vars.append(var)

    # Systems of ODEs
    odes = {}
    for var, ode_str in zip(cont_vars, problem_json["vectorField"]):
        ode_eq_0 = fromStringFormula(parser, vars_decl_str, ode_str)
        ode = ode_eq_0.args()[0]
        odes[var] = ode

    dyn_sys = DynSystem(cont_vars, input_vars, [], odes, {}, False)

    if (not is_lzz):
        return (dyn_sys, invar, antecedent, consequent, predicates)
    else:
        return (dyn_sys, invar, candidate)

def importLzz(json_stream, env):
    problem_json = json.load(json_stream)
    (dyn_sys, invar, candidate) = parse_dyn_sys(env, problem_json, True)
    return (problem_json["name"], candidate, dyn_sys, invar)

def importInvar(json_stream, env):
    problem_json_list = json.load(json_stream)

    results = []
    for problem_json in problem_json_list:
        res = parse_dyn_sys(env, problem_json)
        (dyn_sys, invar, antecedent, consequent, predicates) = res

        results.append((problem_json["name"], antecedent, consequent,
                        dyn_sys, invar, predicates))

    return results
