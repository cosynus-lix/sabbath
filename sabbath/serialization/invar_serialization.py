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
from pysmt.shortcuts import Real, Equals

import pysmt.smtlib.commands as smtcmd
from pysmt.smtlib.printers import SmtDagPrinter
from pysmt.smtlib.script import SmtLibScript, SmtLibCommand

from sabbath.system import DynSystem

def fromString(parser, string):
    output = StringIO()

    # Does not support ^ symbol
    # for pow now.
    assert(string.find("^") < 0)

    output.write(string)
    output.seek(0)

    try:
        script = parser.get_script(output)
    except Exception as e:
        output.seek(0)
        print("Error parsing the SMT expression %s" % output.getvalue())

        raise e
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

def parse_dyn_sys(env, problem_json, is_check_problem = False, only_ode = False):
    """
    is_check_problem: true if the problem is to check if a differential invariant holds (so, need to read candidate and not antecendent and consequent)
    only_ode: parse a dynamical system and not a hybrid system
    """

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

    if (not is_check_problem):
        if not (only_ode):
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
        if not (only_ode):
            # Invariant candidate
            candidate = fromStringFormula(parser, vars_decl_str, problem_json["candidate"])
        else:
            candidate = None

    # Invariant of the dynamical system
    if (not only_ode):
        invar = fromStringFormula(parser, vars_decl_str, problem_json["constraints"])
    else:
        invar = None

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

    if (not is_check_problem):
        return (dyn_sys, invar, antecedent, consequent, predicates)
    else:
        return (dyn_sys, invar, candidate)

def importInvarCheck(json_stream, env):
    problem_json = json.load(json_stream)
    (dyn_sys, invar, candidate) = parse_dyn_sys(env, problem_json, True)
    return (problem_json["name"], candidate, dyn_sys, invar)

def importInvarVer(json_stream, env):
    problem_json_list = json.load(json_stream)

    results = []
    for problem_json in problem_json_list:
        res = parse_dyn_sys(env, problem_json)
        (dyn_sys, invar, antecedent, consequent, predicates) = res

        results.append((problem_json["name"], antecedent, consequent,
                        dyn_sys, invar, predicates))

    return results


def get_smt_vars(var, env):
    var_cmd = SmtLibCommand(name=smtcmd.DECLARE_FUN, args=[var])
    outstream = StringIO()
    var_cmd.serialize(outstream=outstream)
    return outstream.getvalue()

def get_smt_formula(formula, printer):
    outstream = StringIO()
    printer = SmtDagPrinter(outstream)
    printer.printer(formula)
    return outstream.getvalue()

def get_smt_formula_pred(formula, printer):
    return get_smt_formula(Equals(formula, Real(0)), printer)

def serializeInvar(outstream, invar_problems, env):
    """
    Writes invar_problem problem on outstream
    """
    invar_problems_json = []
    for invar_problem in invar_problems:
        name, antecedent, consequent, dyn_sys, invar, predicates = invar_problem
        cont_vars_smt = [get_smt_vars(v, env) for v in dyn_sys.states()]
        json_data = {
            "name" : name,
            "contVars" : cont_vars_smt,
            "varsDecl" : cont_vars_smt + [get_smt_vars(v, env) for v in dyn_sys.inputs()],
            "antecedent": get_smt_formula(antecedent, env),
            "consequent": get_smt_formula(consequent, env),
            "constraints": get_smt_formula(invar, env),
            "predicates" : [get_smt_formula_pred(p, env) for p in predicates],
            "vectorField": [get_smt_formula_pred(dyn_sys.get_ode(v), env) for v in dyn_sys.states()]
        }
        invar_problems_json.append(json_data)

    json.dump(invar_problems_json, outstream)

