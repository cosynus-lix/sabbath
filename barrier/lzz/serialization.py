""" Import LZZ problem

Example of json file:
{
  "varsDecl": ["(declare-fun _x () Real)", "(declare-fun _y () Real)"],
  "contVars": ["(declare-fun _x () Real)", "(declare-fun _y () Real)"],
  "candidate": "(<= (+ (* _x (* _x (* _x (* _x 1)))) (* 2 (* _y (* _y 1)))) 10)",
  "constraints": "(and true (<= (+ (* _x (* _x (* _x (* _x 1)))) (* 2 (* _y (* _y 1)))) 10))",
  "name": "MIT astronautics Lyapunov",
  "vectorField": ["(= (- _y (* (* _x (* _x (* _x (* _x (* _x (* _x (* _x 1))))))) (- (+ (* _x (* _x (* _x (* _x 1)))) (* 2 (* _y (* _y 1)))) 10))) 0)", "(= (- (- (* _x (* _x (* _x 1)))) (* (* 3 (* _y (* _y (* _y (* _y (* _y 1)))))) (- (+ (* _x (* _x (* _x (* _x 1)))) (* 2 (* _y (* _y 1)))) 10))) 0)"]
}

"""

import json
from io import StringIO

from pysmt.smtlib.parser import SmtLibParser
import pysmt.smtlib.commands as smtcmd

from barrier.system import DynSystem

def fromString(parser, string):
    output = StringIO()
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

def importLzz(json_stream, env):
    problem_json = json.load(json_stream)
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

    # Invariant candidate
    candidate = fromStringFormula(parser, vars_decl_str, problem_json["candidate"])
    # Invariant of the dynamical system
    invar = fromStringFormula(parser, vars_decl_str, problem_json["constraints"])

    # Systems of ODEs
    odes = {}
    for var, ode_str in zip(cont_vars, problem_json["vectorField"]):
        ode_eq_0 = fromStringFormula(parser, vars_decl_str, ode_str)
        ode = ode_eq_0.args()[0]
        odes[var] = ode

    dyn_sys = DynSystem(cont_vars, [], [], odes, {}, False)

    return (problem_json["name"], candidate, dyn_sys, invar)
