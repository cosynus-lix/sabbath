"""

{
  "name" : "thermo",
  "contVars": ["(declare-fun x () Real)"],
  "varsDecl": ["(declare-fun x () Real)"],
  "init" : {
    "1" : "(= x 0)"
  },
  "locations" : {
    "1" : {
      "invar" : "(<= x 10)",
      "vectorField": ["(= x 0)"]
    },
    "2" : {
      "invar" : "(>= x 0)",
      "vectorField": ["(= (- x) 0)"]
    }
  },
  "edges" : {
    "1" : [{"dst" : "2", "trans" : "(& (= x 10) (= x_next 10))"}],
    "2" : [{"dst" : "1", "trans" : "(& (= x 0) (= x_next 0))"}]
  },
  "property" : "(& (>= x 0) (<= x 10))",
  "property_by_loc" : {
    "1" : "true"
  }
}
"""

import json
from io import StringIO

from pysmt.smtlib.parser import SmtLibParser
import pysmt.smtlib.commands as smtcmd
from pysmt.shortcuts import Real, Equals

import pysmt.smtlib.commands as smtcmd
from pysmt.smtlib.printers import SmtDagPrinter
from pysmt.smtlib.script import SmtLibScript, SmtLibCommand

from barrier.system import (
    DynSystem, HybridAutomaton,
    HaProp,
    HaVerProblem,
)
from barrier.serialization.invar_serialization import (
    readVar, fromStringFormula,
    get_smt_formula, get_smt_formula_pred, get_smt_vars
)
from barrier.ts import TS

def add_next_vars(env, all_vars, vars_decl_str):
    f_next = TS.get_next_f(all_vars, env)
    next_vars = [f_next(l) for l in all_vars]

    for n in next_vars:
        var_decl = "(declare-fun %s () %s)" % (n.serialize(), n.symbol_type())
        vars_decl_str = var_decl if vars_decl_str is None else "%s\n%s" % (vars_decl_str, var_decl)
    return vars_decl_str


def parse_hs(env, problem_json):
    parser = SmtLibParser(env)

    name = problem_json["name"]

    # Read all the variables
    all_vars = []
    vars_decl_str = None
    for var_decl in problem_json["varsDecl"]:
        readVar(parser, var_decl, all_vars)
        vars_decl_str = var_decl if vars_decl_str is None else "%s\n%s" % (vars_decl_str, var_decl)
    vars_decl_str = add_next_vars(env, all_vars, vars_decl_str)

    # Read the continuous variables
    cont_vars = []
    for var_decl in problem_json["contVars"]:
        readVar(parser, var_decl, cont_vars)

    # Discrete variables (e.g., parameters) that are not in the
    # continuous variables become (discrete) inputs.
    input_vars = []
    for var in all_vars:
        if not var in cont_vars:
            input_vars.append(var)

    # Read init
    init = {}
    for loc, init_formula in problem_json["init"].items():
        init[loc] = fromStringFormula(parser, vars_decl_str, init_formula)

    # read locations
    locations = {}
    for loc, loc_data in problem_json["locations"].items():
        loc_invar = fromStringFormula(parser, vars_decl_str, loc_data["invar"])
        odes = {}
        for var, ode_str in zip(cont_vars, loc_data["vectorField"]):
            ode_eq_0 = fromStringFormula(parser, vars_decl_str, ode_str)
            ode = ode_eq_0.args()[0]
            odes[var] = ode
        dyn_sys = DynSystem(cont_vars, input_vars, [], odes, {}, False)
        location = HybridAutomaton.Location(invar=loc_invar, vector_field=dyn_sys)
        locations[loc] = location

    # read edges
    edges = {}
    for loc, edge_data in problem_json["edges"].items():
        loc_edges = []
        for edge in edge_data:
            dst = edge["dst"]
            trans = fromStringFormula(parser, vars_decl_str, edge["trans"])
            ha_edge = HybridAutomaton.Edge(dst=dst, trans=trans)
            loc_edges.append(ha_edge)
        edges[loc] = loc_edges

    # read predicates
    predicates = []
    if "predicates" in problem_json:
        for pred_json in problem_json["predicates"]:
            pred_eq_0 = fromStringFormula(parser, vars_decl_str, pred_json)
            pred = pred_eq_0.args()[0]
            predicates.append(pred)

    # read property
    prop = fromStringFormula(parser, vars_decl_str, problem_json["property"])

    prop_by_loc = {}
    if "property_by_loc" in problem_json:
        for loc, prop_json in problem_json["property_by_loc"].items():
            prop_loc = fromStringFormula(parser, vars_decl_str, prop_json)
            prop_by_loc[loc] = prop_loc

    ha = HybridAutomaton(input_vars, cont_vars, init, locations, edges)
    ha_prop = HaProp(prop, prop_by_loc)

    problem = HaVerProblem(name, ha, ha_prop, predicates)
    return problem

def serializeHS(outstream, problem, env):
    # problem = HaVerProblem(name, ha, ha_prop, predicates)

    name = problem.name
    ha = problem.ha
    predicates = problem.predicates
    ha_prop = problem.prop

    cont_vars_smt = [get_smt_vars(v, env) for v in ha._cont_vars]
    disc_vars_smt = [get_smt_vars(v, env) for v in ha._disc_vars]

    def build_init(init_list):
        init_map = {}
        for (loc,f) in init_list:
            init_map[loc] = get_smt_formula(f, env)
        return  init_map


    def build_locations(loc_list):
        loc_map = {}
        for (loc, location) in loc_list:
            loc_map[loc] = {
                "invar" : get_smt_formula(location.invar, env),
                "vectorField" : [get_smt_formula_pred(location.vector_field.get_ode(v), env) for v in ha._cont_vars]
            }
        return loc_map

    def build_edges(edge_list):
        edge_map = {}
        for (loc, edge_list) in edge_list:
            dst_edge_list = []
            for edge in edge_list:
                dst_edge_list.append({"dst" : edge.dst,
                                      "trans" : get_smt_formula(edge.trans, env)})
            edge_map[loc] = dst_edge_list
        return edge_map

    def build_prop_loc(prop_by_loc, env):
        prop_by_loc_text = {}
        for (loc, loc_prop) in prop_by_loc.items():
            prop_by_loc_text[loc] = get_smt_formula(loc_prop, env)
        return prop_by_loc_text


    ha_json = {
        "name" : name,
        "contVars" : cont_vars_smt,
        "varsDecl" : cont_vars_smt + disc_vars_smt,
        "init" : build_init(ha._init.items()),
        "locations" : build_locations(ha._locations.items()),
        "edges" : build_edges(ha._edges.items()),
        "predicates" : [get_smt_formula_pred(p, env) for p in predicates],
        "property" : get_smt_formula(ha_prop.global_prop, env),
        "property_by_loc" : build_prop_loc(ha_prop.prop_by_loc, env)
    }
    json.dump(ha_json, outstream)

def importHSVer(json_stream, env):
    problem_json = json.load(json_stream)
    problem = parse_hs(env, problem_json)

    return problem
