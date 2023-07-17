import argparse
import logging

import barrier
from sabbath.lzz.serialization import importLzz, importInvar
from pysmt.shortcuts import get_env, Solver
from pysmt.logics import QF_NRA
from sabbath.lzz.lzz import lzz, LzzOpt
from sabbath.mathematica.mathematica import get_mathematica, MathematicaSession



parser = argparse.ArgumentParser()
parser.add_argument("problem",help="File containing the invariant check problem")

parser.add_argument("--solver",
                    choices=["z3","mathsat","mathematica"],
                    default="z3",
                    help="SMT solver to use")

args = parser.parse_args()
logging.basicConfig(level=logging.DEBUG)

print("Parsing problem...")
env = get_env()
with open(args.problem, "r") as json_stream:
  lzz_problem = importLzz(json_stream, env)
  (name, candidate, dyn_sys, invar) = lzz_problem

solver = Solver(logic=QF_NRA, name="z3")
opt = LzzOpt(True,True)

is_invar = lzz(opt, solver, candidate, dyn_sys.get_derivator(), candidate, invar)
print(is_invar)



