import argparse
import logging

import barrier
from barrier.lzz.serialization import importLzz, importInvar
from pysmt.shortcuts import get_env, Solver, Not
from pysmt.logics import QF_NRA

from barrier.compute_barrier import synth_barrier



parser = argparse.ArgumentParser()
parser.add_argument("problem",help="File containing the invariant verification")

parser.add_argument("--solver",
                    choices=["z3","mathsat","mathematica"],
                    default="z3",
                    help="SMT solver to use")

args = parser.parse_args()
logging.basicConfig(level=logging.DEBUG)

print("Parsing problem...")
env = get_env()

with open(args.problem, "r") as json_stream:
  problem_list = importInvar(json_stream, env)
  assert(len(problem_list) == 1)
  for p in problem_list:
      (problem_name, init, safe, dyn_sys, invariants, predicates) = p


degree = 2
max_degree = 10
solved = False
while ( (not solved) and degree < max_degree):
  print("Finding barrier with %d degree..." % degree)
  (res, barrier) = synth_barrier(dyn_sys, init, Not(safe), degree)
  solved = res
  degree += 1

if (solved):
  print("Found barrier: ",barrier.serialize())
else:
  print("Barrier not found")
