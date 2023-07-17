""" Convert based on the degree of polynomials

"""

import sys
import argparse
import logging
import os
import signal
import sys

from pysmt.exceptions import SolverAPINotFound
from pysmt.logics import QF_NRA
from pysmt.shortcuts import (
    get_env, Solver
)

from sabbath.lzz.serialization import importInvar, serializeInvar
from sabbath.lzz.lzz import LzzOpt
from sabbath.decomposition.explicit import (
    Result,
    dwcl,
    get_invar_lazy
)
from sabbath.decomposition.encoding import (
    DecompositionOptions,
    DecompositionEncoder
)
from sabbath.ts import TS
from sabbath.utils import get_mathsat_smtlib
from sabbath.mathematica.mathematica import (
    get_mathematica, exit_callback_print_time, OutOfTimeSolverError, MathematicaSession
)

from sabbath.decomposition.utils import sort_poly_by_degree

def get_degrees(derivator, predicates):
    dset = set()
    for p in predicates:
        dset.add(derivator.get_poly_degree(p))
    return dset

def bound_degree(derivator, predicates, degree_bound):
    res = []
    for p in predicates:
        if derivator.get_poly_degree(p) <= degree_bound:
            res.append(p)
    return res

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("problem",help="Verification problem file")

    args = parser.parse_args()

    logging.basicConfig(level=logging.DEBUG)


    def signal_handler(sig, frame):
        # Kill any instance of mathematica, if any.
        print('You pressed Ctrl+C!')
        sys.stdout.flush()
        sys.stderr.flush()
        os._exit(1)
    signal.signal(signal.SIGINT, signal_handler)

    print("Parsing problem...")
    env = get_env()
    with open(args.problem, "r") as json_stream:
        problem_list = importInvar(json_stream, env)
    assert(len(problem_list) == 1)
    (problem_name, init, safe, dyn_sys, invariants, predicates) = problem_list[0]
    print("parsed problem...")

    # print(dyn_sys)
    # print(invariants.serialize())
    # print(init.serialize())
    # print(safe.serialize())
    # print(predicates)

    derivator = dyn_sys.get_derivator()
    sort_poly_by_degree(derivator, predicates)
    #print(predicates)

    deg_set = get_degrees(derivator, predicates)

    for d in deg_set:
        print("degree Bound " + str(d))
        bounded_pred = bound_degree(derivator, predicates, d)
        bounded_prob = (problem_name, init, safe, dyn_sys, invariants, bounded_pred)
        with open(os.path.splitext(args.problem)[0] + "_degbound_" + str(d) + ".invar", "w") as output:
            serializeInvar(output, [bounded_prob], env)

if __name__ == '__main__':
    main()
    sys.exit(os.EX_OK)
