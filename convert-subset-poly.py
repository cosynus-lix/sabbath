""" Convert based on the increasing subset of the original polynomials

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

def max_degree(derivator, predicates):
    res = 0
    for p in predicates:
        res = max(res, derivator.get_poly_degree(p))
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
    print(predicates)

    psize = len(predicates)
    for i in range(psize):
        print("number of polynomials " + str(i))
        bounded_pred = predicates[:i+1]
        print(bounded_pred)
        bounded_prob = (problem_name, init, safe, dyn_sys, invariants, bounded_pred)
        with open(os.path.splitext(args.problem)[0] + "_poly_" + str(i+1) + "_maxdegree_" + str(max_degree(derivator, bounded_pred)) + ".invar", "w") as output:
            serializeInvar(output, [bounded_prob], env)

if __name__ == '__main__':
    main()
    sys.exit(os.EX_OK)
