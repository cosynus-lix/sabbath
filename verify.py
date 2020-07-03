""" Verify the safety of a dynamical system.

"""

import sys
import argparse
import logging

from functools import partial

from pysmt.logics import QF_NRA
from pysmt.shortcuts import (
    get_env, Solver
)

from barrier.lzz.serialization import importInvar
from barrier.decomposition.explicit import (
    Result,
    dwcl,
    get_invar_lazy
)
from barrier.decomposition.encoding import DecompositionEncoder
from barrier.ts import TS
from barrier.utils import get_mathsat_smtlib
from barrier.mathematica.mathematica import get_mathematica

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("problem",help="Verification problem file")

    parser.add_argument("--task",
                        choices=["dwcl","reach","dump_vmt"],
                        default="dwcl",
                        help="Verify using dwcl or dump vmt file")

    parser.add_argument("--solver",
                        choices=["z3","mathsat","mathematica"],
                        default="z3",
                        help="SMT solver to use")

    parser.add_argument("--outvmt", help="Output vmt file")
    parser.add_argument("--outpred", help="Output predicates file")

    args = parser.parse_args()

    logging.basicConfig(level=logging.DEBUG)

    print("Parsing problem...")
    env = get_env()
    with open(args.problem, "r") as json_stream:
        problem_list = importInvar(json_stream, env)
    assert(len(problem_list) == 1)
    (problem_name, init, safe, dyn_sys, invariants, predicates) = problem_list[0]
    print("parsed problem...")


    if (args.task != "dump_vmt"):

        solvers = {"z3" : partial(Solver, logic=QF_NRA, name="z3"),
                   "mathematica" : partial(get_mathematica, env=get_env()),
                   "mathsat" : partial(get_mathsat_smtlib, env=get_env())}

        get_solver = solvers[args.solver]

        if (args.task == "dwcl"):
            print("Verifying using dwcl...")
            (res, invars) = dwcl(dyn_sys, invariants, predicates, init, safe,
                                 get_solver, get_solver)

        elif (args.task == "reach"):
            print("Verifying using reachability analysis...")
            (res, invars) = get_invar_lazy(dyn_sys,
                                          invariants,
                                          predicates,
                                          init, safe, get_solver)

        print("%s %s: %s" % (problem_name, str(res), str(invars)))

    else:
        assert(args.task == "dump_vmt")
        if (not args.outvmt):
            print("Missing output name for vmt file")
            sys.exit(1)
        if (not args.outpred):
            print("Missing output name for predicates  file")
            sys.exit(1)


        print("Encoding verification problem in the vmt file to %s..." % args.outvmt)
        encoder  = DecompositionEncoder(env,
                                        dyn_sys,
                                        invariants,
                                        predicates,
                                        init,
                                        safe)

        (ts, p, predicates) = encoder.get_ts_ia()
        with open(args.outvmt, "w") as outstream:
            ts.to_vmt(outstream, p)
            print("Printed vmt to %s..." % args.outvmt)

        with open(args.outpred, "w") as outstream:
            TS.dump_predicates(outstream, predicates)
            print("Printed predicates to %s..." % args.outpred)

if __name__ == '__main__':
    main()
