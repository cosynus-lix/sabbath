""" Verify the safety of a dynamical system.

"""

import sys
import argparse
import logging

from pysmt.shortcuts import get_env

from barrier.lzz.serialization import importInvar
from barrier.decomposition.explicit import (
    Result,
    dwcl,
    get_invar_lazy
)
from barrier.decomposition.encoding import DecompositionEncoder

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("problem",help="Verification problem file")

    parser.add_argument("--task",
                        choices=["dwcl","reach","dump_vmt"],
                        default="dwcl",
                        help="Verify using dwcl or dump vmt file")

    parser.add_argument("--outvmt", help="Out vmt file")
    args = parser.parse_args()

    logging.basicConfig(level=logging.DEBUG)

    env = get_env()
    with open(args.problem, "r") as json_stream:
        problem_list = importInvar(json_stream, env)
    assert(len(problem_list) == 1)
    (problem_name, init, safe, dyn_sys, invariants, predicates) = problem_list[0]

    if (args.task == "dwcl"):
        print("Verifying using dwcl...")
        (res, invars) = dwcl(dyn_sys, invariants, predicates, init, safe)
        print("%s %s: %s" % (problem_name, str(res), str(invars)))

    if (args.task == "reach"):
        (res, reach) = get_invar_lazy(dyn_sys,
                                      invariants,
                                      predicates,
                                      init, safe)
        print("%s %s: %s" % (problem_name, str(res), str(reach)))

    elif (args.task == "dump_vmt"):
        if (not args.outvmt):
            print("Missing out file")
            sys.exit(1)

        print("Encoding verification problem in the vmt file to %s..." % args.outvmt)
        encoder  = DecompositionEncoder(env,
                                        dyn_sys,
                                        invariants,
                                        predicates,
                                        init,
                                        safe)
        (ts, p) = encoder.get_ts()

        with open(args.outvmt, "w") as outstream:
            ts.to_vmt(p, outstream)
            print("Printed to %s..." % args.outvmt)

if __name__ == '__main__':
    main()
