""" Verify the safety of a dynamical system.

"""

import sys
import argparse
import logging
import os
import signal
import sys

from functools import partial

from pysmt.exceptions import SolverAPINotFound
from pysmt.logics import QF_NRA
from pysmt.shortcuts import (
    get_env, Solver
)

from sabbath.decomposition.predicates import (
    AbsPredsTypes, get_polynomials_ha,
    get_polynomials_invar_problem
)
from sabbath.decomposition.utils import get_unique_poly_list
from sabbath.serialization.invar_serialization import importInvarVer
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
from sabbath.vmt.vmt_engines import prove_ts, VmtResult
from sabbath.mathematica.mathematica import (
    get_mathematica, exit_callback_print_time, OutOfTimeSolverError, MathematicaSession
)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("problem",help="Verification problem file")

    parser.add_argument("--task",
                        choices=["dwcl","dwcl_ic3","reach","dump_vmt","ic3ia"],
                        default="dwcl",
                        help="Verify using dwcl, explicit reachability analysis, ic3ia, or dump the abstraction to vmt file")

    parser.add_argument("--solver",
                        choices=["z3","mathsat","mathematica"],
                        default="z3",
                        help="SMT solver to use")

    parser.add_argument("--mathematica-budget_time",
                        default=0,
                        type=int,
                        help="Time out for the mathematica kernel (Default: 0 (no timeout))")

    parser.add_argument("--outvmt", help="Output vmt file")
    parser.add_argument("--outpred", help="Output predicates file")
    parser.add_argument("--encode_init_and_prop",
                        choices=["true","false"],
                        default="false",
                        help="Retiming to encode init and property")

    parser.add_argument("--direct_encoding",
                        choices=["true","false"],
                        default="false",
                        help="Use the direct encoding (must be used in IC3-IA)")

    parser.add_argument("--simplified_ia_encoding",
                        dest="simplified_ia_encoding", action='store_true',
                        help="Use simplified IA encoding (with input variables)")

    parser.add_argument("--abstraction",
                        choices=["factors","lie","invar","prop","preds_from_model"],
                        action='append', nargs='+',
                        help="Polynomials to use in the abstraction (default: take from input)",
                        default=[])


    args = parser.parse_args()

    logging.basicConfig(level=logging.INFO)


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
        problem_list = importInvarVer(json_stream, env)
    assert(len(problem_list) == 1)
    invar_problem = problem_list[0]
    (problem_name, init, safe, dyn_sys, invariants, predicates) = invar_problem
    print("parsed problem...")
    print(dyn_sys)
    print("Invariant ", invariants.serialize())
    print("Init ", init.serialize())
    print("Safe ", safe.serialize())

    # Always use remainders
    lzz_opt = LzzOpt(True, True)

    if (args.simplified_ia_encoding):
        simplified_ia_encoding = True
    else:
        simplified_ia_encoding = False
    print("Using simplified ia: " + str(simplified_ia_encoding))

    abs_type = AbsPredsTypes.NONE.value
    preds_from_model = False
    if args.abstraction:
        for l in args.abstraction:
            for t in l:
                if t == "factors":
                    abs_type = abs_type | AbsPredsTypes.FACTORS.value
                elif t == "prop":
                    abs_type = abs_type | AbsPredsTypes.PROP.value
                elif t == "lie":
                    abs_type = abs_type | AbsPredsTypes.LIE.value
                elif t == "invar":
                    abs_type = abs_type | AbsPredsTypes.INVAR.value
                elif t == "preds_from_model":
                    preds_from_model = True
                else:
                    raise Exception("Unknown abstraction type %s " % t)
    else:
        preds_from_model = True

    auto_poly = get_polynomials_invar_problem(invar_problem, abs_type, env)
    if (not preds_from_model):
        predicates = auto_poly
    else:
        predicates = set(predicates)
        predicates.update(auto_poly)
    predicates = get_unique_poly_list(predicates)

    print("Using polynomials:")
    for p in predicates:
        print(p.serialize())
    print("----")

    if (args.task in ["dwcl","reach","dwcl_ic3"]):
        exit_callback_inst = partial(exit_callback_print_time, outstream=sys.stdout)

        solvers = {"z3" : partial(Solver, logic=QF_NRA, name="z3"),
                   "mathematica" : partial(get_mathematica,
                                           budget_time=args.mathematica_budget_time,
                                           env=get_env(),
                                           exit_callback=exit_callback_inst),
                   "mathsat" : partial(get_mathsat_smtlib, env=get_env())}

        get_solver = solvers[args.solver]

        try:
            if (args.task in ["dwcl", "dwcl_ic3"]):
                print("Verifying using " + args.task + "...")
                (res, invars) = dwcl(dyn_sys, invariants, predicates, init, safe,
                                     get_solver, get_solver, sys.stdout,
                                     args.task == "dwcl_ic3",
                                     lzz_opt)

            elif (args.task == "reach"):
                print("Verifying using reachability analysis...")
                (res, invars) = get_invar_lazy(dyn_sys,
                                               invariants,
                                               predicates,
                                               init, safe, get_solver,
                                               sys.stdout,
                                               lzz_opt)

            print("%s %s: %s" % (problem_name, str(res), str(invars)))
        except SolverAPINotFound as e:
            print("Did not find the solver.")
        finally:
            if (args.solver == "mathematica"):
                MathematicaSession.terminate_session()

    else:
        assert(args.task == "dump_vmt" or args.task == "ic3ia")
        if (args.task == "dump_vmt"):
            if (not args.outvmt):
                print("Missing output name for vmt file")
                sys.exit(1)
            if (not args.outpred):
                print("Missing output name for predicates  file")
                sys.exit(1)


        print("Encoding verification problem in the vmt file to %s..." % args.outvmt)

        encode_init_and_prop = False
        if (args.encode_init_and_prop == "true"):
            encode_init_and_prop = True
        else:
            encode_init_and_prop = False

        direct_encoding = False
        if (args.direct_encoding == "true"):
            direct_encoding = True
        else:
            assert args.direct_encoding == "false"
            direct_encoding = False
        print("Re-encoding init and prop? %d" % encode_init_and_prop)

        opt = DecompositionOptions(encode_init_and_prop,
                                   encode_init_and_prop,
                                   False,
                                   False,
                                   lzz_opt)
        encoder  = DecompositionEncoder(env,
                                        dyn_sys,
                                        invariants,
                                        predicates,
                                        init,
                                        safe,
                                        opt,
                                        sys.stdout)

        if (direct_encoding):
            print("Using the direct encoding to IA...")
            (ts, p, predicates) = encoder.get_direct_ts_ia()
        else:
            print("Using the manual encoding to IA...")
            (ts, p, predicates) = encoder.get_ts_ia(simplified_ia_encoding)

        if (args.task == "dump_vmt"):
            with open(args.outvmt, "w") as outstream:
                ts.to_vmt(outstream, p)
                print("Printed vmt to %s..." % args.outvmt)

            with open(args.outpred, "w") as outstream:
                TS.dump_predicates(outstream, predicates)
                print("Printed predicates to %s..." % args.outpred)
        else:
            assert(args.task == "ic3ia")
            vmtres = prove_ts(ts, p, predicates)

            if (vmtres == VmtResult.SAFE):
                res = Result.SAFE
            else:
                res = Result.UNKNOWN

            print("%s %s" % (problem_name, str(res) ))


if __name__ == '__main__':
    main()
    sys.exit(os.EX_OK)
