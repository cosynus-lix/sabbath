""" Verify the safety of a hybrid system
"""

import sys
import argparse
import logging
import os
import signal
import sys

from sabbath.lzz.lzz import LzzOpt
from sabbath.serialization.hybrid_serialization import importHSVer
from sabbath.decomposition.predicates import AbsPredsTypes, get_polynomials_ha
from sabbath.decomposition.encoding import (
    DecompositionOptions, DecompositionEncoderHA
)

from sabbath.decomposition.explicit import Result

from sabbath.decomposition.utils import get_unique_poly_list

from sabbath.vmt.vmt_engines import prove_ts, VmtResult

from pysmt.shortcuts import (
    get_env
)



def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("problem",help="Verification problem file")

    parser.add_argument("--task",
                        choices=["dump_vmt","ic3ia"],
                        default="ic3ia",
                        help="Verify an invariant property on a hybrid system")

    parser.add_argument("--abstraction",
                        choices=["factors","lie","invar","prop","preds_from_model"],
                        action='append', nargs='+',
                        help="Polynomials to use in the abstraction")

    parser.add_argument("--outvmt", help="Output vmt file")
    parser.add_argument("--outpred", help="Output predicates file")

    args = parser.parse_args()

    logging.basicConfig(level=logging.DEBUG)

    preds_from_model = False
    abs_type = AbsPredsTypes.NONE.value
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

    # Read HS
    print("Parsing problem...")
    env = get_env()
    with open(args.problem, "r") as f:
        problem = importHSVer(f, env)

    # Get the polynomials for the abstraction
    poly_from_ha = get_polynomials_ha(problem.ha, problem.prop, abs_type, env)

    if (not preds_from_model):
        polynomials = poly_from_ha
    else:
        polynomials = set(problem.predicates)
        polynomials.update(poly_from_ha)
    polynomials = get_unique_poly_list(polynomials)

    print("List of polynomials")
    for p in polynomials:
        print(p.serialize())
    print("")

    # Encoding
    lzz_opt = LzzOpt(True, True) # always use the remainder
    options = DecompositionOptions(False, False, False, False, lzz_opt)
    encoder = DecompositionEncoderHA(env, problem.ha, polynomials, problem.prop, options, None)

    (ts, p, predicates) = encoder.get_ts_ia()

    if (args.task == "dump_vmt"):
        if (not args.outvmt):
            print("Missing output name for vmt file")
            sys.exit(1)
        if (not args.outpred):
            print("Missing output name for predicates  file")
            sys.exit(1)

        with open(args.outvmt, "w") as f:
            ts.to_vmt(f, p)
        with open(args.outpred, "w") as outstream:
            ts.dump_predicates(outstream, predicates)
    else:
        assert(args.task == "ic3ia")
        vmtres = prove_ts(ts, p, predicates)

        if (vmtres == VmtResult.SAFE):
            res = Result.SAFE
        else:
            res = Result.UNKNOWN

        print("%s %s" % (problem.name, str(res) ))


if __name__ == '__main__':
    main()
    sys.exit(os.EX_OK)
