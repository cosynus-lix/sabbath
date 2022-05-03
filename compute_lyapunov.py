import sys
import argparse
import logging

from fractions import Fraction

from pysmt.shortcuts import Symbol, REAL, get_env

from barrier.system import DynSystem
from barrier.lyapunov.lyapunov import synth_lyapunov, validate_lyapunov
from barrier.lzz.serialization import importInvar


def main():
    # x1,x2,x3,x4 = sp.symbols('x1 x2 x3 x4')
    # vars_list = [x1,x2,x3,x4]

    # vector_field = {
    #     x1 : -x1 + x2**3 - 3*x3*x4,
    #     x2 : -x1 - x2**3,
    #     x3 : x1 * x4 - x3,
    #     x4 : x1 * x3 - x4**4
    # }
    # feasible, lyap = test_lyapunov(factory, vector_field, vars_list, 4)
    # print(feasible, lyap)

    parser = argparse.ArgumentParser()
    parser.add_argument("problem",help="File containing the verification problem")

    parser.add_argument("--synth_algorithm",
                        choices=["sos","smt","quantifier_elimination"],
                        default="sos",
                        help="Technique used to synthesise the Lyapunov function.")

    parser.add_argument("--validate",
                        dest="validate", action='store_true',
                        help="Validate the lyapunov function")

    # parser.add_argument("--smt-synth",
    #                     choices=["z3","mathsat","cvc5"],
    #                     default="z3",
    #                     help="SMT solver to use for synthesis (still not implemented)")

    # parser.add_argument("--smt-validation",
    #                     choices=["z3","mathsat","cvc5"],
    #                     default="z3",
    #                     help="SMT solver to use for validation (still not implemented)")


    args = parser.parse_args()
    logging.basicConfig(level=logging.DEBUG)

    env = get_env()

    with open(args.problem, "r") as json_stream:
        problem_list = importInvar(json_stream, env)
    assert(len(problem_list) == 1)
    for p in problem_list:
        (problem_name, init, safe, sys, invariants, predicates) = p
        break


    (mathematica, smt) = {
        "sos" : (False,False),
        "smt" : (False,True),
        "quantifier_elimination" : (True,False),
    }[args.synth_algorithm]

    # Pre-processing
    assert (sys.is_linear)
    rescaled_systems = sys.get_rescaled_by_equilibrium_point()
    if len(rescaled_systems) != 1:
        print("Found multiple equilibrium point")

    for rescaled in rescaled_systems:
        print("Start synthesis using ", args.synth_algorithm)
        (res, lyapunov) = synth_lyapunov(rescaled, 2, mathematica, smt)

        if (res is None):
            print("Unknown!")
        elif (res):
            print("Found a Lyapunov function: ", lyapunov.serialize())

            if (args.validate):
                if (mathematica or smt):
                    print("Skipping validation (correct by construction)")
                else:
                    print ("Validating the Lyapunov function...")
                    is_valid = validate_lyapunov(rescaled, lyapunov)
                    print("Is valid: ", is_valid)

            else:
                if (not (mathematica or smt)):
                    print("WARNING: The Lyapunov function was obtained with numeric (unsound) methods")
        else:
            print("Cannot find a Lyapunov function")


if __name__ == "__main__":
    main()
