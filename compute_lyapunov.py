import sys
import argparse
import logging

from fractions import Fraction

from pysmt.shortcuts import Symbol, REAL, get_env

from barrier.system import DynSystem
from barrier.lyapunov import synth_lyapunov, validate_lyapunov
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

    parser.add_argument("--solver",
                        choices=["z3","mathsat","mathematica"],
                        default="z3",
                        help="SMT solver to use")

    args = parser.parse_args()
    logging.basicConfig(level=logging.DEBUG)

    env = get_env()

    with open(args.problem, "r") as json_stream:
        problem_list = importInvar(json_stream, env)
    assert(len(problem_list) == 1)
    for p in problem_list:
        (problem_name, init, safe, sys, invariants, predicates) = p
        break

    mathematica = False
    smt = True
    (res, lyapunov) = synth_lyapunov(sys, 2, mathematica, smt)

    if (res is None):
        print("Unknown!")
    elif (res):
        print("Found a Lyapunov function: ", lyapunov.serialize())

        if (not mathematica and not smt):
            is_valid = validate_lyapunov(sys, lyapunov)
            print("Is valid: ", is_valid)
    else:
        print("Lyapunov function does not exist!")


if __name__ == "__main__":
    main()
