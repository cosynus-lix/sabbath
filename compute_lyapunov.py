import sys
from fractions import Fraction

from pysmt.shortcuts import Symbol, REAL

from barrier.system import DynSystem
from barrier.lyapunov import synth_lyapunov, validate_lyapunov



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

    x1, x2 = [Symbol("x%s" % (i+1), REAL) for i in range(2)]

    sys = DynSystem([x1,x2], [], [],
                    {
                        x1 : -x1,
                        x2 : x1 - x2
                    },
                    {})


    sys = DynSystem([x1,x2], [], [],
                    {
                        x1 : -2 * x1,
                        x2 : x1 - x2
                    },
                    {})


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
