""" Implements the (linear) encoding of the semi-algebraic decomposition.
"""

from functools import partial

from pysmt.shortcuts import (
    TRUE, FALSE,
    Real,
    Not, And, Or, Implies, Iff, Equals,
    Equals, GE, GT, LT, LE
)

class DecompositionEncoder:
    def __init__(self, dyn_sys,
                 invar,
                 polynomials,
                 init, safe):
        return


    def get_symbolic_decomposition():
        """
        Input (a safety verification problem):
        - a polynomial dynamical system der(X) = p(X)
        - a set of initial states I(X)
        - a set of invariant sates Inv(X)
        - a safety property P(X)
        - a set of polynomials defining the abstraction

        Output (a symbolic transition system):
        - I'(X)
        - T'(X,X',Z)
        - P'(X)
        can be used for predicate abstraction.
        """
        return

    def _get_trans_enc(self):
        return

    def _get_lzz_tr_enc(self):
        return

    @staticmethod
    def _get_neigh_encoding(poly, get_next_formula):
        zero = Real(0)

        def _change_noteq(p, get_next):
            next_p = get_next(p)
            return And(
                Implies(GT(p, zero), Or( Equals(next_p, zero),
                                         GT(next_p, zero))),
                And(Implies(LT(p, zero), Or( Equals(next_p, zero),
                                             LT(next_p, zero))),
                    Implies(Equals(p, zero),Equals(next_p, zero)))
            )

        def _change_eq(p, get_next):
            next_p = get_next(p)
            return And(Implies(GT(p, zero), GT(next_p, zero)),
                       Implies(LT(p, zero), LT(next_p, zero)))

        def _iter(poly, p_fun):
            res = TRUE()
            for p in poly:
                res = And(res, p_fun(p))
            return res

        return Or(_iter(poly, partial(_change_noteq,
                                      get_next = get_next_formula)),
                  _iter(poly, partial(_change_eq, get_next = get_next_formula)))

