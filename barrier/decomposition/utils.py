"""
Common utils for computing/encoding the algebraic decomposition.

"""

from barrier.lie import Pysmt2Sympy, Sympy2Pysmt
from barrier.formula_utils import PredicateExtractor

from pysmt.shortcuts import (
    Real,
    Equals, LT
)


def get_neighbors(polynomials, abs_state):
    """ Get the neighbors of abs_state """
    def _get_neighbors_rec(signs,
                           polynomials, index,
                           abs_state,
                           trail, res):
        if index == len(polynomials):
            assert(len(trail) == len(polynomials))
            res.add(frozenset(trail))
            return res
        else:
            a = polynomials[index]
            pair = None
            for (sign, first) in [(LT,True), (LT,False), (Equals,True)]:
                predicate = sign(a, Real(0)) if first else sign(Real(0), a)
                if predicate in abs_state:
                    pair = (sign,first)
                    break

            assert not pair is None
            assert not predicate is None

            if sign == LT and sign in signs:
                # < -> {=}
                new_trail = set(trail)
                new_trail.add(Equals(a, Real(0)))
                trail.add(predicate)

                return _get_neighbors_rec(signs, # do not change predicates
                                          polynomials,
                                          index+1,
                                          abs_state,
                                          new_trail,
                                          _get_neighbors_rec(signs,
                                                             polynomials,
                                                             index+1,
                                                             abs_state,
                                                             trail,
                                                             res))
            elif sign == Equals and sign in signs:
                # = -> {<, >}
                new_trail = set(trail)
                new_new_trail = set(trail)

                trail.add(predicate)
                new_trail.add(LT(a, Real(0)))
                new_new_trail.add(LT(Real(0), a))

                return _get_neighbors_rec(signs,
                                          polynomials,
                                          index+1,
                                          abs_state,
                                          new_new_trail,
                                          _get_neighbors_rec(signs,
                                                             polynomials,
                                                             index+1,
                                                             abs_state,
                                                             new_trail,
                                                             _get_neighbors_rec(signs,
                                                                                polynomials,
                                                                                index+1,
                                                                                abs_state,
                                                                                trail,
                                                                                res)))
            else:
                trail.add(predicate)
                return _get_neighbors_rec(signs,
                                          polynomials,
                                          index + 1,
                                          abs_state,
                                          trail,
                                          res)

    res_lt = _get_neighbors_rec({LT}, polynomials, 0, abs_state, set(), set())
    res_eq = _get_neighbors_rec({Equals}, polynomials, 0, abs_state, set(), set())
    res_lt.update(res_eq)
    res_lt.remove(abs_state)
    return res_lt


def get_poly_from_pred(pred):
    """
    Get a polynomial from a predicate.
    """
    poly = None

    assert(pred.is_equals() or
           pred.is_le() or
           pred.is_lt())

    # left-hand side - right-hand side
    poly = pred.args()[1] - pred.args()[0]

    return (poly, pred.node_type())

def get_unique_poly_list(poly_list):
    """
    The algebraic decomposition obtained with a polynomial p and with -p are the
    same.

    We want to just keep one of p here.
    """

    pysmt2sympy = Pysmt2Sympy()
    sympy2pysmt = Sympy2Pysmt()

    poly_set = set()
    new_poly_list = []
    for p in poly_list:
        sympy_p = (pysmt2sympy.walk(p)).expand()
        sympy_minus_p = (- sympy_p).expand()

        if (not ((sympy_p in poly_set) or
                 (sympy_minus_p in poly_set))):
            new_poly_list.append(p)
            poly_set.add(sympy_p)
            poly_set.add(sympy_minus_p)

    return new_poly_list

def add_poly_from_formula(poly_list, formula, env):
    new_preds = 0
    for pred in PredicateExtractor.extract_predicates(formula,
                                                      env):
        poly_list.append(get_poly_from_pred(pred)[0])
        new_preds += 1
