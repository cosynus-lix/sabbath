"""
Implement the LZZ procedure from:

Computing Semi-algebraic Invariants for Polynomial Dynamical Systems, Liu, Zhan, Zhao, EMSOFT11

"""

import logging

from barrier.lie import get_lie, get_lie_rank

from pysmt.shortcuts import (
    FALSE, TRUE,
    And, Or, Not, Implies,
    Equals, LE, GE, LT,
    Real,
)


def get_polynomial(predicate, GE):
    """
    Returns the polynomial p such that p >= 0 is equivalent
    to predicate.
    """

    polynomial = None
    node_type = predicate.node_type()

    if (predicate.is_le()):
        # left-hand side - right-hand side
        polynomial = predicate.args()[1] - predicate.args()[0]
    else:
        raise Exception("Predicate must be GE or LE "
                        "(instead was: %s)" % str(predicate))

    assert not polynomial is None

    return polynomial

def get_trans_f_p(poly, dyn_sys):
    """
    Returns the formula encoding the "transverse" set of the vector
    field f of the dyn_sys over the domain p >= 0.

    The transverse set represents all the points where the k-th lie
    derivative is different from 0 and negative, and where k is the
    first lie derivative different from 0.

    A point x in the transverse set is either:
    - not in p > 0; or
    - it is on the boundary of p >= 0, and the trajectory starting
    at x will exit p >= 0 immediately.
    """

    rank = get_lie_rank(dyn_sys.states(), poly, dyn_sys)
    assert rank >= 0

    trans_f_p = FALSE()
    prev_lie_eq_0 = None
    lie_at_i = None
    for i in range(rank+1):
        if (i == 0):
             lie_at_i = poly
             prev_lie_eq_0 = TRUE()
             trans_f_p_i = LT(poly, Real(0))
        else:
            assert not lie_at_i is None
            assert not prev_lie_eq_0 is None

            prev_lie_eq_0 = And(prev_lie_eq_0,
                                Equals(lie_at_i, Real(0)))
            lie_at_i = get_lie(lie_at_i, dyn_sys)
            trans_f_p_i = And(prev_lie_eq_0, LT(lie_at_i, Real(0)))

        trans_f_p = Or(trans_f_p, trans_f_p_i)

    return trans_f_p


def is_p_invar(solver, predicate, dyn_sys, init, invar):
    """ Check if the predicate is a an invariant for dyn_sys.

    Caveats: now we only check the "simple" invariant condition for a
    predicate (instead of a semi-algebraic set) and for an invariant
    that is also a single predicate (instead of a semi-algebraic set).

    The predicate must be of the form p >= 0, and the invariant of the
    form h >= 0.

    Returns true iff predicate is a continuous invariant.
    """

    logger = logging.getLogger(__name__)

    # get p >= 0 from predicate
    p_poly = get_polynomial(predicate, GE)
    # get p >= 0 from invariant
    h_poly = get_polynomial(invar, GE)

    trans_f_p = get_trans_f_p(p_poly, dyn_sys)
    trans_f_h = get_trans_f_p(h_poly, dyn_sys)

    # predicate is an invariant of the dynamical system if:
    #
    # 1. init -> predicate; and
    # 2. all the points on the border (i.e., p = 0) either:
    #    - do not escape the boundary (i.e., do not belong to
    #      trans_f_p); or
    #    - do not belong to the points escaping the invariants

    # check [init -> predicate]
    if (solver.is_valid(Implies(init, predicate))):
        # Check condition on the differential equation
        on_border = Equals(p_poly, Real(0))
        inside = Implies(on_border, Or(Not(trans_f_p), trans_f_h))

        if solver.is_valid(Implies(on_border, inside)):
            return True
        else:
            logger.debug("%s is not an invariant (consecution "
                         "condition failed)" % predicate)

            return False
    else:
        logger.debug("%s is not an invariant (initial "
                     "condition failed)" % predicate)
        return False

