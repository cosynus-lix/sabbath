"""
Implement the LZZ procedure from:

Computing Semi-algebraic Invariants for Polynomial Dynamical Systems, Liu, Zhan, Zhao, EMSOFT11

"""

import logging
from functools import partial

from barrier.system import DynSystem
from barrier.lie import Derivator, get_lie, get_lie_rank
from barrier.lzz.dnf import ApplyPredicate, DNFConverter

import pysmt.operators as pysmt_op
from pysmt.shortcuts import (
    FALSE, TRUE,
    And, Or, Not, Implies,
    Equals, LE, GE, LT, GT,
    Minus,
    Real,
)


def get_polynomial_ge(predicate):
    """
    Returns the polynomial p such that p >= 0 is equivalent
    to predicate.
    """

    polynomial = None
    if (predicate.is_le()):
        # left-hand side - right-hand side
        polynomial = predicate.args()[1] - predicate.args()[0]
    else:
        raise Exception("Predicate must be LE "
                        "(instead was: %s)" % str(predicate))

    assert not polynomial is None

    return polynomial

def get_generic_set(poly, derivator, op, sign_mult, rank = None):
    """
    TODO: document, factor the computation of trans_f, \psi+ and \phi+
    """
    def get_lie_op_term(lie, op, sign_mult, i):
        if (sign_mult and i % 2 != 0):
            # on odd indexes we switch the sign of lie
            # this is to encode \phi+
            lie = Minus(Real(0), lie)
        return op(lie, Real(0))

    if rank is None:
        rank = derivator.get_lie_rank(poly)
    assert rank >= 0

    trans_f_p = FALSE()
    prev_lie_eq_0 = None
    lie_at_i = None
    for i in range(rank+1):
        if (i == 0):
             lie_at_i = poly
             prev_lie_eq_0 = TRUE()
             trans_f_p_i = get_lie_op_term(poly, op, sign_mult, i)
        else:
            assert not lie_at_i is None
            assert not prev_lie_eq_0 is None

            prev_lie_eq_0 = And(prev_lie_eq_0,
                                Equals(lie_at_i, Real(0)))
            lie_at_i = derivator.get_lie_der(lie_at_i)
            lie_term_at_i = get_lie_op_term(lie_at_i, op, sign_mult, i)
            trans_f_p_i = And(prev_lie_eq_0, lie_term_at_i)

        trans_f_p = Or(trans_f_p, trans_f_p_i)

    # logger = logging.getLogger(__name__)
    # logger.debug("get_generic_set(%s, %s, %s, %d): %s" %
    #              (str(poly), str(op), str(sign_mult), rank, str(trans_f_p.serialize())))

    return trans_f_p.simplify()

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

    return get_generic_set(poly, Derivator(dyn_sys.get_odes()), LT, False)


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
    p_poly = get_polynomial_ge(predicate)
    # get p >= 0 from invariant
    h_poly = get_polynomial_ge(invar)

    trans_f_p = get_trans_f_p(p_poly, dyn_sys)
    trans_f_h = get_trans_f_p(h_poly, dyn_sys)

    # predicate is an invariant of the dynamical system if:
    #
    # 1. init -> predicate; and
    # 2. all the points on the border (i.e., p = 0) either:
    #    - do not escape the boundary (i.e., do not belong to
    #      trans_f_p); or
    #    - do not belong to the points escaping the invariants

    # check [init -> predicate]]
    if (solver.is_valid(Implies(And(init, invar), predicate))):
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


def change_sign(predicate):
    if predicate.is_minus():
        # -(p1 - p2) = p2 - p1
        predicate = Minus(predicate.args()[1],
                          predicate.args()[0])
    else:
        predicate = Minus(predicate, Real(0))
    return predicate.simplify()

def get_lie_eq_0(derivator, predicate, rank):
    all_eq_0 = TRUE()
    for i in range(rank+1):
        if i == 0:
            lie_at_i = predicate
            all_eq_0 = Equals(lie_at_i, Real(0))
        else:
            lie_at_i = derivator.get_lie_der(lie_at_i)
            all_eq_0 = And(all_eq_0, Equals(lie_at_i, Real(0)))
    return all_eq_0

def get_inf_lt_pred(derivator, predicate):
    predicate = change_sign(predicate)
    return get_generic_set(predicate, derivator, GT, False)

def get_inf_le_pred(derivator, predicate):
    predicate = change_sign(predicate)
    rank = derivator.get_lie_rank(predicate)
    first_disjunct = get_generic_set(predicate, derivator, GT, False, rank)
    all_eq_0 = get_lie_eq_0(derivator, predicate, rank)
    res = Or(first_disjunct, all_eq_0)
    return res

def get_ivinf_lt_pred(derivator, predicate):
    predicate = change_sign(predicate)
    return get_generic_set(predicate, derivator, GT, True)

def get_ivinf_le_pred(derivator, predicate):
    predicate = change_sign(predicate)
    rank = derivator.get_lie_rank(predicate)
    first_disjunct = get_generic_set(predicate, derivator, GT, True, rank)
    all_eq_0 = get_lie_eq_0(derivator, predicate, rank)
    res = Or(first_disjunct, all_eq_0)
    return res

def get_inf_dnf(derivator, formula):
    app = ApplyPredicate({pysmt_op.LT : partial(get_inf_lt_pred, derivator),
                          pysmt_op.LE : partial(get_inf_le_pred, derivator)})
    inf_dnf = app.walk(formula)
    return inf_dnf


# DEBUG
IVINF_VIA_MINUS_F = True
def get_ivinf_dnf(derivator, formula):
    if IVINF_VIA_MINUS_F:
        inverse_derivator = derivator.get_inverse()
        return get_inf_dnf(inverse_derivator, formula)
    else:
        app = ApplyPredicate({pysmt_op.LT : partial(get_ivinf_lt_pred, derivator),
                              pysmt_op.LE : partial(get_ivinf_le_pred, derivator)})
        ivinf_dnf = app.walk(formula)
        return ivinf_dnf

def lzz(solver, candidate, derivator, init, invar):
    """ Implement the LZZ procedure.

    Check if the candidate an invariant for derivatoo, starting from
    init and subject to the invariant invar.
    """
    logger = logging.getLogger(__name__)

    # candidate is an invariant of the dynamical system if:
    #
    # 1. (init /\ Invar) => candidate; and
    # 2. (candidate /\ Invar /\ Inf(Invar)) => Inf(candidate); and
    # 3. (!candidate /\ Invar /\ IvInf(Invar)) => !IvInf(candidate)
    # are valid
    if (solver.is_valid(Implies(And(init, invar), candidate))):
        # Check condition on the differential equation

        c = DNFConverter()
        candidate_dnf = c.get_dnf(candidate)
        invar_dnf = c.get_dnf(invar)

        c2 = Implies(And(candidate, invar,
                         get_inf_dnf(derivator, invar_dnf)),
                     get_inf_dnf(derivator, candidate_dnf))

        if solver.is_valid(c2):
            c3 = Implies(And(Not(candidate), invar,
                             get_ivinf_dnf(derivator, invar_dnf)),
                         Not(get_ivinf_dnf(derivator, candidate_dnf)))

            if solver.is_valid(c3):
                return True
            else:
                logger.debug("c3 failed!")
                return False
        else:
            logger.debug("c2 failed!")
            return False
    else:
        logger.debug("%s is not an invariant (initial "
                     "condition failed)" % candidate)
        return False


def lzz_fast(solver, candidate, derivator, init, invar):
    """ Implement the "fast" LZZ procedure, as in Pegasus.

    The "fast" LZZ drops the possibly expensive conjuncts from
    the pre-condition.
    """

    logger = logging.getLogger(__name__)

    # candidate is an invariant of the dynamical system if:
    #
    # 1. init => candidate; and
    # 2. (candidate /\ Invar) => Inf(candidate); and
    # 3. (!candidate /\ Invar) => !IvInf(candidate)
    # are valid
    logger.debug("Checking c1: %s" % Implies(init, candidate).serialize())
    if (solver.is_valid(Implies(init, candidate))):
        # Check condition on the differential equation

        c = DNFConverter()
        candidate_dnf = c.get_dnf(candidate)
        invar_dnf = c.get_dnf(invar)

        c2 = Implies(And(candidate, invar),
                     get_inf_dnf(derivator, candidate_dnf))

        if solver.is_valid(c2):
            c3 = Implies(And(Not(candidate), invar),
                         Not(get_ivinf_dnf(derivator, candidate_dnf)))

            if solver.is_valid(c3):
              return True
            else:
              logger.debug("c3 failed!")
              return False
        else:
            logger.debug("c2 failed!")
            return False
    else:
        logger.debug("c1 failed!" % candidate)
        return False


