"""
Implement the LZZ procedure from:

Computing Semi-algebraic Invariants for Polynomial Dynamical Systems, Liu, Zhan, Zhao, EMSOFT11

"""

import logging
from functools import partial

from sabbath.system import DynSystem
from sabbath.lie import Derivator
from sabbath.lzz.dnf import ApplyPredicate, DNFConverter
from sabbath.formula_utils import get_max_poly_degree

import pysmt.operators as pysmt_op
from pysmt.shortcuts import (
    FALSE, TRUE,
    And, Or, Not, Implies,
    Equals, LE, GE, LT, GT,
    Minus,
    Real,
)

# [SM] Still in Testing - the Inf should distribute over an arbitrary boolean combination (according to the journal paper from Ghorbal and Sogokon)
AVOID_DNF_CONVERSION = False

class LzzOpt:
    def __init__(self, ivinf_via_inf = False, use_remainder = False):
        # remainder without inverting ivinf is not implemented now
        assert ((not use_remainder) or ivinf_via_inf)
        self.ivinf_via_inf = ivinf_via_inf
        self.use_remainder = use_remainder

    def __str__(self):
        return "ivinf_via_inf = %s\n" \
            "use_remainder = %s\n" % (str(self.ivinf_via_inf),
                                      str(self.use_remainder))

def debug_print_max_degree(logger, formula):
    if (logger.level <= logging.DEBUG):
        degree = get_max_poly_degree(formula)
        logger.debug("[LZZ] - max degree: %d" % degree)

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
    # lie derivatives = [l0,l1,...,lk]
    # returns:   p0 op 0
    #          | (p_0 = 0 & p_1 op 0)
    #          | (p_0 = 0 & p_1 = 0 & p_2 op 0)
    #          ...
    # op should be <,>,=
    #
    # sign_mult = True should encode IvInf...

    def get_lie_op_term(lie, op, sign_mult, i):
        if (sign_mult and i % 2 != 0):
            # on odd indexes we switch the sign of lie
            # this is to encode \phi+
            lie = Minus(Real(0), lie)
        return op(lie, Real(0))

    assert (op == GT or op == LT or op == Equals)

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

def get_inf_op_remainders(derivator, poly, op):
    # remainders = [r0,r1,...,rk]
    # returns: (rank,  r0 < 0
    #          | (r_0 = 0 & r_1 op 0)
    #          | (r_0 = 0 & r_1 = 0 & r_2 op 0)
    #          ...)

    logger = logging.getLogger(__name__)
    logger.debug("Get remainders")
    remainders = derivator.get_remainders_list(poly)
    trans_f_p = FALSE()
    index = 0
    for r in remainders:
        logger.debug("Get remainders, iteration %d" % index)
        j = 0
        disjunct = op(r, Real(0))
        while (j < index):
            disjunct = And(disjunct, Equals(remainders[j], Real(0)))
            j = j + 1

        trans_f_p = Or(trans_f_p, disjunct)
        index = index + 1

    logger.debug("Computed reminders, reached index %d" % index)
    return (len(remainders) - 1, trans_f_p)


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

    return get_generic_set(poly, dyn_sys.get_derivator(), LT, False, None)


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

# IN_{f,<}
def get_inf_lt_pred(derivator, bound, predicate):
    predicate = change_sign(predicate)
    rank = derivator.get_lie_rank(predicate) if bound is None else bound
    return get_generic_set(predicate, derivator, GT, False, rank)

# IN_{f,<=}
def get_inf_le_pred(derivator, bound, predicate):
    predicate = change_sign(predicate)
    rank = derivator.get_lie_rank(predicate) if bound is None else bound
    first_disjunct = get_generic_set(predicate, derivator, GT, False, rank)
    all_eq_0 = get_lie_eq_0(derivator, predicate, rank)
    res = Or(first_disjunct, all_eq_0)
    return res

# IN_{f,=}
# TODO: add specific encoding for equalities
def get_inf_eq_pred(derivator, bound, predicate):
    return And(get_inf_le_pred(derivator, bound, predicate),
               get_inf_le_pred(derivator, bound, Minus(Real(0), predicate)),
               )


# IN_{f,<}
def get_inf_lt_pred_remainders(derivator, predicate):
    predicate = change_sign(predicate)
    rank, inf = get_inf_op_remainders(derivator, predicate, GT)
    return inf

# IN_{f,<=}
def get_inf_le_pred_remainders(derivator, predicate):
    predicate = change_sign(predicate)
    rank, inf = get_inf_op_remainders(derivator, predicate, GT)
    all_eq_0 = get_lie_eq_0(derivator, predicate, rank)
    res = Or(inf, all_eq_0)
    return res

# IN_{f,=}
# TODO: add specific encoding for equalities
def get_inf_eq_pred_remainders(derivator, predicate):
    return And(get_inf_le_pred_remainders(derivator, predicate),
               get_inf_le_pred_remainders(derivator, Minus(Real(0), predicate)),
               )

# IvIN_{f,<}
def get_ivinf_lt_pred(derivator, predicate):
    predicate = change_sign(predicate)
    return get_generic_set(predicate, derivator, GT, True, None)

# IvIN_{f,<=}
def get_ivinf_le_pred(derivator, predicate):
    predicate = change_sign(predicate)
    rank = derivator.get_lie_rank(predicate)
    first_disjunct = get_generic_set(predicate, derivator, GT, True, rank)
    all_eq_0 = get_lie_eq_0(derivator, predicate, rank)
    res = Or(first_disjunct, all_eq_0)
    return res

# TODO: improve, simplify for equality
# IvIN_{f,=}
def get_ivinf_eq_pred(derivator, predicate):
    return And(get_ivinf_le_pred(derivator,predicate),
               get_ivinf_le_pred(derivator,Minus(Real(0), predicate)))


def unsupported(pred):
    raise Exception("Unsupported predicate ", pred.serialize())

def get_inf_dnf(lzz_opt, derivator, bound, formula):
    if (not lzz_opt.use_remainder):
        op_map = {pysmt_op.LT : partial(get_inf_lt_pred, derivator, bound),
                  pysmt_op.LE : partial(get_inf_le_pred, derivator, bound),
                  pysmt_op.EQUALS : partial(get_inf_eq_pred, derivator, bound) }
    else:
        # We still did not implement the bounded version when using remainders
        assert bound is None
        op_map = {pysmt_op.LT : partial(get_inf_lt_pred_remainders, derivator),
                  pysmt_op.LE : partial(get_inf_le_pred_remainders, derivator),
                  pysmt_op.EQUALS : partial(get_inf_eq_pred_remainders, derivator) }

    app = ApplyPredicate(op_map)
    inf_dnf = app.walk(formula)
    return inf_dnf


# We can compute IVINF(f,pred) as INF(-f, pred).
#
# The main drawback is that we will not reuse the memoization of the
# rank for a polynomial, since the vector field changes.
#
def get_ivinf_dnf(lzz_opt, derivator, bound, formula):
    if lzz_opt.ivinf_via_inf:
        inverse_derivator = derivator.get_inverse()
        return get_inf_dnf(lzz_opt, inverse_derivator, bound, formula)
    else:
        assert not lzz_opt.use_remainder
        assert bound is None
        app = ApplyPredicate({pysmt_op.LT : partial(get_ivinf_lt_pred, derivator),
                              pysmt_op.LE : partial(get_ivinf_le_pred, derivator),
                              pysmt_op.EQUALS : partial(get_ivinf_eq_pred, derivator) })
        ivinf_dnf = app.walk(formula)
        return ivinf_dnf

def lzz_with_cex(lzz_opt, solver, candidate, derivator, init, invar, bound=None, get_model=False):
    """ Implement the LZZ procedure.

    Check if the candidate an invariant for derivator, starting from
    init and subject to the invariant invar.
    """
    logger = logging.getLogger(__name__)

    # candidate is an invariant of the dynamical system if:
    #
    # 1. (init /\ Invar) => candidate; and
    # 2. (candidate /\ Invar /\ Inf(Invar)) => Inf(candidate); and
    # 3. (!candidate /\ Invar /\ IvInf(Invar)) => !IvInf(candidate)
    # are valid
    c1 = Implies(And(init, invar), candidate)
    logger.debug("Checking c1...")
    if (solver.is_valid(c1)):
        # Check condition on the differential equation

        if AVOID_DNF_CONVERSION:
            candidate_dnf = candidate
            invar_dnf = invar
        else:
            c = DNFConverter()
            candidate_dnf = c.get_dnf(candidate)
            invar_dnf = c.get_dnf(invar)

        logger.debug("Constructing c2...")
        c2 = Implies(And(candidate, invar,
                         get_inf_dnf(lzz_opt, derivator, bound, invar_dnf)),
                     get_inf_dnf(lzz_opt, derivator, bound, candidate_dnf))

        logger.debug("Checking c2...")
        debug_print_max_degree(logger, c2)

        if solver.is_valid(c2):
            logger.debug("Constructing c3...")
            c3 = Implies(And(Not(candidate), invar,
                             get_ivinf_dnf(lzz_opt, derivator, bound, invar_dnf)),
                         Not(get_ivinf_dnf(lzz_opt, derivator, bound, candidate_dnf)))

            logger.debug("Checking c3...")
            debug_print_max_degree(logger, c3)
            if solver.is_valid(c3):
                return (True, None)
            else:
                logger.debug("c3 failed!")
                model = solver.get_model() if get_model else None
                return (False, model)
        else:
            logger.debug("c2 failed!")
            model = solver.get_model() if get_model else None
            return (False, model)
    else:
        logger.debug("%s is not an invariant (initial "
                     "condition failed)" % candidate)
        model = solver.get_model() if get_model else None
        return (False, model)

def lzz(lzz_opt, solver, candidate, derivator, init, invar, bound=None):
    return lzz_with_cex(lzz_opt, solver, candidate, derivator, init, invar, bound, False)



def get_lzz_encoding(lzz_opt, candidate, derivator, invar):
    """
    Return the formula:
    ((candidate /\ Invar /\ Inf(Invar)) => Inf(candidate))  /\
    ((!candidate /\ Invar /\ IvInf(Invar)) => !IvInf(candidate))
    """

    # TODO: Factor with lzz checks
    if AVOID_DNF_CONVERSION:
        candidate_dnf = candidate
        invar_dnf = invar
    else:
        c = DNFConverter()
        candidate_dnf = c.get_dnf(candidate)
        invar_dnf = c.get_dnf(invar)

    c2 = Implies(And(candidate, invar,
                     get_inf_dnf(lzz_opt, derivator, invar_dnf)),
                 get_inf_dnf(lzz_opt, derivator, candidate_dnf))

    c3 = Implies(And(Not(candidate), invar,
                     get_ivinf_dnf(lzz_opt, derivator, invar_dnf)),
                 Not(get_ivinf_dnf(lzz_opt, derivator, candidate_dnf)))

    return And(c2, c3)

def lzz_fast(lzz_opt, solver, candidate, derivator, init, invar):
    """ Implement the "fast" LZZ procedure, as in Pegasus.

    The "fast" LZZ drops the possibly expensive conjuncts from
    the pre-condition.
    """

    logger = logging.getLogger(__name__)
    bound = None

    # candidate is an invariant of the dynamical system if:
    #
    # 1. init => candidate; and
    # 2. (candidate /\ Invar) => Inf(candidate); and
    # 3. (!candidate /\ Invar) => !IvInf(candidate)
    # are valid
    c1 = Implies(init, candidate)
    logger.debug("Checking c1 (fast)...")
    debug_print_max_degree(logger, c1)
    if (solver.is_valid(c1)):
        # Check condition on the differential equation

        if AVOID_DNF_CONVERSION:
            candidate_dnf = candidate
            invar_dnf = invar
        else:
            c = DNFConverter()
            candidate_dnf = c.get_dnf(candidate)
            invar_dnf = c.get_dnf(invar)

        c2 = Implies(And(candidate, invar),
                     get_inf_dnf(lzz_opt, derivator, bound, candidate_dnf))

        logger.debug("Checking c2 (fast)...")
        debug_print_max_degree(logger, c2)

        if solver.is_valid(c2):
            c3 = Implies(And(Not(candidate), invar),
                         Not(get_ivinf_dnf(lzz_opt, derivator, bound, candidate_dnf)))

            logger.debug("Checking c3 (fast)...")
            debug_print_max_degree(logger, c3)
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


