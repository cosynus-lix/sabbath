""" Implement the explicit invariant generation using semi-algebraic
decompositions from the paper:

A Method for Invariant Generation for Polynomial Continuous Systems
Sogokon, Ghorbal, Jackson, Platzer
FM2016

We implement the algorithms:
  - lazyreach
  - DWC
  - DWCL
"""

import logging

from enum import Enum

from barrier.system import DynSystem
from barrier.lzz.lzz import (lzz, lzz_fast)
from barrier.system import DynSystem
from barrier.lie import Derivator

from pysmt.logics import QF_NRA
from pysmt.shortcuts import (
    Solver,
    Implies, And, Not, Or,
    FALSE, TRUE,
    LT, Equals,
    Real,
)

from barrier.decomposition.utils import get_neighbors


class Result(Enum):
    UNSAFE=0
    UNKNOWN=1
    SAFE=2

# EOC Result

def _get_logger():
    return logging.getLogger(__name__)

def _get_solver():
    """ Use Z3 as standard solver for now.
    """
    return Solver(logic=QF_NRA, name="z3")

def _get_lzz_solver():
    return _get_solver()

def abstract(solver, polynomials, sigma):
    """ Compute the abstract state for model """

    abs_preds = []

    for a in polynomials:
        for (sign, first) in [(LT,True), (LT,False), (Equals,True)]:
            predicate = sign(a, Real(0)) if first else sign(Real(0), a)
            subs = predicate.substitute(sigma).simplify()
            if (solver.is_sat(subs)):
                abs_preds.append(predicate)
                break

    abs_state = frozenset(abs_preds)

    return abs_state


def get_invar_lazy_set(dyn_sys, invar,
                       polynomials,
                       init, safe,
                       get_solver = _get_solver):
    return _get_invar_lazy_set(dyn_sys.get_derivator(), invar,
                               polynomials,
                               init, safe,
                               get_solver = _get_solver)

def _get_invar_lazy_set(derivator, invar,
                        polynomials,
                        init, safe,
                        get_solver = _get_solver):
    """
    Implement the LazyReach invariant computation using semi-algebraic
    decomposition.

    Returns a pair (is_invar, set of abstract states) reachable from
    init and that is safe.
    """

    def solve(solver, formula):
        solver.push()
        solver.add_assertion(formula)
        sat = solver.solve()
        solver.pop()
        return sat

    def get_all_abstract(solver, polynomials):
        """ Compute the set of abstract state for the formula asserted in
        solver and according to polynomials.
        """
        def _get_all_abstract_rec(solver, polynomials, index, preds_trail, abs_states):
            if (index < len(polynomials)):
                a = polynomials[index]
                for (sign, first) in [(LT,True), (LT,False), (Equals,True)]:
                    predicate = sign(a, Real(0)) if first else sign(Real(0), a)

                    solver.push()
                    solver.add_assertion(predicate)

                    if (solver.solve()):
                        new_list = list(preds_trail)
                        new_list.append(predicate)

                        abs_states = _get_all_abstract_rec(solver, polynomials,
                                                           index + 1,
                                                           new_list,
                                                           abs_states)
                    solver.pop()
            else:
                abs_states.append(frozenset(preds_trail))
            return abs_states

        abs_states = _get_all_abstract_rec(solver, polynomials, 0, [], [])
        return abs_states


    logger = _get_logger()

    # remove duplicates, keep order
    has_poly = set()
    new_polynomials = []
    for p in polynomials:
        if not p in has_poly:
            new_polynomials.append(p)
            has_poly.add(p)
    polynomials = new_polynomials

    logger.info("get_invar_lazy with %d polynomials" % len(polynomials))

    # Set of abstract states reachable from init under invar.
    abs_visited = set()

    # Get abstract states that intersect with init and invar
    init_solver = get_solver()
    init_solver.add_assertion(init)
    init_solver.add_assertion(invar)

    invar_solver = get_solver()
    invar_solver.add_assertion(invar)

    safe_solver = get_solver()
    safe_solver.add_assertion(Not(safe))

    if solve(safe_solver, init):
        logger.info("Init is unsafe!")
        return (Result.UNSAFE, set())

    to_visit = list()
    while (init_solver.solve()):

        # [SM] Commented out
        # try:
        #     model = init_solver.get_model()
        #     sigma = {v: model[v] for v in dyn_sys.states()}
        #     init_abs_state = abstract(get_solver(), polynomials,
        #                               sigma)
        #     init_solver.add_assertion(Not(And(init_abs_state)))
        #     if not init_abs_state in abs_visited:
        #         to_visit.append(init_abs_state)
        # except:
        # Enum all the initial states
        # We have issue getting an algebraic model from mathematica and mathsat, apparently.
        logger.info("Enumerating all initial abstract states...")
        all_init_sates = get_all_abstract(init_solver, polynomials)
        logger.info("get_invar_lazy: found %d initial states" % len(all_init_sates))


        for init_abs_state in all_init_sates:
            init_solver.add_assertion(Not(And(init_abs_state)))
            to_visit.append(init_abs_state)

            # s = get_solver()
            # s.add_assertion(init)
            # print(init.serialize())
            # for l in init_abs_state:
            #     print((And(l)).serialize())
            #     s.add_assertion(And(l))
            # assert(s.solve())


        while 0 < len(to_visit):
            abs_state = to_visit.pop()

            if abs_state in abs_visited:
                continue

            logger.info("Visiting abs state: %s" %
                        " ".join([s.serialize() for s in abs_state]))

            if solve(safe_solver, And(abs_state)):
                logger.info("Abstract state %s is Unsafe!" % (" ".join([s.serialize() for s in abs_state])))
                return (Result.UNKNOWN, set())

            abs_visited.add(abs_state)
            init_solver.add_assertion(Not(And(abs_state)))

            # Visit all the neighbors of abs_state
            for neigh in get_neighbors(polynomials, abs_state):
                if neigh in abs_visited:
                    continue

                # Check if neigh has some intersection with invariant
                invar_solver.push()
                invar_solver.add_assertion(And(abs_state))
                if not invar_solver.solve():
                    invar_solver.pop()
                    continue
                invar_solver.pop()

                lzz_solver = get_solver()

                is_invar = lzz(lzz_solver, And(abs_state),
                               derivator,
                               And(abs_state),
                               Or(And(abs_state), And(neigh)))

                if (not is_invar):
                    logger.info("New trans from %s to %s" %
                                (" ".join([s.serialize() for s in abs_state]),
                                 " ".join([s.serialize() for s in neigh])))
                    to_visit.append(neigh)

                    if solve(safe_solver, And(neigh)):
                        logger.info("Abstract state %s is Unsafe!" % (" ".join([s.serialize() for s in neigh])))
                        return (Result.UNKNOWN, set())

    return (Result.SAFE, abs_visited)

def _set_to_formula(abs_state_set):
    formula = FALSE()
    for s in abs_state_set:
        formula = Or(formula, And(s))
    return formula

def get_invar_lazy(dyn_sys, invar, polynomials,
                   init, safe,
                   get_solver = _get_solver):
    return _get_invar_lazy(dyn_sys.get_derivator(),
                           invar, polynomials,
                           init, safe,
                           get_solver)

def _get_invar_lazy(derivator, invar, polynomials,
                    init, safe,
                    get_solver = _get_solver):
    """
    Compute the set of abstract reachable states for dyn_sys, starting
    from init and staying inside safe.

    """
    (res, reach_states) = _get_invar_lazy_set(derivator, invar,
                                              polynomials,
                                              init, safe,
                                              get_solver)
    return (res, _set_to_formula(reach_states))


def dwc_general(dwcl, derivator,
                invar, polynomials, init, safe,
                get_solver = _get_solver,
                get_lzz_solver = _get_lzz_solver):
    """
    Implements the Differential Weakening Cut (dwc) algorithm.

    Returns a formula representing an invariant for the vector field in derivator.
    """

    logger = _get_logger()
    logger.info("DWC...")

    r0 = Real(0)

    solver = get_solver()
    if (solver.is_unsat(And(invar, init))):
        logger.info("Init and invar unsat!")
        return (Result.SAFE, FALSE())
    elif (solver.is_valid(Implies(invar, safe))):
        # DW - Differential Weakening
        logger.info("DW: invar -> safe!")
        logger.info("%s -> %s" % (invar, safe))
        return (Result.SAFE, invar)
    else:
        rt0 = Real(0)

        logger.debug("Trying to remove predicates...")
        counter = 0
        for a in polynomials:
            counter += 1
            logger.debug("Testing DC on %d/%d..." % (counter, len(polynomials)))
            preds = {LT(rt0,a), LT(a,rt0), Equals(a,rt0)}
            for pred in preds:
                if solver.is_valid(Implies(And(invar, init), pred)):
                    lzz_solver = get_lzz_solver()
                    is_invar = lzz_fast(lzz_solver, pred, derivator,
                                        pred, invar)
                    lzz_solver.exit()
                    logger.debug("LZZ end...")

                    if (is_invar):
                        logger.debug("[DC] Found %s is invar (under %s)" % (pred.serialize(), invar.serialize()))
                        new_polynomials = list(polynomials)
                        new_polynomials.remove(a)
                        dwc_invar = dwc_general(dwcl, derivator,
                                                And(invar, pred),
                                                new_polynomials,
                                                init, safe,
                                                get_solver,
                                                get_lzz_solver)
                        return dwc_invar

        logger.debug("Trying to decompose...")
        counter = 0
        for a in polynomials:
            counter += 1
            logger.debug("Trying DDC %d/%d..." % (counter, len(polynomials)))

            preds = {LT(rt0,a), LT(a,rt0), Equals(a,rt0)}
            eq_0 = Equals(a,rt0)

            lzz_solver = get_lzz_solver()
            is_invar = lzz(lzz_solver, eq_0, derivator, eq_0, invar)
            lzz_solver.exit()

            if is_invar:
                inv_derivator = derivator.get_inverse()
                lzz_solver = get_lzz_solver()
                is_invar = lzz(lzz_solver, eq_0, inv_derivator, eq_0, invar)
                lzz_solver.exit()

                if (is_invar):
                    logger.debug("[DDC] Cannot leave %s = 0 " % (eq_0.serialize()))
                    new_polynomials = list(polynomials)
                    new_polynomials.remove(a)

                    def or_simpl(a,b):
                        if a == TRUE(): return a
                        elif b == TRUE(): return b
                        elif a == FALSE(): return b
                        elif b == FALSE(): return a
                        else: return Or(a,b)

                    result = Result.SAFE
                    res_invar = FALSE()
                    for pred in preds:
                        (dwc_res, dwc_invar) = dwc_general(dwcl,
                                                           derivator,
                                                           And(invar, pred),
                                                           new_polynomials,
                                                           And(init, pred),
                                                           safe,
                                                           get_solver,
                                                           get_lzz_solver)

                        # Invar holds under pred
                        dwc_invar = And(dwc_invar, pred)

                        if (dwc_res == Result.SAFE):
                            res_invar = or_simpl(res_invar, dwc_invar)
                        elif (dwc_res == Result.UNKNOWN):
                            # We cannot prove that one partition stays
                            # inside the safe states
                            res_invar = or_simpl(res_invar, dwc_invar)
                            result = Result.UNKNOWN
                        elif (dwc_res == Result.UNSAFE):
                            return (Result.UNSAFE, FALSE())
                        else:
                            # unreachable
                            assert (False)

                    return (result, res_invar)

        if not dwcl:
            return (Result.UNKNOWN, invar)
        else:
            logging.debug("Calling lazy invar computation with %d polynomials..." % (len(polynomials)))
            (res, reach_states) = _get_invar_lazy(derivator,
                                                  invar,
                                                  polynomials,
                                                  init, safe,
                                                  get_solver)

            # Add the invariant states to the set of reachable states
            # The predicates cut from DW are in the invariant
            return (res, And(invar, reach_states))


def dwc(dyn_sys, invar, polynomials, init, safe,
        get_solver = _get_solver,
        get_lzz_solver = _get_lzz_solver):
    derivator = dyn_sys.get_derivator()
    return dwc_general(False, derivator, invar, polynomials, init, safe,
                       get_solver, get_lzz_solver)

def dwcl(dyn_sys, invar, polynomials, init, safe,
         get_solver = _get_solver,
         get_lzz_solver = _get_lzz_solver):
    derivator = Derivator(dyn_sys.get_odes())
    return dwc_general(True, derivator, invar, polynomials, init, safe,
                       get_solver, get_lzz_solver)
