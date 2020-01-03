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

from barrier.system import DynSystem
from barrier.lzz.lzz import (lzz, lzz_fast)
from barrier.system import DynSystem

from pysmt.logics import QF_NRA
from pysmt.shortcuts import (
    Solver,
    Implies, And, Not, Or,
    FALSE,
    LT, Equals,
    Real,
    get_env
)



def _get_logger():
    return logging.getLogger(__name__)

def get_z3():
    return Solver(logic=QF_NRA, name="z3")

def get_mathsat_smtlib():
    name = "mathsat-smtlib"
    logics = [QF_NRA]

    env = get_env()
    if not env.factory.is_generic_solver(name):
        path = ["/Users/sergiomover/Tools/mathsat5/build/mathsat"]
        env.factory.add_generic_solver(name, path, logics)

    return Solver(name=name, logic=logics[0]) #, solver_options={'debug_interaction':True})

def _get_solver():
    return get_z3()

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

def _get_neighbors(polynomials, abs_state):

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

def get_invar_lazy_set(dyn_sys, invar,
                       polynomials,
                       init, safe,
                       get_solver = _get_solver):
    """
    Implement the LazyReach invariant computation using semi-algebraic
    decomposition.
    """

    def solve(solver, formula):
        solver.push()
        solver.add_assertion(formula)
        sat = solver.solve()
        solver.pop()
        return sat

    logger = _get_logger()
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
        logger.info("Init unsafe!")
        return set()
    # Here all the initial states are safe

    to_visit = list()
    while (init_solver.solve()):
        model = init_solver.get_model()
        sigma = {v: model[v] for v in dyn_sys.states()}
        init_abs_state = abstract(get_solver(), polynomials,
                                  sigma)

        init_solver.add_assertion(Not(And(init_abs_state)))

        if not init_abs_state in abs_visited:
            to_visit.append(init_abs_state)

        while 0 < len(to_visit):
            abs_state = to_visit.pop()

            if abs_state in abs_visited:
                continue

            logger.info("Visiting abs state: %s" %
                        " ".join([s.serialize() for s in abs_state]))
            abs_visited.add(abs_state)

            # Visit all the neighbors of abs_state
            for neigh in _get_neighbors(polynomials, abs_state):
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
                is_invar = lzz(lzz_solver, And(abs_state), dyn_sys,
                               And(abs_state),
                               Or(And(abs_state), And(neigh)))

                if (not is_invar):
                    logger.info("New trans from %s to %s" %
                                (" ".join([s.serialize() for s in abs_state]),
                                 " ".join([s.serialize() for s in neigh])))
                    to_visit.append(neigh)

                    if solve(safe_solver, And(neigh)):
                        logger.info("Unsafe!")
                        return set()
    return abs_visited

def _set_to_formula(abs_state_set):
    formula = FALSE()
    for s in abs_state_set:
        formula = Or(formula, And(s))
    return formula

def get_invar_lazy(dyn_sys, invar,
                   polynomials,
                   init, safe,
                   get_solver = _get_solver):
    reach = get_invar_lazy_set(dyn_sys, invar,
                               polynomials,
                               init, safe,
                               get_solver)
    return _set_to_formula(reach)


def dwc_general(dwcl, dyn_sys, invar, polynomials, init, safe,
                get_solver = _get_solver):
    """
    Implement the Differential Weakening Cut algorithm

    Returns a formula representing an invariant
    """

    logger = _get_logger()
    logger.info("DWC...")

    r0 = Real(0)

    solver = get_solver()
    if (solver.is_unsat(And(invar, init))):
        logger.info("Init (%s) outside invariant (%s)!" % (init.serialize(), invar.serialize()))
        return FALSE()
    elif (solver.is_valid(Implies(invar, safe))):
        # DW - Differential Weakening
        logger.info("DW: invar -> safe!")
        logger.info("%s -> %s" % (invar, safe))
        return invar
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


                    lzz_solver = _get_solver()
                    logger.debug("LZZ for %s..." % (pred.serialize()))
                    is_invar = lzz_fast(lzz_solver, pred, dyn_sys,
                                        pred, invar)
                    lzz_solver = None
                    logger.debug("LZZ end...")

                    if (is_invar):
                        logger.debug("DC on %s" % (pred.serialize()))
                        new_polynomials = list(polynomials)
                        new_polynomials.remove(a)
                        return dwc(dyn_sys, And(invar, pred),
                                   new_polynomials,
                                   init, safe, get_solver)

        logger.debug("Trying to decompose...")
        counter = 0
        for a in polynomials:
            counter += 1
            logger.debug("Trying to DC %d/%d..." % (counter, len(polynomials)))

            preds = {LT(rt0,a), LT(a,rt0), Equals(a,rt0)}
            eq_0 = Equals(a,rt0)

            lzz_solver = _get_solver()
            is_invar = lzz(lzz_solver, eq_0, dyn_sys, eq_0, invar)
            if is_invar:
                inv_dyn_sys = DynSystem.get_inverse(dyn_sys)

                lzz_solver = _get_solver()
                is_invar = lzz(lzz_solver, eq_0, inv_dyn_sys, eq_0, invar)

                if (is_invar):
                    logger.debug("Decomposing on %s" % (eq_0.serialize()))
                    new_polynomials = list(polynomials)
                    new_polynomials.remove(a)

                    res = FALSE()
                    for pred in preds:
                        pred_res = dwc(dyn_sys, And(invar, pred),
                                       new_polynomials,
                                       And(init, pred), safe, get_solver)
                        res = Or(res, pred_res)
                    return res
            lzz_solver = None

        if not dwcl:
            return invar
        else:
            return get_invar_lazy(dyn_sys, invar,
                                  polynomials,
                                  init, safe,
                                  get_solver)


def dwc(dyn_sys, invar, polynomials, init, safe,
        get_solver = _get_solver):
    return dwc_general(False, dyn_sys, invar, polynomials, init, safe, get_solver)

def dwcl(dyn_sys, invar, polynomials, init, safe,
         get_solver = _get_solver):
    return dwc_general(True, dyn_sys, invar, polynomials, init, safe, get_solver)
