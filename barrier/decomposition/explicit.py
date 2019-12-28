""" Implement the explicit invariant generation using semi-algebraic
decompositions from the paper:

A Method for Invariant Generation for Polynomial Continuous Systems
Sogokon, Ghorbal, Jackson, Platzer
FM2016

"""

import barrier.lzz
from barrier.system import DynSystem

from pysmt.shortcuts import (
    Solver,
    Implies, And, Not,
    LT, Equals,
    Real
)

from pysmt.logics import QF_NRA

def get_solver():
    solver = Solver(logic=QF_NRA, name="z3")
    return solver

def abstract(solver, polynomials, model):
    """ Compute the abstract state for model """

    abs_preds = []
    sigma = {v: model[v] for v in dyn_sys.states}

    for a in polynomials:
        for (sign, first) in [(LT,True), (LT,False), (Equals,True)]:
            predicate = sign(a, Real(0)) if first else sign(Real(0), a)
            subs = predicate.substitute(sigma).simplify()
            if (solver.is_sat(subs)):
                abs_preds.append(predicate)
                break

    abs_state = frozenset(abs_preds)

    return abs_state

def get_neighbors(polynomials, abs_state):
    """ Get the neighbors of abs_state """
    def _get_neighbors_rec(polynomials, index, abs_state, res):
        if index == len(polynomials):
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

            if sign == LT:
                # < -> {=}
                res.append(Equals(a, Real(0)))
                return _get_neighbors_rec(polynomials,
                                          index+1,
                                          abs_state,
                                          res)
            else:
                # = -> {<, >}
                res.append(LT(a, Real(0)))
                res.append(LT(Real(0), a))
                return _get_neighbors_rec(polynomials,
                                          index+1,
                                          abs_state,
                                          res)
    res = _get_neighbors_rec(polynomials, 0, abs_state, [])
    return res

def get_invar_lazy(dyn_sys, invar,
                   polynomials,
                   init, safe,
                   get_solver = get_solver):
    """
    Implement the LazyReach invariant computation using semi-algebraic
    decomposition.
    """

    # Set of abstract states reachable from init under invar.
    abs_visited = set()

    # Get abstract states that intersect with init and invar
    init_solver = get_solver()
    init_solver.add_assertion(init)
    init_solver.add_assertion(invar)

    invar_solver = get_solver()
    invar_solver.add_assertion(invar)

    to_visit = list()
    while (init_solver.solve()):
        init_abs_state = abstract(get_solver(), polynomials, init_init_solver.get_model())
        init_solver.add_assertion(Not(And(init_abs_state)))

        if not init_abs_state in abs_visited:
            to_visit.push(init_abs_state)

        while 0 < len(to_visit):
            abs_state = to_visit.pop()
            if abs_state in abs_visited:
                continue
            abs_visited.add(abs_state)

            # Visit all the neighbors of abs_state
            for neigh in get_neighbors(polynomials, abs_state):
                if neigh in abs_visited:
                    continue

                # Check if neigh has some intersection with invariant
                if not invar_solver.solve(And(abs_state)):
                    continue

                lzz_solver = get_solver()
                is_invar = lzz(lzz_solver, And(abs_state), dyn_sys,
                               And(abs_state),
                               Or(And(abs_state), And(neigh)))

                if (not is_invar):
                    to_visit.append(neigh)

    return abs_visited
