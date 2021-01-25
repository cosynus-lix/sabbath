""" Utilities to extract predicates from the invariant verification
problem.

Examples of predicates are
  - factors of the RHS of the ODEs and of the safety property (called "factors")
  - the (first) lie derivatives
  - algebraic invariants (e.g., darboux polynomials) --- still not implemented
"""

from enum import Enum

from pysmt.shortcuts import get_env

from barrier.formula_utils import PredicateExtractor
from barrier.lie import Derivator, Pysmt2Sympy, Sympy2Pysmt, add_poly_factors
from barrier.decomposition.utils import (
    get_poly_from_pred, get_unique_poly_list, get_poly_from_pred
)



class AbsPredsTypes(Enum):
    """
    Types of predicates to extract from the verification problem
    """
    NONE = 0
    FACTORS = 1
    LIE = 2
    INVAR = 4
    GUARDS = 8
    PROP = 16


def add_factors(derivator, problem, predicates_set, env):
    """ Add the factors of the ODEs and of the safety
    property in the list of predicates """

    def add_factors_for_preds(derivator, formula, factor_set, env):
        """ Add all the factors in a formula """
        for pred in PredicateExtractor.extract_predicates(formula, env):
            poly = get_poly_from_pred(pred)[0]
            derivator.add_poly_factors(poly, factor_set)

    (problem_name, ant, cons, dyn_sys, invar, predicates) = problem

    # factors from property
    add_factors_for_preds(derivator, cons, predicates_set, env)

    # factors from RHS of the odes
    for v in dyn_sys.states():
        ode = dyn_sys.get_ode(v)
        derivator.add_poly_factors(ode, predicates_set)

def add_lie(derivator, problem, predicates_set):
    """ Extend predicates_set with the set of lie derivatives """
    predicates_set_copy = set(predicates_set)
    for pred in predicates_set_copy:
        predicates_set.add(derivator.get_lie_der(pred))

def add_pred_formula(formula, predicates):
    raise NotImplementedError()


def get_predicates(invar_problem, preds_types):
    (problem_name, ant, cons, dyn_sys, invar, predicates) = invar_problem

    derivator = dyn_sys.get_derivator()

    new_predicates = set()

    env = get_env()

    if (preds_types & AbsPredsTypes.FACTORS.value):
        add_factors(derivator, invar_problem, new_predicates, env)

    if (preds_types & AbsPredsTypes.PROP.value):
        add_invariants(derivator, invar_problem, new_predicates)

    # Note: to call last --- uses the content of new_predicates
    # to build the Lie derivatives
    if (preds_types & AbsPredsTypes.LIE.value):
        add_lie(derivator, invar_problem, new_predicates)

    return new_predicates

def get_polynomials_invar_problem(invar_problem, preds_types, env):
    (problem_name, ant, cons, dyn_sys, invar, predicates) = invar_problem
    derivator = dyn_sys.get_derivator()

    new_polynomials = set()

    if (preds_types & AbsPredsTypes.FACTORS.value):
        add_factors(derivator, invar_problem, new_polynomials, env)

    predicates = PredicateExtractor.extract_predicates(ant, env)
    for p in predicates:
        new_polynomials.add(get_poly_from_pred(p)[0])

    if (preds_types & AbsPredsTypes.INVAR.value):
        predicates = PredicateExtractor.extract_predicates(invar, env)
        for p in predicates:
            new_polynomials.add(get_poly_from_pred(p)[0])


    if (preds_types & AbsPredsTypes.PROP.value):
        predicates = PredicateExtractor.extract_predicates(cons, env)
        for p in predicates:
            new_polynomials.add(get_poly_from_pred(p)[0])

    # Note: to call last --- uses the content of new_predicates
    # to build the Lie derivatives
    if (preds_types & AbsPredsTypes.LIE.value):
        add_lie(derivator, invar_problem, new_polynomials)

    return new_polynomials


def get_polynomials_ha(ha, ha_prop, preds_types, env):
    # Get the polynomials to use for the abstraction

    pysmt2sympy = Pysmt2Sympy()
    sympy2pysmt = Sympy2Pysmt()

    new_polynomials = set()

    # Get the polynomial of the property
    if (preds_types & AbsPredsTypes.PROP.value):
        prop_predicates = PredicateExtractor.extract_predicates(ha_prop.global_prop, env)

        for loc, loc_prop in ha_prop.prop_by_loc.items():
            loc_prop_preds = PredicateExtractor.extract_predicates(loc_prop, env)
            prop_predicates.update(loc_prop_preds)

        for p in prop_predicates:
            poly = get_poly_from_pred(p)[0]
            if (ha.is_pred_cont(poly)):
                new_polynomials.add(poly)
                if (preds_types & AbsPredsTypes.FACTORS.value):
                    add_poly_factors(pysmt2sympy, sympy2pysmt, poly, new_polynomials)

    # Get the factors of:
    # - the RHS of the ODEs in all the modes
    # - get poly from the invar
    loc_polynomials = set()
    for q,loc in ha._locations.items():
        # Add the polynomials from the RHS of the odes
        if (preds_types & AbsPredsTypes.FACTORS.value):
            derivator = loc.vector_field.get_derivator(pysmt2sympy, sympy2pysmt)

            for v in loc.vector_field.states():
                ode = loc.vector_field.get_ode(v)

                factors = set()
                add_poly_factors(pysmt2sympy, sympy2pysmt, ode, factors)
                loc_polynomials.update(factors)

                # Add the lie derivative for all the predicates
                if (preds_types & AbsPredsTypes.LIE.value):
                    # Add the first derivative
                    for factor in factors:
                        loc_polynomials.add(derivator.get_lie_der(factor))

        # Add the polynomials from the factors of the invariant condition
        if (preds_types & AbsPredsTypes.INVAR.value):
            invar_predicates = PredicateExtractor.extract_predicates(loc.invar, env)
            for predicate in invar_predicates:
                poly = get_poly_from_pred(predicate)[0]
                if (ha.is_pred_cont(poly)):
                    loc_polynomials.add(poly)
                    if (preds_types & AbsPredsTypes.FACTORS.value):
                        add_poly_factors(pysmt2sympy, sympy2pysmt, ode, loc_polynomials)

    new_polynomials.update(loc_polynomials)
    new_polynomials = get_unique_poly_list(new_polynomials)

    return new_polynomials



