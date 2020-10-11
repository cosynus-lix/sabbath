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
from barrier.lie import Derivator
from barrier.decomposition.utils import get_poly_from_pred



class AbsPredsTypes(Enum):
    """
    Types of predicates to extract from the verification problem
    """
    FACTORS = 1
    LIE = 2
    INVAR = 4


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

def add_invariants(derivator, problem, predicates):
    raise NotImplementedError()


def get_predicates(invar_problem, preds_types):
    (problem_name, ant, cons, dyn_sys, invar, predicates) = invar_problem

    derivator = dyn_sys.get_derivator()

    new_predicates = set()

    env = get_env()

    if (preds_types & AbsPredsTypes.FACTORS.value):
        add_factors(derivator, invar_problem, new_predicates, env)

    if (preds_types & AbsPredsTypes.INVAR.value):
        add_invariants(derivator, invar_problem, new_predicates)

    # Note: to call last --- uses the content of new_predicates
    # to build the Lie derivatives
    if (preds_types & AbsPredsTypes.LIE.value):
        add_lie(derivator, invar_problem, new_predicates)

    return new_predicates

