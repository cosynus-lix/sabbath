""" Compute a Lyapunov function

ASSUMPTIONS - now the functions deal only with systems with equilibrium point in 0 and possibly linear.
Some methods could be easily extended to non-linear (e.g., SOS encodig) and different equilibrium points.

"""

import sympy as sp
import numpy as np


import picos
try:
    from SumOfSquares import SOSProblem
except ImportError:
    def SOSProblem():
        raise Exception("SumOfSquare module not found")

import sys
from fractions import Fraction


import pysmt.typing as types
from pysmt.logics import QF_NRA, NRA, QF_LRA
from pysmt.shortcuts import (
    get_env,
    FreshSymbol, Symbol, REAL, Solver,
    Exists, ForAll,
    Or, NotEquals, And, Implies, Not, Equals,
    GT, LE, GE, TRUE,
    Real,
    Times
)
from pysmt.rewritings import nnf, conjunctive_partition

from barrier.system import DynSystem
from barrier.utils import gen_template, gen_quadratic_template, get_new
from barrier.sympy_utils import make_positive_definite
from barrier.mathematica.mathematica import MathematicaQuantifierEliminator



def synth_lyapunov_sos(get_new, vars_list, coefficients, template, lie, degree):
    prob = SOSProblem()

    # template positive definite
    (p_prime, g_list, E_list, gamma) = make_positive_definite(get_new, prob, template, vars_list)
    # prob.add_sos_constraint(template, vars_list)
    # lie derivative negative semi-definite
    prob.add_sos_constraint(-lie, vars_list)
    # prob.set_objective('max', prob.sym_to_var(coefficients[0]))

    sol = prob.solve()

    if (sol.problemStatus == picos.modeling.solution.PS_FEASIBLE):
        new_template = template
        for s in coefficients:
            c = prob.sym_to_var(s)
            # convert floating point to rationals
            val = round(c.value, 5)
            sympy_value = sp.nsimplify(sp.sympify(val), rational=True)
            #print("%s, %s (%s)" % (s, c, str(c.value)))
            new_template = new_template.subs(s, sympy_value)
        return (True, new_template)
    else:
        # None or False
        return (None, None)


def synth_lyapunov_mathematica(vars_list, coefficients, template, lie):
    lyapunov = Exists(coefficients,
                      ForAll(vars_list,
                             And(Implies( Or([ NotEquals(v, Real(0)) for v in vars_list ]),
                                          GT(template, Real(0))),
                                 LE(lie, Real(0)))))
    lyapunov = ForAll(vars_list,
                      And(Implies( Or([ NotEquals(v, Real(0)) for v in vars_list ]),
                                   GT(template, Real(0))),
                          LE(lie, Real(0))))
    lyapunov = ForAll(vars_list,
                      Implies( Or([ NotEquals(v, Real(0)) for v in vars_list ]),
                                   GT(template, Real(0))),
                      )

    eliminator = MathematicaQuantifierEliminator(get_env(), NRA)
    try:
        res = eliminator.eliminate_quantifiers(lyapunov)
    finally:
        eliminator.exit()


    solver = Solver(logic=QF_NRA, name="z3")
    if solver.is_sat(res):
        coef_map = {}
        for c in coefficients:
            coef_map[c] = solver.get_value(c)
        lyapunov = template.substitute(coef_map)

        return (True, lyapunov)
    else:
        return (False, None)




def synth_linear_lyapunov_smt(vars_list, coefficients, l, derivative, max_iter = -1):
    # find a quadratic lyapunov function for the linear system
    # L(X) = X^T P X
    # P = P^T, and P > 0 (means forall x. x != 0 => x^T P x > 0)
    #
    # Then forall x. d(L(X)) < 0
    #
    # From Automated and Sound Synthesis of Lyapunov Functions with SMT Solvers,
    # Abate et al, TACAS 2020

    DEBUG = False

    # (x != 0 -> L(X) > 0) & d(L(X)) <= 0 & 
    condition = And(Implies(Or([ NotEquals(v, Real(0)) for v in vars_list  ] ),
                            GT(l, Real(0))),
                    LE(derivative, Real(0)))

    iteration = 0

    learner = Solver(logic=QF_LRA, name="z3")
    verifier = Solver(logic=QF_NRA, name="z3")


    to_subs = {}
    for c in vars_list:
        to_subs[c] = Real(0)

    condition_blocking = condition
    while (max_iter < 0 or iteration < max_iter):
        if DEBUG: print("Iteration %d..." % iteration)
        if DEBUG: print("Lyapunov condition", condition_blocking.serialize())

        if (learner.is_sat(condition_blocking)):
            to_subs = {}
            blocking = TRUE()
            for c in coefficients:
                c_value = learner.get_value(c)
                to_subs[c] = c_value
                blocking = And(blocking, Equals(c, c_value))
            blocking = Not(blocking)

            to_check = condition.substitute(to_subs)

            # print("Verifier", to_check.serialize())
            if (verifier.is_valid(to_check)):
                lyapunov = l.substitute(to_subs)
                return (True, lyapunov)
            else:
                condition_blocking = And(condition_blocking, blocking)

                to_subs = {}
                for c in vars_list:
                    c_value = verifier.get_value(c)
                    to_subs[c] = c_value

                if DEBUG: print(to_subs)
                to_hold = condition.substitute(to_subs)

                if DEBUG: print(to_hold.serialize())
                if DEBUG: print(learner.is_sat(to_hold))

                condition_blocking = And(condition_blocking, to_hold)


        else:
            print("Learner unsat")
            return (False, None)
        iteration = iteration + 1

    print("Unknown")
    return (None, None)


def synth_lyapunov(dyn_sys, degree, use_mathematica=False, use_smt = False, max_iter=-1):
    """
    Entry point for synthesising different lyapunov function for dynamical systems

    """
    assert not (use_smt and use_mathematica)

    vars_list = [s for s in dyn_sys.states()]

    if (use_smt and degree == 2):
        (template, coefficients) = gen_quadratic_template(vars_list)
    else:
        (template, coefficients) = gen_template(dyn_sys, degree)

    # x1, x2, a, b = Symbol("x1", REAL), Symbol("x2", REAL), Symbol("a", REAL), Symbol("b", REAL)
    # template = a * x1 * x1 + b * x2 * x2
    # coefficients = [a,b]

    derivator = dyn_sys.get_derivator()
    template_derivative = derivator.get_lie_der(template)

    if use_mathematica:
        (res, lyapunov) = synth_lyapunov_mathematica(vars_list,
                                                     coefficients,
                                                     template,
                                                     template_derivative)
    elif use_smt:
        assert (dyn_sys.is_linear())
        (res, lyapunov) = synth_linear_lyapunov_smt(vars_list, coefficients,
                                                    template, template_derivative,
                                                    max_iter)
    else:
        get_new_inst = lambda : get_new(derivator)

        (res, lyapunov) = synth_lyapunov_sos(
            get_new_inst,
            [derivator._get_sympy_expr(v) for v in dyn_sys.states()],
            [derivator._get_sympy_expr(v) for v in coefficients],
            derivator._get_sympy_expr(template),
            derivator._get_sympy_expr(template_derivative),
            degree)
        if not lyapunov is None:
            lyapunov = derivator._get_pysmt_expr(lyapunov)

    return (res, lyapunov)


def validate_lyapunov(sys, lyapunov):
    """ Use smt to validate that lyapunov is a lyapunov function """
    solver = Solver(logic=QF_NRA, name="z3")

    # lyapunov must be positive (apart in the equilibrium point?)
    if (not solver.is_valid(Implies (Or([ NotEquals(v, Real(0)) for v in sys.states() ] ),
                                     GT(lyapunov, Real(0))) )):
        print("The lyapunov function is NOT positive")
        return False
    elif (not solver.is_valid( LE(sys.get_derivator().get_lie_der(lyapunov), Real(0)) )):
        print("The lyapunov function is not non-negative")
        return False

    return True


def get_sympy_matrix(derivator, equations, variables):
    sympy_equations = [derivator._get_sympy_expr(expr) for expr in equations]
    sympy_variables = [dervivator._get_sympy_expr(var) for var in variables]

    sys = sp.linear_eq_to_matrix(sympy_equations, sympy_variables)

    return sys

def synth_exp_lyapunov_values(s1, s2, alpha = None):
    """ Ad-hoc function for values """

    # Get only linear systems (not affine)
    s1_scaled = s1.get_rescaled_by_equilibrium_point()
    s2_lin = s2.remove_affine_terms()
    s2_lin._derivator = s1_scaled.get_derivator()

    A1 = get_sympy_matrix(s1_scaled.get_derivator(),
                          [ode for ode in s1_scaled.get_odes()],
                          [s for s in s1_scaled.get_states()])
    A2 = get_sympy_matrix(s2_lin.get_derivator(),
                          [ode for ode in s2_lin.get_odes()],
                          [s for s in s2_lin.get_states()])

    if (alpha is None):
        alpha = picos.Constant('alpha', [1])
    else:
        alpha = picos.Constant('alpha', [alpha])

    # The quadratic Lyapunov function is of the form V(X) = x^T P x with P a n x n matrix.
    # P must be positive definite (to ensure V(x) > 0 when x != 0, and V(0) = 0,
    sdp = picos.Problem()
    s1_dim = len(s1_scaled.get_states())
    s2_dim = len(s2_lin.get_states())

    assert(s1_dim + 1 == s2_dim)

    P = pic.SymmetricVariable('P', (s1_dim,s1_dim))
    sdp.add_constraint(P >> 0)

    # PA1 + A1^TP + alpha P << 0
    sdp.add_constraint(P * A1 + A1.T * P + alpha * P << 0)

    # P'A2 + A2^TP' + alpha P' << 0
    # P' = | P     b2 |
    #      | b2^T  c  |
    b2 = picos.RealVariable('b2', (s1_dim,1))
    c = pic.SymmetricVariable('c', 1)
    P2 = ((P // b2.T).T // (b2 // c).T).T
    sdp.add_constraint(P2 * A2 + A2.T * P2 + alpha * P2 << 0)


    solution = sdp.solve(solver='cvxopt',verbosity=False)

    if (sol.problemStatus == picos.modeling.solution.PS_FEASIBLE):
        # # Construct the alyapunov function, x^T P x
        # lyapunov = Real(0)
        # state_vars = [v in dynamical_systems[0].get_states()]
        # for row_index in range(len(state_vars))
        #     row_sum = Real(0)
        #     for column_index in columns:
        #         val_from_picos = P[row_index * len(state_vars), column_index]

        #         # Back to pysmt
        #         val_from_picos = Real(val_from_picos)

        #         row_sum = row_sum + Times(state_vars[column_index],
        #                                   val_from_picos)
        #     row_product = Times(state_vars[row_index], row_sum)

        #     lyapunov += lyapunov + row_product

        return (True, lyapunov)
    else:
        return (False, None)


    return lyapunov



def synth_common_lyapunov_for_AGS(dynamical_systems, alpha=None):
    """
    Input: a switched linear system, represented as a list of dynamical system.
    Note: no partitions as input, prove AGS

    der(x) = A1 x   for x in P1
    ...
    der(x) = Ak x   for x in Pk

    Assume the systems are defined over the same state variables.

    alpha > 0

    Compute a common quadratic lyapunov function for asymptotic global stability using a SDP solver (the Lyapunov function synthesis is a LMI).

    Returns (
    """

    assert len(dynamical_systems) > 0
    assert (len(dynamical_systems) == len(partitions))


    # Transform the dynamical systems, if one of them is affine.
    sdp = picos.Problem()

    # The quadratic Lyapunov function is of the form V(X) = x^T P x with P a n x n matrix.
    # P must be positive definite (to ensure V(x) > 0 when x != 0, and V(0) = 0,
    P = pic.SymmetricVariable('P', (2,2))
    sdp.add_constraint(P >> 0)

    if alpha is None:
        # Cannot search for alpha
        assert (False)
    else:
        assert (alpha > 0)

    """ For each system der(x) = A1 x, generate the constraints:
        PA + A^TP + alpha P << 0
    """
    for sys in dynamical_systems:
        sys_matrix = get_sympy_matrix(sys.get_derivator(),
                                      [ode for ode in sys.get_odes()],
                                      [s for s in sys.get_states()])

        # 

    solution = sdp.solve(solver='cvxopt',verbosity=False)

    if (sol.problemStatus == picos.modeling.solution.PS_FEASIBLE):
        # Construct the lyapunov function, x^T P x
        lyapunov = Real(0)
        state_vars = [v in dynamical_systems[0].get_states()]
        for row_index in range(len(state_vars))
            row_sum = Real(0)
            for column_index in columns:
                val_from_picos = P[row_index * len(state_vars), column_index]

                # Back to pysmt
                val_from_picos = Real(val_from_picos)

                row_sum = row_sum + Times(state_vars[column_index],
                                          val_from_picos)
            row_product = Times(state_vars[row_index], row_sum)

            lyapunov += lyapunov + row_product

        return (True, lyapunov)
    else:
        return (False, None)
