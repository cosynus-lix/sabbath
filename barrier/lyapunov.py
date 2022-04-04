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
from barrier.mathematica.mathematica import MathematicaQuantifierEliminator


def make_positive_definite(get_new, prob, p, vars_list):
    def _make_positive_definite(get_new, p, vars_list):
        """
        Takes as input a polynomial p of degree 2*d and returns:
        1. the polynomial p' := p - f

        where f is a new polynomial: sum_{i = 1}^{n} sum_{j = 1}^{d} e_ij xi^2j
        with e_ij a list of new coefficients

        2. the list of polynomials g := [sum_{j = 1}^{d} e_1j - gamma, ..., sum_{j = 1}^{d} e_nj - gamma]
        Each sum "sum_{j = 1}^{d} e_nj - gamma" must be positive

        3. The list of coefficients E := [...eij...]
        All coefficients must be non-negative

        4. The coefficient gamma
        Gamma must be positive
        """

        p_degreee = sp.Poly(p, vars_list).total_degree()
        if (p_degreee % 2 != 0):
            raise Exception("Polynomial degree should be divisible by 2")
        p_degreee = int(p_degreee)
        degree = int(p_degreee / 2)


        # Generate the new polynomial, E, and the constraints on E
        E_list = []
        g_list = []
        gamma = get_new()

        f = 0
        for v in vars_list:
            c_v = 0
            for j in range(degree):
                j += 1

                e = get_new()
                E_list.append(e)

                f += e * (v**(2*j))
                c_v += e
            c_v = c_v - gamma
            g_list.append(c_v)
        p_prime = p - f

        return (p_prime, g_list, E_list, gamma)

    (p_prime, g_list, E_list, gamma) = _make_positive_definite(get_new, p, vars_list)

    prob.add_sos_constraint(p_prime, vars_list)
    for g in g_list:
        prob.add_sos_constraint(g, vars_list)
    for e in E_list:
        prob.add_sos_constraint(e, vars_list)
    prob.add_sos_constraint(gamma, vars_list)

    return (p_prime, g_list, E_list, gamma)


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



