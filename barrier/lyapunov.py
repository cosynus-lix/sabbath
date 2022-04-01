""" Compute a Lyapunov function
"""

import sympy as sp
import numpy as np


try:
    from SumOfSquares import SOSProblem
except ImportError:
    def SOSProblem():
        raise Exception("SumOfSquare module not found")

from sympy.polys.monomials import itermonomials
import picos

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
from barrier.mathematica.mathematica import MathematicaQuantifierEliminator



def get_new(derivator):
    new_symb = FreshSymbol(types.REAL)
    return derivator._get_sympy_expr(new_symb)


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



def gen_quadratic_template(vars_list):
    def get(m,i,j):
        if j > i:
            return (m[j])[i]
        else:
            return (m[i])[j]

    coefficients = []
    p_matrix = []
    for i in range(len(vars_list)):
        row = []
        for j in range(i+1):
            c = FreshSymbol(types.REAL, template="lyap_temp_%d")
            coefficients.append(c)
            row.append(c)
        p_matrix.append(row)


    app = []
    for i in range(len(vars_list)):
        e1 = Real(0)
        for j in range(len(vars_list)):
            e1 = e1 + Times(vars_list[j], get(p_matrix, j, i))
        app.append(e1)

    e1 = Real(0)
    for j in range(len(vars_list)):
      e1 = e1 + app[j] * vars_list[j]

    return (e1, coefficients)


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




def gen_template_sympy(get_new, vars_list, degree, min_degree):
    coefficients = []
    template = 0

    for l in itermonomials(vars_list, degree, min_degree):
        coeff = get_new()
        template = template + coeff * l
        coefficients.append(coeff)
    return (template, coefficients)


def gen_template(dyn_sys, degree, min_degree=1):
    """
    Generates a template up to the given degree (starting from 1) for the given
    list of variables.

    E.g.:
    Input: vars_list = [x,y], degree = 2
    Output: c1 x^2 + c2 y^2 + c3 x y + c4 x + c5 y
    with coefficient map: {x^2 : c1, y^2 : c2, x y : c3, x : c4, y : c5}
    """

    derivator = dyn_sys.get_derivator()
    get_new_inst = lambda : get_new(derivator)

    (sympy_template, sympy_coeff) = gen_template_sympy(get_new_inst,
                                                       [derivator._get_sympy_expr(v) for v in dyn_sys.states()],
                                                       degree, min_degree)

    return (derivator._get_pysmt_expr(sympy_template),
            [derivator._get_pysmt_expr(c) for c in sympy_coeff])





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



def synth_barrier_sos(get_new, vars_list,
                      barrier_template,
                      coefficients,
                      init_preds,
                      bad_preds,
                      barrier_lie,
                      degree,
                      _lambda = 0,
                      eps = 0.001):
    """
    We use the exponential condition for the dynamical system

    Kong, Hui, et al. "Exponential-condition-based barrier certificate generation for safety verification of hybrid systems." CAV 2013
    """
    # Generate a barrier certificate
    prob = SOSProblem()

    assert (_lambda <= 0 and _lambda >= -1)

    # barrier <= on initial states
    # - barrier - sum_{i \in Init}{poly * i} >= 0
    init_condition = - barrier_template
    for init in init_preds:
        IP_init, coefficients_init = gen_template_sympy(get_new, vars_list, degree, 0)
        prob.add_sos_constraint(IP_init, vars_list)
        init_condition = init_condition -(IP_init * init) 
    prob.add_sos_constraint(init_condition, vars_list)

    # barrier > 0 on bad states
    # barrier - sum_{b \in Bad}{poly * b} - epsilon >= 0
    bad_condition = barrier_template - eps
    for bad in bad_preds:
        IP_bad, coefficients_bad = gen_template_sympy(get_new, vars_list, degree, 0)
        prob.add_sos_constraint(IP_bad, vars_list)
        bad_condition = bad_condition - IP_bad * bad
    prob.add_sos_constraint(bad_condition, vars_list)

    # the lie derivative of the barrier always decreases
    # lambda * barrier - barrier' >= 0
    lie_condition = _lambda * barrier_template - barrier_lie
    prob.add_sos_constraint(lie_condition, vars_list)

    sol = prob.solve(primals=None)

    if (sol.problemStatus == picos.modeling.solution.PS_FEASIBLE):
        new_template = barrier_template
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
        return (False, None)



def synth_barrier(dyn_sys, init, bad, degree):
    def process_f(f):
        """
        Assume f is a conjunction of predicates p >= 0.

        Raise an exception if that's not the case, transform the predicate
        and returns a list of predicates p >=0 otherwise
        """

        epsilon = 0.0001
        acc = []
        for p in conjunctive_partition(f):
            if p.is_le():
                polynomial = p.args()[1] - p.args()[0]
                acc.append(polynomial)
            elif p.is_lt():
                # arbitrary epsilon
                polynomial = p.args()[1] - p.args()[0] - epsilon
                acc.append(polynomial)
            elif p.is_equals():
                acc.append(p.args()[1] - p.args()[0])
                acc.append(p.args()[0] - p.args()[1])
            else:
                raise Exception("Unexpected operator in %s" % str(p))

        return acc

    vars_list = [s for s in dyn_sys.states()]

    (barrier_template, coefficients) = gen_template(dyn_sys, degree)
    derivator = dyn_sys.get_derivator()
    barrier_derivative = derivator.get_lie_der(barrier_template)

    get_new_inst = lambda : get_new(derivator)


    # preprocess init and bad
    # we assume init and bad to be a conjunction of predicates P >= 0
    init_pred = process_f(nnf(init))
    bad_pred = process_f(nnf(bad))

    (res, barrier) = synth_barrier_sos(
        get_new_inst,
        [derivator._get_sympy_expr(v) for v in dyn_sys.states()],
        derivator._get_sympy_expr(barrier_template),
        [derivator._get_sympy_expr(v) for v in coefficients],
        [derivator._get_sympy_expr(i) for i in init_pred],
        [derivator._get_sympy_expr(b) for b in bad_pred],
        derivator._get_sympy_expr(barrier_derivative),
        degree
    )

    if not barrier is None:
        barrier = derivator._get_pysmt_expr(barrier)

    return (res, barrier)
