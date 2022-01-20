import sympy as sp
import numpy as np
from SumOfSquares import SOSProblem, poly_opt_prob
from sympy.polys.monomials import itermonomials
import picos

import sys
from fractions import Fraction


import pysmt.typing as types
from pysmt.logics import QF_NRA, NRA
from pysmt.shortcuts import (
    get_env,
    FreshSymbol, Symbol, REAL, Solver,
    Exists, ForAll,
    Or, NotEquals, And, Implies,
    GT, LE,
    Real
)

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


def synth_lyapunov_sympy(get_new, vars_list, coefficients, template, lie, degree):
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
            sympy_value = sp.nsimplify(sp.sympify(c.value), rational=True)
            #print("%s, %s (%s)" % (s, c, str(c.value)))
            new_template = new_template.subs(s, sympy_value)
        return (True, new_template)
    else:
        return (False, None)


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

    print(lyapunov.serialize())
    print(res.serialize())


    solver = Solver(logic=QF_NRA, name="z3")
    if solver.is_sat(res):
        coef_map = {}
        for c in coefficients:
            coef_map[c] = solver.get_value(c)
        lyapunov = template.substitute(coef_map)

        print(coef_map)
        print(template)

        return (True, lyapunov)
    else:
        return (False, None)



def gen_template(dyn_sys, degree, min_degree=1):
    """
    Generates a template up to the given degree (starting from 1) for the given
    list of variables.

    E.g.:
    Input: vars_list = [x,y], degree = 2
    Output: c1 x^2 + c2 y^2 + c3 x y + c4 x + c5 y
    with coefficient map: {x^2 : c1, y^2 : c2, x y : c3, x : c4, y : c5}
    """

    def gen_template_sympy(get_new, vars_list, degree, min_degree):
        #coefficients = {}
        coefficients = []
        template = 0

        for l in itermonomials(vars_list, degree, min_degree):
            coeff = get_new()
            template = template + coeff * l
            # coefficients[l] = coeff
            coefficients.append(coeff)
        return (template, coefficients)

    derivator = dyn_sys.get_derivator()
    get_new_inst = lambda : get_new(derivator)

    (sympy_template, sympy_coeff) = gen_template_sympy(get_new_inst,
                                                       [derivator._get_sympy_expr(v) for v in dyn_sys.states()],
                                                       degree, min_degree)

    return (derivator._get_pysmt_expr(sympy_template),
            [derivator._get_pysmt_expr(c) for c in sympy_coeff])





def synth_lyapunov(dyn_sys, degree, use_mathematica=False):
    (template, coefficients) = gen_template(dyn_sys, degree)

    # x1, x2, a, b = Symbol("x1", REAL), Symbol("x2", REAL), Symbol("a", REAL), Symbol("b", REAL)
    # template = a * x1 * x1 + b * x2 * x2
    # coefficients = [a,b]

    derivator = dyn_sys.get_derivator()
    template_derivative = derivator.get_lie_der(template)

    if (not use_mathematica):
        get_new_inst = lambda : get_new(derivator)

        (res, lyapunov) = synth_lyapunov_sympy(
            get_new_inst,
            [derivator._get_sympy_expr(v) for v in dyn_sys.states()],
            [derivator._get_sympy_expr(v) for v in coefficients],
            derivator._get_sympy_expr(template),
            derivator._get_sympy_expr(template_derivative),
            degree)
        if not lyapunov is None:
            lyapunov = derivator._get_pysmt_expr(lyapunov)
    else:
        (res, lyapunov) = synth_lyapunov_mathematica([s for s in dyn_sys.states()],
                                                     coefficients,
                                                     template,
                                                     template_derivative)

    print(lyapunov)
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


def main():
    # x1,x2,x3,x4 = sp.symbols('x1 x2 x3 x4')
    # vars_list = [x1,x2,x3,x4]

    # vector_field = {
    #     x1 : -x1 + x2**3 - 3*x3*x4,
    #     x2 : -x1 - x2**3,
    #     x3 : x1 * x4 - x3,
    #     x4 : x1 * x3 - x4**4
    # }
    # feasible, lyap = test_lyapunov(factory, vector_field, vars_list, 4)
    # print(feasible, lyap)

    x1, x2 = [Symbol("x%s" % (i+1), REAL) for i in range(2)]

    sys = DynSystem([x1,x2], [], [],
                    {
                        x1 : -x1,
                        x2 : x1 - x2
                    },
                    {})

    (res, lyapunov) = synth_lyapunov(sys, 2)

    if (res):
        print("Found a Lyapunov function")
        print(lyapunov)

        is_valid = validate_lyapunov(sys, lyapunov)
        print("Is valid: ", is_valid)
    else:
        print("No Lyapunov function")


if __name__ == "__main__":
    main()
