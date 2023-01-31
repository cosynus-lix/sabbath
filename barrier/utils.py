"""
Utility functions
"""

import logging

from fractions import Fraction
from pysmt.typing import BOOL, REAL, INT

from pysmt.shortcuts import (
    Symbol, TRUE, FALSE, FreshSymbol,
    Real,
    And,
    LE,
    Real,
    get_env,
    Times
)

from pysmt.logics import QF_NRA
from pysmt.exceptions import SolverAPINotFound

from barrier.sympy_utils import gen_template_sympy

import traceback

def get_range(var_list, range_matrix):
    """
    Generates a box constraints.
    """

    var_range = TRUE()

    assert(len(range_matrix) == len(var_list))

    for i in range(len(var_list)):
        assert(2 == len(range_matrix[i]))

        var = var_list[i]
        lower = range_matrix[i][0]
        upper = range_matrix[i][1]

        var_range = And(var_range,
                        And(LE(lower, var),
                            LE(var, upper)))

    return var_range


def get_range_from_int(var_list, range_matrix):
    """
    Generates a box constraints.
    """

    new_range_matrix = []

    for m in range_matrix:
        (lower, upper) = m
        # Throw exception if not integers
        lower = int(lower)
        upper = int(upper)
        new_range_matrix.append((Real(Fraction(lower,1)),
                                 Real(Fraction(upper,1))))

    return get_range(var_list, new_range_matrix)

def get_mathsat_smtlib(env = get_env()):
    """
    Get the mathsat SMT lib solver
    """

    name = "mathsat-smtlib"
    logics = [QF_NRA]
    try:
        if not env.factory.is_generic_solver(name):
            from shutil import which
            mathsat_path = which("mathsat")

            if mathsat_path is None:
                logging.debug("Mathsat path not found!")
            else:
                logging.debug("Mathsat path: %s" % mathsat_path)
                env.factory.add_generic_solver(name, mathsat_path, logics)

        solver = env.factory.Solver(name=name, logic=logics[0])
    except:
        raise SolverAPINotFound

    return solver

def get_cvc5_smtlib(env = get_env()):
    """
    Get the mathsat SMT lib solver
    """

    name = "cvc5-smtlib"
    logics = [QF_NRA]
    try:
        if not env.factory.is_generic_solver(name):
            from shutil import which
            solver_path = which("cvc5")

            if solver_path is None:
                logging.debug("CVC5 path not found!")
            else:
                logging.debug("CVC5 path: %s" % solver_path)
                env.factory.add_generic_solver(name, [solver_path,"--incremental","--lang=smtlib","--print-success","--output-lang=smtlib","--produce-models"], logics)


        solver = env.factory.Solver(name=name, logic=logics[0],
                                    solver_options={'debug_interaction':False})
    except:
        raise SolverAPINotFound

    return solver

def get_dreal_smtlib(env = get_env()):
    """
    Get the dreal SMT lib solver
    """

    name = "dreal-smtlib"
    logics = [QF_NRA]
    try:
        if not env.factory.is_generic_solver(name):
            from shutil import which
            solver_path = which("dreal")

            if solver_path is None:
                logging.debug("dreal path not found!")
                print("Patg is none")
            else:
                print("Path found " + solver_path)
                logging.debug("dreal path: %s" % solver_path)

                args = [
                    solver_path,
                    "--in",
                    "--format smt2",
                    "--smtlib2-compliant",
                    "--produce-models",
                ]

                print("Adding solver")
                env.factory.add_generic_solver(name,
                                               args,
                                               logics)

                print("Added solver, calling factory")
        solver = env.factory.Solver(name=name, logic=logics[0])
    except Exception as err:
        print(err)
        print(type(err))
        raise SolverAPINotFound

    return solver


def get_new(derivator):
    new_symb = FreshSymbol(REAL)
    return derivator._get_sympy_expr(new_symb)


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
            c = FreshSymbol(REAL, template="lyap_temp_%d")
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



