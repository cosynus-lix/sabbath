"""
Utility functions
"""

import logging
from fractions import Fraction
from pysmt.typing import BOOL, REAL, INT
from pysmt.shortcuts import (
    Symbol, TRUE, FALSE,
    Real,
    And,
    LE,
    Real
)

from pysmt.logics import QF_NRA
from pysmt.shortcuts import get_env
from pysmt.exceptions import SolverAPINotFound

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
