import numpy as np
import sympy as sp
from pysmt.shortcuts import *


def get_switching_predicate_from_linear_constraint(linear_constraint):
    if linear_constraint.is_lt() or linear_constraint.is_le():
        return Plus(linear_constraint.arg(0), Times(linear_constraint.arg(1), Real(-1)))
    else:
        raise Exception("Node type not recognized. We should support <, <=, > and >=.")

def get_vector_from_linear_constraint(linear_constraint):
    # We get symbolic vector from the location invariant when it is linear

    if (not (linear_constraint.is_lt() or linear_constraint.is_le())):
        raise Exception("Unsupported constraint for ", linear_constraint)

    # We start getting Theta
    linear_part = Plus(linear_constraint.arg(0), Times(linear_constraint.arg(1), Real(-1)))
    num_vars = len(linear_constraint.get_free_variables())

    substitution_dictionary = {}
    for var in  linear_part.get_free_variables():
        substitution_dictionary[var]=Real(0)
    lin_part_all_zero = linear_part.substitute(substitution_dictionary).simplify()
    try:
        Theta = sp.sympify(lin_part_all_zero.constant_value())
    except:
        raise Exception("Coefficients of the constraint system are not rationals. Consider approximating them.")

    # Now we get C
    C = np.zeros([1, num_vars])

    for index_coordinate in range (num_vars):
        substitution_dictionary = {}
        ind_check_same_coord = 0
        for var in linear_part.get_free_variables():
            if ind_check_same_coord == index_coordinate:
                substitution_dictionary[var]=Real(1)
            else:
                substitution_dictionary[var]=Real(0)
            ind_check_same_coord += 1
        coeff_constraint_this_coord = linear_part.substitute(substitution_dictionary).simplify()
        try:
            C[0][index_coordinate] = sp.sympify(coeff_constraint_this_coord.constant_value())
        except:
            raise Exception("Coefficients of the linear constraint are not rationals. Consider approximating them.")

    return (np.asarray(C), Theta)

def get_matrices_from_linear_odes(dyn_sys):
    # We get symbolic matrices from the ODEs system when it is linear
    num_vars = len(dyn_sys.get_odes())
    A = sp.zeros(num_vars, num_vars)
    b = sp.zeros(num_vars, 1)
    index_ode = 0

    for coordinate_ode in dyn_sys.get_odes().values():
        substitution_dictionary = {}
        for var in  coordinate_ode.get_free_variables():
            substitution_dictionary[var]=Real(0)
        coeff_ode_all_zero = coordinate_ode.substitute(substitution_dictionary).simplify()
        try:
            b[index_ode] = sp.sympify(coeff_ode_all_zero.constant_value())
        except:
            raise Exception("Coefficients of the linear system are not rationals. Consider approximating them.")
        for index_coordinate in range (num_vars):
            substitution_dictionary = {}
            ind_check_same_coord = 0
            for var in coordinate_ode.get_free_variables():
                if ind_check_same_coord == index_coordinate:
                    substitution_dictionary[var]=Real(1)
                else:
                    substitution_dictionary[var]=Real(0)
                ind_check_same_coord += 1
            coeff_ode_this_coord = coordinate_ode.substitute(substitution_dictionary).simplify()
            try:
                A[index_ode, index_coordinate] = sp.sympify(coeff_ode_this_coord.constant_value()) - b[index_ode]
            except:
                raise Exception("Coefficients of the linear system are not rationals. Consider approximating them.")
        index_ode += 1
    return (np.asarray(A), np.asarray(b))
