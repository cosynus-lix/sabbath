import numpy as np
import sympy as sp
import pysmt
from pysmt.shortcuts import *
from pysmt.typing import REAL
from scipy import io
from collections import namedtuple
import json
from barrier.lyapunov.la_smt import myround
import barrier.system as system

# Maybe we want to do something about these global variables.
THETA = 1
PRECISION = 16


def get_dyn_sys(A, b):
    """
    Construct the dynamical system for der(x) = Ax + b
    """
    states = [Symbol("x_%d" % i, REAL) for i in range(len(A))]

    # dictionary from variable to the ODE right-hand side
    ode_map = {}
    for i in range(len(A)):
        ode_i = Real(0)
        row_i = A[i]
        for j in range(len(row_i)):
            row_i_smt = Real(myround(row_i[j], PRECISION))

            ode_i = ode_i + Times(row_i_smt, states[j])

        ode_map[states[i]] = ode_i + Real(myround(b[i], PRECISION))

    dyn = system.DynSystem(states, [], [], ode_map, {})
    return dyn


def build_dyn_systems_from_hs_file(problem):
    Acs = []
    bs = []
    Cc = []
    
    for index_dyn_system in range(len(problem.ha._locations)):
        (A, b) = get_matrices_from_linear_odes(problem.ha._locations[f"{index_dyn_system}"][1])
        Acs.append(A)
        bs.append(b)
        if index_dyn_system == 0:
            vector_sw_pr_mode0_less0 = get_vector_from_linear_constraint(problem.ha._locations[f"{index_dyn_system}"][0])
    
    dyn_systems = [get_dyn_sys(Acs[0], bs[0]),
                   get_dyn_sys(Acs[1], bs[1])]


    # We get the switching predicate
    switching_predicate_mode0_less0 = get_switching_predicate_from_linear_constraint(problem.ha._locations["0"][0])
    return (dyn_systems, switching_predicate_mode0_less0, vector_sw_pr_mode0_less0) # ,ref_values_smt)

def get_switching_predicate_from_linear_constraint(linear_constraint):
    # Todo, support other node_types
    if linear_constraint.node_type() not in [16,17]:
        raise Exception("Node type not supported. We support < and <= for the moment.")
    return Plus(linear_constraint.arg(0), Times(linear_constraint.arg(1), Real(-1)))

    
def get_vector_from_linear_constraint(linear_constraint):
    # We get symbolic vector from the location invariant when it is linear
    
    
    # Todo, support other node_types
    if linear_constraint.node_type() not in [16,17]:
        raise Exception("Node type not supported. We support < and <= for the moment.")
    
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
    C = sp.zeros(1, num_vars)

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
            C[0,index_coordinate] = sp.sympify(coeff_constraint_this_coord.constant_value()) - Theta
        except:
            raise Exception("Coefficients of the linear constraint are not rationals. Consider approximating them.")

    return (sp.Matrix.hstack(C,sp.Matrix([Theta])))

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