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
PRECISION = 10


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

    for dyn_sys in problem.ha._locations.values():
        (A, b) = get_matrices_from_linear_odes(dyn_sys.vector_field)
        Acs.append(A)
        bs.append(b)
    
    # Get Cc in some way
    
    dyn_systems = [get_dyn_sys(Acs[0], bs[0]),
                   get_dyn_sys(Acs[1], bs[1])]

    Theta_smt = Real(myround(THETA, PRECISION))

    ### OLD CODE, DO WE NEED IT?
    # y0 = get_y0(dyn_systems[0], Cc)
    # refvalues_smt = to_smt_vect(refs, PRECISION)

    # verify_po_logger.info("Reference values: %s" % str(refvalues_smt))

    # r0 = refvalues_smt[0]

    # r0 - y0 - Theta
    # switching_predicate = r0 - y0 - Theta_smt
    ###

    # We get the switching predicate
    # switching_predicate = get_switching_predicate_from_linear_odes(problem)
    switching_predicate ="TODO"
    
    # Do something to give this line a sense:
    # config = Config(new_solver_f)
    config = "TODO"

    return (config, dyn_systems, switching_predicate, Theta_smt) # ,ref_values_smt)


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
            raise Exception("Coefficient of the linear system are not rationals. Consider approximating them.")
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
                raise Exception("Coefficient of the linear system are not rationals. Consider approximating them.")
        index_ode += 1
    return (np.asarray(A), np.asarray(b))