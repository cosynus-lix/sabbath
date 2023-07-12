import numpy as np
import sympy as sp
from pysmt.shortcuts import Real
from scipy import io
from collections import namedtuple
import json

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
    return [A,b]