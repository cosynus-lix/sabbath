import logging
logging.basicConfig(level=logging.CRITICAL)
stability_hs_logger = logging.getLogger(__name__)


import numpy as np
from scipy import io, linalg
import picos as pc
from copy import deepcopy
np.set_printoptions(precision=5, linewidth=1000)

""" Utility functions for linear algebra.
"""

from fractions import Fraction
from pysmt.typing import REAL
from pysmt.logics import QF_NRA
from pysmt.shortcuts import (
  TRUE, Real, Symbol,
  Implies, And, Or, Not,
  Solver, simplify,
  Times, Minus,
  GE, LE, LT, GT, Equals,
  substitute
)
import fractions

import sympy as sp

from .la_smt import *

#LUDO: do I need an empty class for PQ functions???
def _check_implication_full(solver, smt_vars, implication, print_model=False):
  """
  Check if an implication is valid, printing counterexample for debug if it's not.
  """
  solver.reset_assertions()
  solver.add_assertion(Not(implication))
  if (solver.solve()):
    if not print_model:
      return False
    model = solver.get_model()

    def get_le_val(le):
      assert(le.is_le())
      return Minus(le.args()[0], le.args()[1])

    def get_lt_val(le):
      assert(le.is_lt())
      return Minus(le.args()[0], le.args()[1])

    def get_float_val_model(model, exp):
      smt_val = model.get_value(exp)
      float_val = float(fractions.Fraction(smt_val.serialize()))
      return float_val

    def get_float_val_le(model, exp):
      return get_float_val_model(model, get_le_val(exp))

    def get_float_val_lt(model, exp):
      return get_float_val_model(model, get_lt_val(exp))


    implicant = implication.args()[0].simplify()
    consequent = implication.args()[1].simplify()

#    print("Model = ", ", ".join(["%s = %s" % (str(v),get_float_val_model(model, v)) for v in smt_vars]))

    def _print_vals(formula):
      stack = [formula]
      while (len(stack) > 0):
        f = stack.pop()
        if f.is_and():
          for a in f.args():
            stack.append(a)
        elif f.is_le():
          print(f, " := ", get_float_val_le(model, f), " <= 0")
        elif f.is_lt():
          print(f, " := ", get_float_val_lt(model, f), " < 0")
        else:
          print(f, " = ", model.get_value(f))

    _print_vals(implicant)
    _print_vals(consequent)
    return False
  else:
    return True

class Piecewise_Quadratic_Function():
    """
    A piecewise quadratic function.
    We consider 2 modes and one invariant.
    """
    def __init__(self):
        # These are the matrices that describe the PQ function. In mode0 we have
        # the function [x; 1]^t * self.matrices[0] * [x;1].
        self.matrices = {}
        

        # This is the vector that describes mode0. A vector x is in mode0 iff
        # self.vector_sw_pr_mode0_less0 * [x;1] < 0.
        self.vector_sw_pr_mode0_less0 = None
        # This is the smt predicate that describes mode0. A vector x is in mode0 iff
        # self.sw_pr_mode0_less0(x) < 0.
        self.sw_pr_mode0_less0 = None

    def _build_smt_function(self, smt_vars, index_mode):
        """
        [x 1]^T P[index_mode] [x 1]
        """
        P = self.matrices[index_mode]
        assert len(smt_vars) == sp.shape(P)[0]

        smt_vars_app = [v for v in smt_vars]
        smt_vars_app[len(smt_vars_app)-1] = Real(1)

        smt_matrix = from_sympy_to_smt_matrix(P)
        app = vect_times_matrix(smt_vars_app, smt_matrix)
        # [x 1]^T P [x 1]
        V_m = dot_product_smt(app, smt_vars_app)

        return V_m
    
    def serialize_mat(self, filename):
        from scipy.io import savemat
        data = {
            "LF0" : self.matrices[0],
            "LF1" : self.matrices[1],
            "vector_sw_pr_mode0_less0" : self.vector_sw_pr_mode0_less0
        }

        savemat(filename, data)

def get_piecewise_lyapunov_ludo(dyn_systems, vector_sw_pr_mode0_less0, certify = 'smt', normalize = False, sdp_solver = 'cvxopt'):
    # We get the piecewise Lyapunov for the system.
    As = []
    bs = []
    for system in dyn_systems:
        (A,b) = system.get_odes_matrix_and_vector()
        As.append(sp.Matrix(A))
        bs.append(sp.Matrix(b))
    n = sp.shape(As[0])[0] + 1
    stable_0 = As[0].solve( -bs[0], "LU")
    translation = sp.Matrix.vstack(
        sp.Matrix.hstack(sp.eye(n-1), -stable_0),
        sp.Matrix.hstack(sp.zeros(1,n-1), sp.Matrix([[1]])))
    translationinv = translation.inv()

    A1bar_old = augment_sp(As[0])
    A2bar_old = augment_sp(As[1])

    L1 = sp.Matrix(A1bar_old)
    L1[0:n-1, n-1] = bs[0]
    A1bar_old = sp.Matrix(L1)

    L2 = sp.Matrix(A2bar_old)
    L2[0:n-1, n-1] = bs[1]
    A2bar_old = sp.Matrix(L2)
    
    A1bar = translation @ A1bar_old @ (translationinv)
    A2bar = translation @ A2bar_old @ (translationinv)
    
    #Here we build matrices that we need to describe the sdp problem.
    # Ibar = sp.Matrix.vstack(
    #     sp.Matrix.hstack(sp.eye(n-1), sp.zeros(n-1,1)),
    #     sp.zeros(1,n)
    # )

    # matrices describing the mode 1/2 regions
    vector_sw_pr_mode0_geq0 = - vector_sw_pr_mode0_less0

    QQ1A = sp.Matrix.vstack(
        sp.Matrix.hstack(sp.Matrix.zeros(n-1,n-1), (sp.Matrix(vector_sw_pr_mode0_geq0[:-1])/2)),
        sp.Matrix.hstack(sp.Matrix(vector_sw_pr_mode0_geq0[:-1]).transpose()/2, 
                         sp.Matrix([vector_sw_pr_mode0_geq0[-1]]))
    )
    QQ1 = translationinv.transpose() @ QQ1A @ translationinv
    QQ2A = sp.Matrix.vstack(
        sp.Matrix.hstack(sp.Matrix.zeros(n-1,n-1), -(sp.Matrix(vector_sw_pr_mode0_geq0[:-1])/2)),
        sp.Matrix.hstack(-sp.Matrix(vector_sw_pr_mode0_geq0[:-1]).transpose()/2, 
                         -sp.Matrix([vector_sw_pr_mode0_geq0[-1]]))
    )
    QQ2 = translationinv.transpose() @ QQ2A @ translationinv

    cd = sp.Matrix.hstack(QQ1[-1,:-1]*2, sp.Matrix([QQ1[-1,-1]]))
    Qcd = []
    for num_var in range(n):
        Qcd.append( can_vec_sp(num_var+1, n) @ cd + (can_vec_sp(num_var+1, n) @ cd).transpose())  

    # SDP problem

    sdp = pc.Problem()

    P1 = pc.SymmetricVariable("P1", n-1)
    P1b = (P1 & 0) // (0 & 0)
    lambdas = pc.RealVariable("lambdas", n)
    
    P2b = pc.SymmetricVariable("P2b", n)

    Qcd_consts = {}
    for index in range(n):
        Qcd_consts[index] = pc.Constant(f"Qcd{index}", np.matrix(Qcd[index], float))
    
    expression_P2b = P1b
    for index in range(n):
        expression_P2b = expression_P2b + lambdas[index] * Qcd_consts[index]

    sdp.add_constraint(P2b == expression_P2b)

    A1b = pc.Constant("A1b", np.matrix(A1bar, float))
    A2b = pc.Constant("A2b", np.matrix(A2bar, float))

    # alpha = pc.RealVariable("alpha")
    # beta = pc.RealVariable("beta")
    # gamma = pc.RealVariable("gamma")
    # sdp.add_constraint(alpha >> 0)
    # sdp.add_constraint(beta >> 0)
    # sdp.add_constraint(gamma >> 0)

    # Q1 = pc.Constant("Q1", QQ1)
    Q2 = pc.Constant("Q2", np.matrix(QQ2, float))

    # I = pc.Constant("I", Ibar)

    # mu1 = pc.RealVariable("mu1")
    # sdp.add_constraint(mu1 >> 0)
    mu2 = pc.RealVariable("mu2")
    sdp.add_constraint(mu2 >> 0)

    # eta1 = pc.RealVariable("eta1")
    # sdp.add_constraint(eta1 >> 0)
    eta2 = pc.RealVariable("eta2")
    sdp.add_constraint(eta2 >> 0)

    if normalize == True:
      # The following is a normalization condition. It needs to hold (easy to see with Sylvester method).
      # Sometimes the solver does not provide a solution if we give it this condition, but does provide
      # a solution if we do not. This is strange and could be investigated.
      sdp.add_constraint((P1b[0,0]) >> 1)

    # Cond1 = P1b - gamma * I
    # Cond2 = P2b - mu2 * Q2 - gamma * I
    # We set gamma to zero, since it does not make sense to use it (being semidefinite outside an hyperplane is the same as being semidefinite everywhere)
    Cond1 = P1b 
    Cond2 = P2b - mu2 * Q2  


    # Cond3 = 
    # Cond4 =

    # Cond5 = A1b.T * P1b + P1b * A1b + eta1 * Q1 + alpha * I 

    # Cond5 = A1b.T * P1b + P1b * A1b + alpha * I 
    # Cond6 = A2b.T * P2b + P2b * A2b + eta2 * Q2 + alpha * I 
    # We set alpha to zero, since it does not make sense to use it (being semidefinite outside an hyperplane is the same as being semidefinite everywhere)
    Cond5 = A1b.T * P1b + P1b * A1b 
    Cond6 = A2b.T * P2b + P2b * A2b + eta2 * Q2 

    # Cond7 = P1b - P2b - theta12[0] * Q1 - theta12[1] * R12 
    # Cond8 = P2b - P1b - theta21[0] * Q2 - theta21[1] * R21 


    # conditions 3.5
    sdp.add_constraint(Cond1 >> 0)
    sdp.add_constraint(Cond2 >> 0)

    # # conditions 3.6
    # sdp.add_constraint(P1b + nu1 * Q1 - beta * I << 0)
    # sdp.add_constraint(P2b + nu2 * Q2 - beta * I << 0)

    # conditions 3.7
    sdp.add_constraint(Cond5 << 0)
    sdp.add_constraint(Cond6 << 0)

    # # conditions 3.8
    # sdp.add_constraint(Cond7 >> 0)
    # sdp.add_constraint(Cond8 >> 0)

    # ACHTUNG: notice that if we do not give condition P[0,0] > 1, the solution where everything is zero is a valid solution for the SDP problem
    # but is not validated by the SymPy checks. 
    sol = sdp.solve(solver=sdp_solver)

    new_P1b = P1b.np

    # Start validation

    P1_sym = to_sym_matrix(np.asarray(P1b.np))
    # A1bar
    # A2bar
    # # I_sym = to_sym_matrix(np.asarray(Ibar))
    # QQ2
    mu2_sym = myround(mu2.np)
    eta2_sym = myround(eta2)
    P2_sym = deepcopy(P1_sym)
    for index in range(n):
        P2_sym = P2_sym + myround(lambdas[index].np) * Qcd[index]
    
    if not all([mu2_sym >= 0, eta2_sym >= 0]):
      logging.critical("The solution given by the sdp solver is not valid: some constants that should be greater or equal to zero are negative.")
      return None

    P1_sym_old_coord = translation.transpose() @ P1_sym @ (translation)
    P2_sym_old_coord = translation.transpose() @ P2_sym @ (translation)

    if certify != 'smt':
        if not all( [ P1_sym[-1,:] == sp.zeros(1,n),  P1_sym[:,-1] == sp.zeros(n,1), A1bar[-1,:] == sp.zeros(1,n),  A1bar[:,-1] == sp.zeros(n,1) ] ):
            logging.critical("There are errors in the matrices obtained.")
            return None
        P1_help = P1_sym[0:-1, 0:-1]
        A1bar_help = A1bar[0:-1, 0:-1]
        if certify == 'sylvester':
          checks = [(is_positive_sylvester(P1_help),"Lyap m0 is everywhere positive","Lyap m0 is negative at some point"),
                    (is_positive_sylvester(P2_sym - mu2_sym * QQ2),"Lyap m1 is everywhere positive","Lyap m1 is negative at some point"),
                    (is_positive_sylvester(-(sp.transpose(A1bar_help) @ P1_help + P1_help @ A1bar_help)),"Lyap m0 always decrease","Lyap m0 increases at some point"),
                    (is_positive_sylvester(-(sp.transpose(A2bar) @ P2_sym + P2_sym @ A2bar + eta2_sym * QQ2)),"Lyap m1 always decrease","Lyap m1 increases at some point")]
        elif certify == 'sympy':
          checks = [((P1_help).is_positive_definite,"Lyap m0 is everywhere positive","Lyap m0 is negative at some point"),
                    ((P2_sym - mu2_sym * QQ2).is_positive_definite,"Lyap m1 is everywhere positive","Lyap m1 is negative at some point"),
                    ((-(sp.transpose(A1bar_help) @ P1_help + P1_help @ A1bar_help)).is_positive_definite,"Lyap m0 always decrease","Lyap m0 increases at some point"),
                    ((-(sp.transpose(A2bar) @ P2_sym + P2_sym @ A2bar + eta2_sym * QQ2)).is_positive_definite,"Lyap m1 always decrease","Lyap m1 increases at some point")]
        for c,msg_good,msg_bad in checks:
          if not c:
            logging.critical("Fail "+ msg_bad)
            logging.critical("The Piecewise-Quadratic Lyapunov Function was numerically synthesized but is not valid.")
            return None
          logging.critical("CHECK " + msg_good)
        logging.critical("Found a valid Piecewise-Quadratic Lyapunov Function for the system. The system IS STABLE.")
    
    # The following can be used to save the results in an external file.
    # import pickle
    # with open('lf0_old_coord.pickle','wb') as f:
    #     pickle.dump(P1_sym_old_coord,f)
    # with open('lf1_old_coord.pickle','wb') as f:
    #     pickle.dump(P2_sym_old_coord,f)

    # with open('lf0_new_coord.pickle','wb') as f:
    #     pickle.dump(P1_sym,f)
    # with open('lf1_new_coord.pickle','wb') as f:
    #     pickle.dump(P2_sym,f)

    # with open('vector_sw_pr_mode0_less0_old_coord.pickle','wb') as f:
    #     pickle.dump(vector_sw_pr_mode0_less0,f)
    # with open('vector_sw_pr_mode0_less0_new_coord.pickle','wb') as f:
    #     pickle.dump(-cd,f)
    # breakpoint()

    Candidate_Lyap = Piecewise_Quadratic_Function()
    Candidate_Lyap.matrices[0] = P1_sym_old_coord
    Candidate_Lyap.matrices[1] = P2_sym_old_coord
    Candidate_Lyap.vector_sw_pr_mode0_less0 = vector_sw_pr_mode0_less0
    return Candidate_Lyap

def certify_piecewise_lyap(dyn_systems, switching_predicate_mode0_less0, Candidate_lyap, solver = Solver(logic=QF_NRA, name="z3")):

    smt_vars = [v for v in dyn_systems[0].states()]
    smt_vars.append(Symbol("var_weird_name", REAL))

    LF0 = Candidate_lyap._build_smt_function(smt_vars, 0)
    LF1 = Candidate_lyap._build_smt_function(smt_vars, 1)
    
    m0_invariant = LT(switching_predicate_mode0_less0, Real(0))
    m1_invariant = Not(m0_invariant)

    # Positive
    c1_0 = Implies( And(Equals(smt_vars[-1], Real(1)), m0_invariant), GE(LF0, Real(0)))
    c1_1 = Implies( And(Equals(smt_vars[-1], Real(1)), m1_invariant), GE(LF1, Real(0)))

    # Derivative positive
    LF0_der = dyn_systems[0].get_derivator().get_lie_der(LF0)

    eq_point = dyn_systems[0].get_equilibrium_point()[0]

    x_equals_equilibrium = And(And([ Equals(x, eq_point[x]) for x in smt_vars[:-1]]), Equals(smt_vars[-1], Real(1)))
    
    c2_0 = Implies(And(Equals(smt_vars[-1], Real(1)), m0_invariant, Not(x_equals_equilibrium)),
                    LT(LF0_der, Real(0)))
    # c2_0 = Implies(m0_invariant, LE(LF0_der, Real(0)))

    LF1_der = dyn_systems[1].get_derivator().get_lie_der(LF1)
    c2_1 = Implies(And(Equals(smt_vars[-1], Real(1)), m1_invariant, Not(x_equals_equilibrium)),
                   LT(LF1_der, Real(0)))
    # c2_1 = Implies(And(Equals(states[-1],Real(1)),m1_invariant), LE(LF1_der, Real(0)))

    # Does not decrease on switch
    cswitch = Implies(Equals(switching_predicate_mode0_less0, Real(0)), Equals(LF0,LF1))
    
    check = [(c1_0,"Lyap m0 is everywhere positive","Lyap m0 is negative at some point"),
            (c1_1,"Lyap m1 is everywhere positive","Lyap m1 is negative at some point"),
            (c2_0,"Lyap m0 always decrease","Lyap m0 increases at some point"),
            (c2_1,"Lyap m1 always decrease","Lyap m1 increases at some point"),
            (cswitch,"The two functions are equal on the switching surface","The two functions are NOT equal on the switching surface")
            ]

    for c,msg_good,msg_bad in check:
        if not _check_implication_full(solver, smt_vars, c):
            logging.critical("Fail "+ msg_bad)
            return False
        logging.critical("CHECK " + msg_good)
    return True