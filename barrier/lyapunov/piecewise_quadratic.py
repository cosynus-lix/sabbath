"""
Computes the swtiched lyapunov function following Jens Oehlerking thesis.

Plan:
  1. Encoding of Lyapunov function synthesis
    - just implement and validate with thesis'example
    - then extend

  2. S-procedure for linear sets (invariants and guards)
  3. Encoding for exact switching

"""
from collections import namedtuple
import sys
import fractions
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

import numpy as np
import picos

from barrier.lie import Derivator


Affine = namedtuple("Affine", "A b") # Ax + b
LeConst = namedtuple("LeConst", "A b") # Ax <= b
Edge = namedtuple("Edge", "source guards update dest")


# Ax >= b
def get_ge(A,b):
  return LeConst(-A,-b)

def myround(n):
  return round(float(n),20)

# SMT products
def vect_times_matrix(vect, matrix):
  assert(len(vect) == len(matrix))
  res = []
  for i1 in range(len(vect)):
    index_term = Real(0)
    for i2 in range(len(vect)):
      num = matrix[i2][i1]
      coefficient = num
      index_term = index_term + Times(vect[i2], coefficient)
    res.append(simplify(index_term))
  return res

def dot_product_smt(vect1, vect2):
  # vect1^T vect2
  assert len(vect1) == len(vect2)

  res = Real(0)
  for i1 in range(len(vect1)):
    res = res + vect2[i1] * vect1[i1]
  res = simplify(res)
  return res

def to_smt_vect(vect):
  res = []
  for j in range(len(vect)):
    num = myround(vect[j])
    res.append(Real(num))
  return res

def to_smt_matrix(np_matrix):
  smt_matrix = []
  for i in range(len(np_matrix)):
    res = to_smt_vect(np_matrix[i])
    smt_matrix.append(res)
  return smt_matrix


def get_derivator(hs, smt_vars, flow, ignore_b = False):
  vector_field = {}
  A_smt = to_smt_matrix(flow.A)
  b_smt = to_smt_vect(flow.b)

  for i in range(hs.dimensions):
    var = smt_vars[i]
    if not var.is_symbol():
      continue
    assert(ignore_b or b_smt[i] == Real(0)) # never add affine term b_smt[i]: but it should be explicit!
    flow = dot_product_smt(A_smt[i], smt_vars) 
    vector_field[var] = flow
  derivator = Derivator(vector_field)
  return derivator

def _get_lyapunov_smt(smt_vars, lyapunov_map, lyapunov_smt, m):
  if m not in lyapunov_smt:
    smt_matrix = to_smt_matrix(lyapunov_map[m])
    app = vect_times_matrix(smt_vars, smt_matrix)
    # x^T V_m x
    V_m = dot_product_smt(app, smt_vars)
    lyapunov_smt[m] = V_m
  V_m = lyapunov_smt[m]
  return V_m


class NumericAffineHS:
  """ Streamlined representation of a affine hs using matrix """

  def __init__(self, modes, dimensions, flow, edges, invariant, is_homogeneous=False):
    self.modes = modes # set of modes (should be integers)
    self.dimensions = dimensions # number of continuous variables
    self.flows = flow # mode -> List[Affine]

    self.edges = edges # list of edges
    self.invariant = invariant # list of constraint

    self.s_procedure_invar = {} # S-procedure term for modes (a list of matrixes for each mode)
    self.s_procedure_edges = [[] for i in range(len(self.edges))] # S-procedure terms for edges (a list of matrixes for each edge)


    self.is_homogeneous = is_homogeneous # True if the system is homogeneous (should be checked automatically)
    self.has_last_var_dummy = False # True if dimensions were extended to make system homogeneous

  @staticmethod
  def get_smt_vars(dimension):
    return [Symbol("x_%d" % i, REAL) for i in range(dimension)]

  def set_s_procedure_invar(self, mode, s_procedure_matrixes):
    self.s_procedure_invar[mode] = s_procedure_matrixes

  def set_s_procedure_edge(self, edge_index, s_procedure_matrixes):
    self.s_procedure_edges[edge_index] = s_procedure_matrixes

  # Assume to have the terms from the S-procedure for invar and guards
  def get_s_procedure_invar(self, mode):
    if mode in self.s_procedure_invar:
      return self.s_procedure_invar[mode]
    else:
      return []

  def get_s_procedure_edge(self, edge_index):
    if edge_index in self.s_procedure_edges:
      return self.s_procedure_edges[edge_index]
    else:
      return []

  def make_homogeneous(self):
    """ Makes the system homogeneus, adding a fake variable """

    def extend_affine(affine, new_dimension, is_update=False):
      if affine is None:
        return None
      new_A = np.concatenate((affine.A, np.transpose(np.array([affine.b]))), axis=1)
      new_A = np.concatenate((new_A, np.zeros((1,new_dimension))), axis=0)
      if is_update:
        new_A[new_dimension-1, new_dimension-1] = 1
      return Affine(new_A, np.zeros((new_dimension,1)))

    def extend_le(le, new_dimension):
      if affine is None:
        return None
      new_A = np.concatenate((le.A, np.zeros((new_dimension-1,1))), axis=1)
      new_A = np.concatenate((new_A, np.zeros((1,new_dimension))), axis=0)
      new_b = np.concatenate((le.b,np.zeros(1)),axis=0)
      return LeConst(new_A, new_b)


    if self.is_homogeneous:
      return

    self.dimensions = self.dimensions + 1

    new_flow = {}
    for (mode, affine_list) in self.flows.items():
      new_affine_list = []
      for affine in affine_list:
        new_affine_list.append(extend_affine(affine, self.dimensions))
      new_flow[mode] = new_affine_list
    self.flows = new_flow

    new_edges = []
    for edge in self.edges:
      new_edge = Edge(edge.source,
                      [extend_le(le,self.dimensions) for le in edge.guards],
                      extend_affine(edge.update, self.dimensions, True),
                      edge.dest)
      new_edges.append(new_edge)
    self.edges = new_edges

    new_invars = {}
    for mode,const in self.invariant.items():
      new_const = [extend_le(le, self.dimensions) for le in const]
      new_invars[mode] = new_const
    self.invariant = new_invars

    self.is_homogeneous = True
    self.has_last_var_dummy = True


  def change_coordinate(self, point):
    """
    Change the corrdinate system from x to y, where y = x - point
    """
    assert not self.has_last_var_dummy

    point_stack = np.vstack(point)
    def dotprod(A, point):
      return np.dot(A,point).transpose()[0]

    new_flow = {}
    for (mode, affine_list) in self.flows.items():
      new_affine_list = []
      for affine in affine_list:
        # Ax + b => A (y + point) + b => A y + (b + A point)
        new_b = affine.b + dotprod(affine.A, point_stack)
        new_affine_list.append(Affine(affine.A, new_b))
        assert(len(affine.b) == len(new_b))
      new_flow[mode] = new_affine_list
    self.flows = new_flow

    new_edges = []
    for edge in self.edges:
      new_edge = Edge(edge.source,
                      # Ax <= b => A (y + point) <= b => A y  <= b - A point
                      [LeConst(le.A, le.b - dotprod(le.A, point_stack)) for le in edge.guards],
                      # x' = Ax + b => y' + point = A (y + point) + b =>
                      #    y' = A y + A point + b - point
                      Affine(edge.update.A, dotprod(edge.update.A, point_stack) - point + edge.update.b),
                      edge.dest)
      new_edges.append(new_edge)
    self.edges = new_edges

    new_invars = {}
    for mode,const in self.invariant.items():
      # Ax <= b => A (y + point) <= b => A y  <= b - A point
      new_const = [LeConst(le.A, le.b - dotprod(le.A,point_stack)) for le in const]
      new_invars[mode] = new_const
    self.invariant = new_invars


  def get_vars(self):
    raise NotImplementedException()


  @staticmethod
  def le_as_smt(smt_vars, le_constraint):
    res = TRUE()
    for i in range(len(le_constraint.A)):
      assert len(le_constraint.A[i]) == len(smt_vars)
      e1 = LE(dot_product_smt([Real(float(n)) for n in le_constraint.A[i]],
                              smt_vars),
              Real(float(le_constraint.b[i])))
      res = And(res,e1)
    return res

  def verify_s_procedure(self): 
    smt_vars = NumericAffineHS.get_smt_vars(self.dimensions-1)
    smt_vars.append(Real(1))

    # invar first
    for m in self.modes:
      invar_m = NumericAffineHS.get_smt_affine(smt_vars, self.invariant[m])
      for invar_matrix in self.get_s_procedure_invar(m):
        if not NumericAffineHS._verify_s_procedure(invar_m, invar_matrix, smt_vars):
          return False

    for i in range(len(self.edges)):
      edge = self.edges[i]
      invar_m = NumericAffineHS.get_smt_affine(smt_vars, self.invariant[edge.source])
      guard_i = NumericAffineHS.get_smt_affine(smt_vars, edge.guards)

      for guard_matrix in self.get_s_procedure_edge(i):
        if not NumericAffineHS._verify_s_procedure(And(invar_m,guard_i), guard_matrix, smt_vars):
          return False
    return True


  @staticmethod
  def _verify_s_procedure(smt_formula, s_procedure_matrix, smt_vars):
    s_procedure_constraints = TRUE()

    # x^T * matrix
    p1 = []
    for i1 in range(len(smt_vars)):
      index_term = Real(0)
      for i2 in range(len(smt_vars)):
        num = myround(s_procedure_matrix[i2,i1])
        coefficient = Real(num)
        index_term = index_term + Times(smt_vars[i2], coefficient)
      p1.append(simplify(index_term))

    # p1 * x
    res = Real(0)
    for i1 in range(len(smt_vars)):
      res = res + p1[i1] * smt_vars[i1]
    res = simplify(GE(res, Real(0)))

    solver = Solver(logic=QF_NRA, name="z3")

    # DEBUG
    # if (not solver.is_valid(Implies(smt_formula, res))):
    #   solver.add_assertion(Not(Implies(smt_formula, res)))
    #   if solver.solve():
    #     model = solver.get_model()
    #     print(model)
    #     print(model.get_value(smt_formula))
    #     print(res.simplify().serialize(), " ", model.get_value(res))

    return solver.is_valid(Implies(smt_formula, res))

  @staticmethod
  def get_smt_affine(smt_vars, affine_list):
    smt_list = [NumericAffineHS.le_as_smt(smt_vars, le_constraint) for le_constraint in affine_list]
    return And(smt_list)

  def __str__(self):
    return ("Modes: %s" \
            "\ndimensions: %d\n" \
            "is_homogeneous: %d\n" \
            "has_last_var_dummy: %d\n" \
            "flow:\n%s\n") % (",".join([str(l) for l in self.modes]),
                             self.dimensions,
                             self.is_homogeneous,
                             self.has_last_var_dummy,
                             "\n".join([str(m) + ": " + ",".join([str(a) for a in flowlist]) for (m,flowlist) in self.flows.items()]))

class PiecewiseQuadraticLF:
  def __init__(self):
    self.alpha = None
    self.beta = None
    self.gamma = None
    self.edge_slack = None

    self.lyapunov_map = {}

    # use this to re-construct the problem
    self.I_tilda = {}


def synth_piecewise_quadratic(hs, modes_in_loop=[], epsilon = 0.0001, dbg_stream=sys.stdout):
  """
  Synthesize a piecewise quadratic lyapunov function for the system.
  Follows 3.5.2

  Input: affine hybrid system

  Output: A piece-wise quadradic lyapunov function Bool x (m -> R^{n+1 x n+1})
  """

  def dbgprint(*args):
    print(args, file=dbg_stream)

  V_GE_F1 = 1
  V_LE_F2 = 2
  V_PRIME_LE_MINUS_F3 = 4
  V_EDGES = 8
  S_PROCEDURE = 16

  to_encode = V_GE_F1 | V_LE_F2 | V_PRIME_LE_MINUS_F3 | V_EDGES | S_PROCEDURE
  #to_encode = V_GE_F1 | V_LE_F2 | V_PRIME_LE_MINUS_F3  | S_PROCEDURE
  #to_encode = V_PRIME_LE_MINUS_F3

  # get the homogeneous system from an affine one. This simplifies things, and move the equilibrium point to 0
  assert(hs.is_homogeneous)

  sdp = picos.Problem()

  I = np.identity(hs.dimensions-1)
  I = np.concatenate((I, np.zeros((1,hs.dimensions-1))), axis=0)
  I = np.concatenate((I, np.zeros((hs.dimensions,1))), axis=1)
  I_tilda = picos.Constant('identity_tilda', I)

  # Optimization
  # When the dynamic for a variable is 0 in a mode, then we set
  # the correspondent entry I_tilda as 0
  I_tilda_map = {}
  for m in hs.modes:
    non_const_dimensions = np.zeros(hs.dimensions)
    for f in hs.flows[m]:
      # f is an affine
      for i in range(hs.dimensions):
        for j in range(hs.dimensions):
          if f.A[i][j] != 0:
            non_const_dimensions[i] = 1
            break
        if f.b[i] != 0:
          non_const_dimensions[i] = 1
    I_tilda_map[m] = picos.Constant('identity_tilda_%d' % m,  np.diag(non_const_dimensions))


  epsilon = picos.Constant("epsilon", epsilon)

  # declare slack vars
  alpha = picos.RealVariable("alpha")
  beta = picos.RealVariable("beta")
  gamma = picos.RealVariable("gamma")
  edge_slack = picos.RealVariable("edge_slack")
  slack_vars = [alpha,beta,gamma,edge_slack]

  Q_invar = {}
  for mode in hs.modes:

    Q_invar[mode] = hs.get_s_procedure_invar(mode)

  R_edges = {}
  for index in range(len(hs.edges)):
    e = hs.edges[index]
    res = hs.get_s_procedure_edge(index)
    R_edges[index] = res

  # S-Procedure terms!
  #
  # m = number of modes, tot_q_constraints
  # for all m, for all j in Q_invar[m](0) (tot constraints for m)
  #   mu_m_j
  #   nu_m_j
  #   eta_m_j
  # declare P_m \in (n+1) x (n+1)
  vec_size = (1, hs.dimensions)
  mu = {}
  nu = {}
  eta = {}
  P_s = {}
  for mode in hs.modes:
    tot_constraints = len(Q_invar[mode])
    if (tot_constraints <= 0):
      mu[mode] = None
      nu[mode] = None
      eta[mode] = []
      flow_index = -1
      for flow in hs.flows[mode]:
        flow_index += 1
        eta[mode].append(None)
    else:
      mu[mode] = picos.RealVariable("mu_%d" % mode, tot_constraints)
      nu[mode] = picos.RealVariable("nu_%d" % mode, tot_constraints)

      eta[mode] = []
      flow_index = -1
      for flow in hs.flows[mode]:
        flow_index += 1
        eta[mode].append(picos.RealVariable("eta_m%d_f%d" % (mode, flow_index),
                                            tot_constraints))

      # Constraints from (3.3)
      # Positivity for mu, nu, eta, scalars
      if (to_encode & S_PROCEDURE):
        dbgprint("Encoding 3.3")

        constraints = []
        c1 = mu[mode] >= 0
        c2 = nu[mode] >= 0
        constraints.append(c1)
        constraints.append(c2)
        flow_index = -1
        for flow in hs.flows[mode]:
          flow_index += 1
          c3 = eta[mode][flow_index] >= 0
          constraints.append(c3)

        for c in constraints:
          sdp.add_constraint(c)
        dbgprint(",".join([str(c) for c in constraints]))

    # hack if mode has to be equal
    dst_loop = False
    for (src,dst) in modes_in_loop:
      if dst == mode:
        dst_loop = True
        break
    if (not dst_loop):
      P_s[mode] = picos.SymmetricVariable('P_%d' % mode, (hs.dimensions, hs.dimensions))

  # HACK - still not general, assume a single loop...
  for (src,dst) in modes_in_loop:
    equality_on_border = None
    edge = None
    for e in hs.edges:
      if e.source == src and e.dest == dst:
        edge = e
    assert not edge is None

    guard = e.guards[0]

    AA = -np.copy(guard.A)
    AA[:,hs.dimensions-1] = guard.b
    all_eq_on_border = picos.Constant(0)
    for i in range(hs.dimensions):
      constraint = AA[i]
      if (np.all(constraint == 0)):
        # all zeros
        continue
      for j in range(hs.dimensions):
        base_vect = np.zeros(hs.dimensions)
        base_vect[j] = 1
        e_j = np.transpose(np.vstack(base_vect))
        vect = np.vstack(AA[i])
        q_j = e_j * np.transpose(vect) + vect * np.transpose(e_j)

        if (np.all(q_j == 0)):
          # skipping 0-s matrix
          continue
        # print("\n",e_j,vect,q_j)
        # print("e_j: ", e_j)
        # print("vect ", vect)
        # print("e_j * vect^T ", e_j * np.transpose(vect))
        # print("vect * e_j^T ", vect * np.transpose(e_j))
        # print("QJ ", q_j)

        l = picos.RealVariable("eq_guards_%d_%d_%d_%d" % (edge.source, edge.dest, i, j), 1)
        sdp.add_constraint(l >= 0)
        if equality_on_border is None:
          all_eq_on_border = all_eq_on_border + l * q_j

    P_s[dst] = P_s[src] + all_eq_on_border
    print("P_s[%d] = " % dst,  P_s[dst])

  edge_vars = {}
  for index in range(len(hs.edges)):
    e = hs.edges[index]
    tot_constraints = len(Q_invar[mode])
    if (tot_constraints > 0):
      edge_vars[index] = picos.RealVariable("edges_%d" % index, tot_constraints)
      # Constraints from (3.4)
      # Positivity for edge_vars scalars
      constraint = edge_vars[index] >= 0
      if (to_encode & S_PROCEDURE):
        dbgprint("Encoding 3.4 ", constraint)
        sdp.add_constraint(constraint)

  # Positivity constraints (3.1, 3.2)
  # alpha and beta greater than 0

  dbgprint("Encoding 3.1, 3.2:")
  for var in slack_vars:
    constraint = var - epsilon >= 0
    sdp.add_constraint(constraint)
    dbgprint("\t",constraint)

  def _build_sproc_const_new(lambda_terms, matrix_list):
    """ Build product with terms from S-Procedure """
    const = picos.Constant(0)
    for i in range(len(matrix_list)):
      const = const + lambda_terms[i] * matrix_list[i]
    return const

  for mode in hs.modes:
    # (3.5) - positivity constraints on Lyapunov function
    # P - invar_constraint - I >> 0
    # V(X) = x^T P x >= ||x||^2
    tmp = _build_sproc_const_new(mu[mode], Q_invar[mode])
    constraint = (P_s[mode] -
                  tmp -
                  gamma * I_tilda_map[mode] >> 0)

    if (to_encode & V_GE_F1):
      dbgprint("Encoding 3.5 ", constraint)
      dbgprint(P_s[mode])
      sdp.add_constraint(constraint)

    # (3.6) - positivity constraints on Lyapunov function
    # P + invar_constraint - beta I << 0
    # V(X) = x^T P x <= beta ||x||^2
    constraint = (P_s[mode] +
                  _build_sproc_const_new(nu[mode], Q_invar[mode]) -
                  beta * I_tilda_map[mode] << 0)
    if (to_encode & V_LE_F2):
      dbgprint("Encoding 3.6 ", constraint)
      sdp.add_constraint(constraint)

    # (3.7) - constraints on the derivative
    flow_index = -1
    for flow in hs.flows[mode]:
      flow_index += 1
      A_t = np.transpose(flow.A)

      # A^T P + P A + alpha I << 0
      # V'(X) <= alpha ||x||^2
      eta_constraints = _build_sproc_const_new(eta[mode][flow_index], Q_invar[mode])

      constraint = A_t * P_s[mode] + P_s[mode] * flow.A + eta_constraints + alpha * I_tilda_map[mode] << 0
      if (to_encode & V_PRIME_LE_MINUS_F3):
        dbgprint("Encoding 3.7", constraint) #, A_t, flow.A, eta_constraints)
        if (mode == 2):
          sdp.add_constraint(constraint)


  for index in range(len(hs.edges)):
    e = hs.edges[index]
    tot_constraints = len(R_edges[index])

    # HACK: skip edges if they are the one from a loop
    skip = False
    for (src,dst) in modes_in_loop:
      if (src == e.source and dst == e.dest) or (dst == e.source and src == e.dest):
        skip = True
        break
    if skip:
      dbgprint("Skipping %d -> %d" % (e.source, e.dest))
      continue

    # (3.8) - constraints on the edges
    if (tot_constraints > 0):
      # Constraints from (3.8)
      edge_constraint = _build_sproc_const_new(edge_vars[index], R_edges[index])

      A_t = np.transpose(e.update.A)
      constraint = P_s[e.source] - A_t * P_s[e.dest] * e.update.A - edge_constraint - edge_slack * I_tilda >> 0
      if (to_encode & V_EDGES):
        dbgprint("Encoding 3.8 ", constraint)
        sdp.add_constraint(constraint)

  #  sdp.options.solver = "mosek"
  solution = sdp.solve(solver='mosek',verbosity=False, primals = None)

  # Return a piecewise Lyapunov function
  if (solution.problemStatus == picos.modeling.solution.PS_FEASIBLE):
    " Get the results with a specific precision "
    lf = PiecewiseQuadraticLF()

    lf.alpha = myround(alpha.value)
    lf.beta = myround(beta.value)
    lf.gamma = myround(gamma.value)
    lf.edge_slack = myround(edge_slack.value)
    lf.lyapunov_map = {}

    for m in hs.modes:
      print(m)
      m_out,m_i_tilda = [],[]
      assert(not P_s[mode] is None)
      assert(not P_s[mode].np is None)
      l_m = P_s[mode].np

      for i in range(hs.dimensions):
        rout,r1 = [],[]
        for j in range(hs.dimensions):
          rout.append(myround(l_m[i][j]))
          r1.append(I_tilda_map[mode].np[i][j])
        m_out.append(rout)
        m_i_tilda.append(r1)

      lf.lyapunov_map[m] = m_out
      lf.I_tilda[m] = m_i_tilda

      # # DEBUG
      # m_positive = np.identity(hs.dimensions)
      # for (sign, a) in to_check[m]:
      #   m_positive = m_positive * (sign * a.np)
      # w, v = np.linalg.eig(m_positive)
      # dbgprint("\nEIGEN %d" % m)
      # dbgprint(m_positive)
      # dbgprint("")
      # dbgprint(w)
      # dbgprint("\n")

      # dbgprint("Mu value %d " % m, mu[m].value, "\n")

      # # END DEBUG

    return (True, lf)
  else:
    return (False, None)



def validate(hs, lf, solver = Solver(logic=QF_NRA, name="z3")):
  """
  Conditions on the Global Lyapunov Function from theorem 3.5.

  Input: We have a function V_m for each mode m.

  We check the following conditions for each mode m:
  1) there exists f1, f2, such that x \in Inv(m) => f1(||x||) <= V_m(x) <= f2(||x||))
  2) there exists f3 such that x \in Inv(m) => V_m' <= -f3(||x||)
  3) for each edge (m,G,U,m2) x \in G => V_m2(U(x)) <= V_m1(x)

  In our case:
    - f1 = ||x||^2 = x^t x
    - f2 = beta ||x||^2 = beta x^t x
    - f3 = alpha ||x||^2 = alpha x^t x

  f1,f2,f3 should be K^{\inf} functions:
    - f(0) = 0
    - f strictly monotonically increasing
    - lim_{x \mapsto \inf}{f(x)} = \inf

  So, we verify that:
  0) beta > 0, alpha > 0

  1) x \in Inv(m) => x^t x <= V_m(x) <= beta x^t x
  2) x \in Inv(m) => V_m'(x) <= - alpha x^t x
  3) for each edge (m,G,U,m2) x \in G => V_m2(U(x)) <= V_m1(x)
  """

  def _get_update(expr, smt_vars, update_expr):
    """ applies the update to the expression """
    new_smt_vars = []
    update_map = {}
    rename_map = {}
    for i in range(len(smt_vars)):
      v = smt_vars[i]
      if (v.is_symbol()):
        new_var = Symbol("%s_copy" % (v.symbol_name()), v.symbol_type())
      else:
        # case of 1 in the vars array
        assert (v.is_constant())
        new_var = v
      new_smt_vars.append(new_var)
      rename_map[new_var] = v

    for i in range(len(smt_vars)):
      v = smt_vars[i]
      assert(len(update_expr.A[i]) == len(new_smt_vars))
      update_v = dot_product_smt([Real(float(coeff)) for coeff in update_expr.A[i]],
                                 new_smt_vars) + Real(float(update_expr.b[i]))
      update_map[v] = update_v

    expr = substitute(expr, update_map)
    expr = substitute(expr, rename_map)
    return expr


  alpha_smt, beta_smt, gamma_smt = [Real(float(val)) for val in [lf.alpha,lf.beta,lf.gamma]]
  to_check = [("alpha", lf.alpha), ("beta", lf.beta), ("gamma", lf.gamma)]
  for name,val in to_check:
    val_smt = Real(float(val))
    if (not solver.is_valid(GT(val_smt,Real(0)))):
      print("%s %f is not positive " % (name,val))
      return False

  smt_vars = NumericAffineHS.get_smt_vars(hs.dimensions-1)
  smt_vars.append(Real(1))

  lyapunov_smt = {}
  for m in hs.modes:
    # build the derivator
    assert(len(hs.flows[m]) == 1)
    derivator = get_derivator(hs, smt_vars, hs.flows[m][0])

    V_m = _get_lyapunov_smt(smt_vars, lf.lyapunov_map, lyapunov_smt, m)
    i_tilda_smt = to_smt_matrix(lf.I_tilda[m])

    smt_invar = hs.get_smt_affine(smt_vars, hs.invariant[m])

    x_t_x = dot_product_smt(vect_times_matrix(smt_vars, i_tilda_smt), smt_vars)

    # 1) x \in Inv(m) => gamma x^t I_tilda x <= V_m(x) <= beta x^t I_tilda x
    c1 = Implies(smt_invar,
                 And(LE(Times(gamma_smt, x_t_x), V_m), LE(V_m, Times(beta_smt, x_t_x))))

    # 2) x \in Inv(m) => V_m'(x) <= - alpha x^t x
    V_m_der = derivator.get_lie_der(V_m)
    c2 = Implies(smt_invar,
                 And(LE(V_m_der, Times(Minus(Real(0), alpha_smt), x_t_x))))

    # 3) for each edge (m,G,U,m2) x \in G => V_m2(U(x)) <= V_m1(x)
    edge_cond = []
    for i in range(len(hs.edges)):
      e = hs.edges[i]
      if (e.source != m):
        continue

      print("Encoding %d -> %d" % (e.source, e.dest))

      smt_guard = And(hs.get_smt_affine(smt_vars, e.guards), smt_invar)
      V_dest = _get_lyapunov_smt(smt_vars, lf.lyapunov_map, lyapunov_smt, e.dest)
      V_dest_update = _get_update(V_dest, smt_vars, e.update)

      # print("V_dest ", V_dest.simplify().serialize())
      # print("V_dest_update ", V_dest_update.simplify().serialize())

      ce = Implies(smt_guard, LE(V_dest_update, V_m))
      edge_cond.append(ce)


    print("Checking for mode ", m)
    res, error = True, None
    if (not solver.is_valid(c1)):
      error = "c1 does not hold" # %s" % c1.simplify().serialize()
      res = False
    elif (not solver.is_valid(c2)):
      error = "c2 does not hold %s" % c2.simplify().serialize()
      res = False
    else:
      for c in edge_cond:
        if (not solver.is_valid(c)):
          error = "c3 does not hold %s" % c.simplify().serialize()
          res =  False
          break

    if (not res):
      print(error)
      return False

  return True


def validate_eq_johansson(hs, lf, solver = Solver(logic=QF_NRA, name="z3")):
  """
  Validate a lf obtained with the Johansson piecewise quadratic lyapunov function, plus equalities on switching conditions.
  Ad-hoc check for the 2-mode system!
  """
  assert hs.is_homogeneous

  alpha_smt = Real(float(lf.alpha))
  if (not solver.is_valid(GT(alpha_smt,Real(0)))):
    print("%s %f is not positive " % ("alpha",val))
    return False

  smt_vars = NumericAffineHS.get_smt_vars(hs.dimensions-1)
  smt_vars.append(Real(1))

  res = True
  lyapunov_smt = {}
  for m in hs.modes:
    # build the derivator
    assert(len(hs.flows[m]) == 1)

    assert (m != 1 or np.all(hs.flows[m][0].b == 0))
    derivator = get_derivator(hs, smt_vars, hs.flows[m][0], m == 1) # ignore affine term b in mode 1

    V_m = _get_lyapunov_smt(smt_vars, lf.lyapunov_map, lyapunov_smt, m)
    V_m_der = derivator.get_lie_der(V_m)
    i_tilda_smt = to_smt_matrix(lf.I_tilda[m])
    smt_invar = hs.get_smt_affine(smt_vars, hs.invariant[m])
    x_t_x = dot_product_smt(vect_times_matrix(smt_vars, i_tilda_smt), smt_vars)

    print("V_%d = %s" % (m,V_m.serialize()))
    print("V_%d_der = %s" % (m,V_m_der.serialize()))

    # 1) x \in Inv(m) => V_m(x) >= 0
    c1 = Implies(smt_invar, And(GE(V_m, Real(0))))

    # 2) x \in Inv(m) => V_m'(x) <= - alpha x^t x
    # c2 = Implies(smt_invar,
    #              LE(V_m_der, Times(Minus(Real(0), alpha_smt), x_t_x)))
    # c2 = Implies(smt_invar,LE(V_m_der, Real(0)))
    c2 = Implies(smt_invar, LE(V_m_der, Real(1)))

    def _check_implication(solver, implication):
      solver.reset_assertions()
      solver.add_assertion(Not(implication))
      if (solver.solve()):
        print("\nNot great!")
        model = solver.get_model()

        def get_le_val(le):
          assert(le.is_le())
          return Minus(le.args()[0], le.args()[1])

        def get_float_val_model(model, exp):
          smt_val = model.get_value(exp)
          float_val = float(fractions.Fraction(smt_val.serialize()))
          return float_val

        def get_float_val_le(model, exp):
          return get_float_val_model(model, get_le_val(exp))

        implicant = implication.args()[0].simplify()
        consequent = implication.args()[1].simplify()

        print("Model = ", ", ".join(["%s = %s" % (str(v),get_float_val_model(model, v)) for v in smt_vars]))
        print("Implicant value =",  get_float_val_le(model, implicant))
        print("Consequent value =", get_float_val_le(model, consequent))
        return False
      else:
        return True

    error = None
    print("Checking c1 mode=",m)
    if (not _check_implication(solver, c1)):
      error = "c1 does not hold" # %s" % c1.simplify().serialize()
      res = False
      print(error)

    print("Checking c2 mode=",m)
    if (not _check_implication(solver, c2)):
      error = "c2 does not hold %s" % c2.simplify().serialize()
      res = False
      print(error)

  return res
