""" Utility functions for linear algebra.
"""

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

def myround(n):
  return round(float(n),6)

# SMT products
def vect_times_matrix(vect, matrix):
  """
  vect x matrix, where vect is [1 x n], matrix is [n x m].
  Result is the dot product, [1 x m] vector.

  vect and matrix should contain Real numbers (from pysmt)
  """
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
  """
  vect1 is [1 x n], vect2 is [1 x n], both containing Real numbers
  Computes dot product of vect1 x transpose(vect2)
  """
  assert len(vect1) == len(vect2)

  res = Real(0)
  for i1 in range(len(vect1)):
    res = res + vect2[i1] * vect1[i1]
  res = simplify(res)
  return res

def to_smt_vect(vect):
  """ Convert a vector containing floating point numbers to
  a vector of Real numbers.

  The function looses precision in the conversion.

  TODO: Fix precision loss.
  """
  res = []
  for j in range(len(vect)):
    num = myround(vect[j])
    res.append(Real(num))
  return res

def to_smt_matrix(np_matrix):
  """ Convert a matrix containing floating points to a 
  matrix containing Real"""
  smt_matrix = []
  for i in range(len(np_matrix)):
    res = to_smt_vect(np_matrix[i])
    smt_matrix.append(res)
  return smt_matrix
