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
import sympy as sp

DEFAULT_PRECISION = 6

def myround(n,k=DEFAULT_PRECISION):
  rounded = round(float(n),k)
  rounded = Fraction.from_float(rounded)
  rounded = rounded.limit_denominator(pow(10,k))
  return rounded


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

def matrix_times_vect(vect, matrix):
  """
  matrix x vect, where matrix is [m x n] vect is [n x 1], .
  Result is the dot product, [m x 1] vector.

  vect and matrix should contain Real numbers (from pysmt)
  """
  res = []
  for row_index in range(len(matrix)):
    assert(len(matrix[row_index]) == len(vect))

    index_term = Real(0)
    for column_index in range(len(vect)):
      num = matrix[row_index][column_index]
      coefficient = num
      index_term = index_term + Times(vect[column_index], coefficient)
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

def to_smt_vect(vect, k=DEFAULT_PRECISION):
  """ Convert a vector containing floating point numbers to
  a vector of Real numbers.

  The function looses precision in the conversion.

  TODO: Fix precision loss.
  """
  res = []
  for j in range(len(vect)):
    num = myround(vect[j], k)
    res.append(Real(num))
  return res

def to_smt_matrix(np_matrix, k = DEFAULT_PRECISION):
  """ Convert a matrix containing floating points to a 
  matrix containing Real"""
  smt_matrix = []
  for i in range(len(np_matrix)):
    res = to_smt_vect(np_matrix[i], k)
    smt_matrix.append(res)
  return smt_matrix

def to_sym_matrix(A, k = DEFAULT_PRECISION):
  A_sympy=[]
  for ind in range(0,len(A)):
    A_sympy.append(sp.Matrix([myround(x) for x in A[ind]]).transpose())
  return sp.Matrix(A_sympy)