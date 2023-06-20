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

DEFAULT_PRECISION = 16

def myround(x, p=DEFAULT_PRECISION):
  ''' Rounding performed keeping p significant figures. '''
  import numpy as np
  x = np.asarray(float(x))
  x_positive = np.where(np.isfinite(x) & (x != 0), np.abs(x), 10**(p-1))
  mags_power = (p - 1 - np.floor(np.log10(x_positive)))
  mags = 10 ** mags_power
  rounded = np.round(x * mags)
  if mags_power < 0:
    rounded = Fraction(int(rounded) * int(10**(-mags_power)))
  else:
    rounded = Fraction(int(rounded), int(mags))
  return rounded

def myround_decimal(n,k=DEFAULT_PRECISION):
  ''' Rounding performed keeping p decimal figures. '''
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

def is_positive_sylvester(A):
  # Note: could be optimized
  n = sp.shape(A)[0]
  for i in range(n-1):
    if sp.Determinant(A).doit() <= 0:
      return False
    A = A.minor_submatrix(0, 0)
  return sp.Determinant(A).doit() > 0

def is_semipositive_sylvester(A):
  # Note: could be optimized
  n = sp.shape(A)[0]
  for i in range(n-1):
    if sp.Determinant(A).doit() < 0:
      return False
    A = A.minor_submatrix(0, 0)
  return sp.Determinant(A).doit() >= 0

def augment_sp(A):
    # Interprets a linear dynamical system in a dimension more.
    n = sp.shape(A)[0]
    A_aug = sp.zeros(n+1, n+1)
    A_aug[0:n, 0:n] = A
    return A_aug

def augment(A):
    # Interprets a linear dynamical system in a dimension more.
    n = len(A)
    A_aug = np.zeros([n+1, n+1])
    A_aug[0:n, 0:n] = A
    return A_aug

def translate(A, b):
    # Given the affine dynamical system A, translates it by the vector b
    n = len(A)
    change_coord = np.vstack([
    np.hstack([np.identity(n-1), -np.transpose(np.asmatrix(b))]),
    np.hstack([np.zeros([1,len(b)]), [[1]]])])
    A_trans = np.transpose(change_coord) @ A @ change_coord
    return A_trans

def can_vec(index,dimension):
    # Gives the dimension-th canonical vector of R^index.
    x = np.matrix(np.zeros([dimension,1]))
    x[index-1,0] = 1
    return x

def can_vec_sp(index,dimension):
    # Gives the dimension-th canonical vector of R^index.
    x = sp.zeros(dimension,1)
    x[index-1,0] = 1
    return x

def from_sympy_to_smt_vector(vect):
  res = []
  for j in range(len(vect)):
    res.append(Real(vect[j].numerator)/Real(vect[j].denominator))
  return res

def from_sympy_to_smt_matrix(sp_matrix):
  smt_matrix = []
  for i in range(sp.shape(sp_matrix)[0]):
    res = from_sympy_to_smt_vector(sp_matrix[i, :])
    smt_matrix.append(res)
  return smt_matrix