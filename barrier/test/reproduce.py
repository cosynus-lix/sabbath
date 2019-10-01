from pysmt.shortcuts import Solver, Equals, Real, Symbol
from pysmt.logics import QF_NRA
from pysmt.typing import REAL

from fractions import Fraction

solver = Solver(logic=QF_NRA, name="z3")

x = Symbol("x", REAL)
formula = Equals(x*x, Real(Fraction(2,1)))

solver.is_sat(formula)

print(solver.get_model())
