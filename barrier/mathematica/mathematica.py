from pysmt.exceptions import SolverAPINotFound

try:
  import wolframclient
  from wolframclient.evaluation import WolframLanguageSession
  from wolframclient.language import wl, wlexpr
except ImportError:
  raise SolverAPINotFound

import pysmt.logics
from pysmt import typing as types
from pysmt.solvers.solver import Solver, Converter, SolverOptions
from pysmt.solvers.eager import EagerModel
from pysmt.walkers import DagWalker

from pysmt.decorators import clear_pending_pop, catch_conversion_error

from pysmt.exceptions import (ConvertExpressionError, PysmtValueError,
                              PysmtTypeError)
from pysmt.oracles import get_logic

class MathematicaOptions(SolverOptions):
  """Options for the Mathematica Solver.
  """

  def __init__(self, **base_options):
    SolverOptions.__init__(self, **base_options)

# EOC MathematicaOptions


class MathematicaSolver(Solver):
  """Solver based on the Mathematica Reduce function
  """
  LOGICS = [ pysmt.logics.NRA ]
  OptionsClass = MathematicaOptions

  def __init__(self, environment, logic, **options):
    Solver.__init__(self,
                    environment=environment,
                    logic=logic,
                    **options)

    self.mgr = environment.formula_manager
    self.converter = MathematicaConverter(environment=self.environment)
    self.options(self)

  @clear_pending_pop
  def reset_assertions(self):
    true_formula = self.mgr.Bool(True)
    self.assertions_stack = [(true_formula,
                              self.converter.convert(true_formula))]

  @clear_pending_pop
  def declare_variable(self, var):
    self.converter.declare_variable(var)

  @clear_pending_pop
  def add_assertion(self, formula, named=None):
    self.assertions_stack.append((formula, None))

  @clear_pending_pop
  def solve(self, assumptions=None):
    if assumptions is not None:
      self.push()
      self.add_assertion(self.mgr.And(assumptions))
      self.pending_pop = True

    for (i, (expr, bdd)) in enumerate(self.assertions_stack):
      if bdd is None:
        bdd_expr = self.converter.convert(expr)
        _, previous_bdd = self.assertions_stack[i-1]
        new_bdd = self.ddmanager.And(previous_bdd, bdd_expr)
        self.assertions_stack[i] = (expr, new_bdd)

    _, current_state = self.assertions_stack[-1]
    res = (current_state != self.ddmanager.Zero())
    # Invalidate cached model
    self.latest_model = None
    return res

  def get_value(self, item):
    if self.latest_model is None:
      self.get_model()
    return self.latest_model.get_value(item)

  def get_model(self):
    raise NotImplementedError

  @clear_pending_pop
  def push(self, levels=1):
    for _ in xrange(levels):
      self.backtrack.append(len(self.assertions_stack))

  @clear_pending_pop
  def pop(self, levels=1):
    for _ in xrange(levels):
      l = self.backtrack.pop()
      self.assertions_stack = self.assertions_stack[:l]

  def _exit(self):
    pass

# EOC MathematicaSolver


class MathematicaConverter(Converter, DagWalker):
  """ Convert a pysmt formula in a mathematica formula.

  Does not implement the back conversion!
  """

  def __init__(self, environment):
    DagWalker.__init__(self)

    self.environment = environment
    self.mgr = self.environment.formula_manager
    self._get_type = environment.stc.get_type

    # todo: remember mapping of symbols
    # todo: implement back mapping


  @catch_conversion_error
  def convert(self, formula):
    """Convert a PySMT formula into a Mathematica formula.

    Now we only allow symbols to be Real, and everything we use the
    Real domain.
    Mathematica has other domains (e.g., Boolean) but I'm not sure
    it implements any theory combination.

    This function might throw an exception if
    an error during conversion occurs.
    """
    # May rewrite Boolean variables to use Real variables in the
    # future.
    res = self.walk(formula)
    return res

  def walk_symbol(self, formula, **kwargs):
    # TODO check the type!
    if not formula.is_symbol():
      raise PysmtTypeError("Trying to declare as a variable something "
                           "that is not a symbol: %s" % formula)

    if not formula.symbol_type().is_real_type():
      raise ConvertExpressionError("Trying to declare a symbol that "
                                   "is not of Real type (%s : %s)" % (str(formula.symbol_type()),
                                                                      formula.symbol_name()))
    res = wlexpr(formula.symbol_name())
    return res

  def walk_real_constant(self, formula, **kwargs):
    assert is_pysmt_fraction(formula.constant_value())
    frac = formula.constant_value()
    n,d = frac.numerator, frac.denominator
    rep = str(n) + "/" + str(d)
    return wlexpr(repr)

  def walk_int_constant(self, formula, **kwargs):
    raise ConvertExpressionError("Integer constants (%s) are not"
                                 "allowed!" % str(formula) )

  def walk_bool_constant(self, formula, **kwargs):
    raise ConvertExpressionError("Boolean constants (%s) are not"
                                 "allowed!" % str(formula) )

  def walk_bv_constant(self, formula, **kwargs):
    raise ConvertExpressionError("BV constants (%s) are not"
                                 "allowed!" % str(formula) )

  def walk_plus(self, formula, args, **kwargs):
    return wl.Plus(*args)

  def walk_minus(self, formula, args, **kwargs):
    return wl.Plus(args[0], wl.Minus(args[1]))

  def walk_times(self, formula, args, **kwargs):
    return wl.Times(args[0],args[1])

  def walk_equals(self, formula, args, **kwargs):
    return wl.Equal(args[0], args[1])

  def walk_le(self, formula, args, **kwargs):
    return wl.LessEqual(args[0], args[1])

  def walk_lt(self, formula, args, **kwargs):
    return wl.Less(args[0], args[1])

  def walk_and(self, formula, args, **kwargs):
    return wl.And(*args)

  def walk_or(self, formula, args, **kwargs):
    return wl.Or(*args)

  def walk_not(self, formula, args, **kwargs):
    return wl.Not(args[0])

  def walk_iff(self, formula, args, **kwargs):
    return wl.Equivalent(args[0], args[1])

  def walk_implies(self, formula, args, **kwargs):
    return wl.Implies(args[0], args[1])

  def walk_ite(self, formula, args, **kwargs):
    i = args[0]
    t = args[1]
    e = args[2]

    if self._get_type(formula).is_bool_type():
      impl = self.mgr.Implies(formula.arg(0), formula.arg(1))
      th = self.walk_implies(impl, [i,t])
      nif = self.mgr.Not(formula.arg(1))
      ni = self.walk_not(nif, [i])
      el = self.walk_implies(self.mgr.Implies(nif, formula.arg(2)), [ni,e])
      return wl.And(th, el)
    else:
      raise ConvertExpressionError("Trying to convert a non-boolean "
                                   "ITE statement (%s)" % formula)

  def walk_function(self, formula, args, **kwargs):
    raise ConvertExpressionError("Uninterpreted functions (%s) are not "
                                 "allowed!" % str(formula) )

  def walk_toreal(self, formula, args, **kwargs):
    raise ConvertExpressionError("toreal operator (%s) are not "
                                 "allowed!" % str(formula) )
# EOC MathematicaConverter
