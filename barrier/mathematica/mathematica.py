from six.moves import xrange

from pysmt.exceptions import SolverAPINotFound

try:
  import wolframclient
  from wolframclient.evaluation import WolframLanguageSession
  from wolframclient.language import wl, wlexpr
except ImportError:
  raise SolverAPINotFound

from pysmt.logics import QF_NRA
from pysmt import typing as types
from pysmt.solvers.solver import Solver, Converter, SolverOptions
from pysmt.solvers.eager import EagerModel
from pysmt.walkers import DagWalker
from pysmt.constants import Fraction, is_pysmt_fraction, is_pysmt_integer
from pysmt.decorators import clear_pending_pop, catch_conversion_error

from pysmt.exceptions import (ConvertExpressionError, PysmtValueError,
                              PysmtTypeError)
from pysmt.oracles import get_logic


from pysmt.shortcuts import get_env

class MathematicaOptions(SolverOptions):
  """Options for the Mathematica Solver.
  """

  def __init__(self, **base_options):
    SolverOptions.__init__(self, **base_options)

  def __call__(self, solver):
    # do nothing now
    pass

# EOC MathematicaOptions


class MathematicaSolver(Solver):
  """Solver based on the Mathematica Reduce function
  """
  LOGICS = [ QF_NRA ]
  OptionsClass = MathematicaOptions

  def __init__(self, environment, logic, **options):
    Solver.__init__(self,
                    environment=environment,
                    logic=logic,
                    **options)

    self.mgr = environment.formula_manager
    self.converter = MathematicaConverter(environment=self.environment)
    self.options(self)

    # Get the connection to mathematica
    # TODO: Get as option the path to mathematica
    self.session = WolframLanguageSession()

    self.backtrack = []
    self.assertions_stack = []
    self.reset_assertions()

  @clear_pending_pop
  def reset_assertions(self):
    true_formula = self.mgr.Bool(True)
    self.assertions_stack = [true_formula]

  @clear_pending_pop
  def add_assertion(self, formula, named=None):
    self.assertions_stack.append(formula)

  @clear_pending_pop
  def solve(self, assumptions=None):
    if assumptions is not None:
      self.push()
      self.add_assertion(self.mgr.And(assumptions))
      self.pending_pop = True

    to_solve = None
    for expr in self.assertions_stack:
      if to_solve is None:
        to_solve = expr
      else:
        to_solve = self.mgr.And(to_solve, expr)

    if to_solve is None:
      to_solve = self.mgr.Bool(True)

    # Here is where we call Reduce from Mathematica
    #assert self.session.ensure_started()

    free_vars = to_solve.get_free_variables()
    exists_formula = self.mgr.Exists(free_vars, to_solve)
    mathematica_exists_formula = self.converter.convert(exists_formula)

    # print(exists_formula)
    # print(mathematica_exists_formula)

    reduce_cmd = wl.Reduce(mathematica_exists_formula, wlexpr('Real'))
    exist_res = self.session.evaluate(reduce_cmd)

    # Invalidate cached model
    self.latest_model = None
    return exist_res

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
    self.session.stop()
    self.session = None

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
    return wlexpr(rep)

  def walk_int_constant(self, formula, **kwargs):
    raise ConvertExpressionError("Integer constants (%s) are not"
                                 "allowed!" % str(formula) )

  def walk_bool_constant(self, formula, **kwargs):
    if formula.constant_value():
      return wlexpr('True')
    else:
      return wlexpr('False')

  def walk_bv_constant(self, formula, **kwargs):
    raise ConvertExpressionError("BV constants (%s) are not"
                                 "allowed!" % str(formula) )

  def walk_plus(self, formula, args, **kwargs):
    return wl.Plus(*args)

  def walk_minus(self, formula, args, **kwargs):
    return wl.Plus(args[0], wl.Minus(args[1]))

  def walk_times(self, formula, args, **kwargs):
    return wl.Times(args[0],args[1])

  def walk_div(self, formula, args, **kwargs):
    return wl.Divide(args[0],args[1])

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

  def walk_exists(self, formula, args, **kwargs):
    assert len(args) == 1
    sf = args[0]
    varset = [self.walk_symbol(x) for x in formula.quantifier_vars()]
    if len(varset) == 0:
      return sf
    return wl.Exists(varset, sf)

  def walk_forall(self, formula, args, **kwargs):
    assert len(args) == 1
    sf = args[0]
    varset = [self.walk_symbol(x) for x in formula.quantifier_vars()]
    if len(varset) == 0:
      return sf
    return wl.ForAll(varset, sf)

  def walk_function(self, formula, args, **kwargs):
    raise ConvertExpressionError("Uninterpreted functions (%s) are not "
                                 "allowed!" % str(formula) )

  def walk_toreal(self, formula, args, **kwargs):
    raise ConvertExpressionError("toreal operator (%s) are not "
                                 "allowed!" % str(formula) )
# EOC MathematicaConverter

def get_mathematica(env=get_env()):
  name = "mathematica"
  logics = [QF_NRA]

  if not env.factory.is_generic_solver(name):
    env.factory.add_generic_solver(name, [], logics)

  return MathematicaSolver(env, QF_NRA)
