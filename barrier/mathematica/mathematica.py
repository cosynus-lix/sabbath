from six.moves import xrange
import logging

from concurrent.futures import TimeoutError

try:
  import wolframclient
  from wolframclient.evaluation import WolframLanguageSession
  from wolframclient.language import wl, wlexpr
  from wolframclient.evaluation.kernel.path import find_default_kernel_path
except:
  pass

from pysmt.exceptions import SolverAPINotFound
from pysmt.logics import QF_NRA
from pysmt import typing as types
from pysmt.solvers.solver import Solver, Converter, SolverOptions
from pysmt.solvers.eager import EagerModel
from pysmt.walkers import DagWalker
from pysmt.constants import Fraction, is_pysmt_fraction, is_pysmt_integer
from pysmt.decorators import clear_pending_pop, catch_conversion_error

from pysmt.exceptions import (PysmtException, ConvertExpressionError,
                              PysmtValueError, PysmtTypeError)
from pysmt.oracles import get_logic
from pysmt.shortcuts import get_env

class OutOfTimeSolverError(PysmtException):
  def __init__(self, budget):
    PysmtException.__init__(self,
                            "The solver used already a maximum budget (%s)" % str(budget))


def has_kernel():
  return not (find_default_kernel_path() is None)

def exit_callback_print_time(solver, outstream):
    if (not solver.session is None):
      outstream.write("Getting out of mathematica!\n")

      if (solver.options.budget_time != 0):
        outstream.write("Mathematica time: %s\n" % str(solver.used_time))
      else:
        outstream.write("Mathematica time (no budget): %s\n" % str(solver.session.evaluate(wl.TimeUsed())))


class MathematicaSession():
  _session = None

  @staticmethod
  def get_session():
    if not has_kernel():
      raise SolverAPINotFound

    if MathematicaSession._session is None:
      if True:
        logging.debug("Creating a session for mathematica...")
        try:
          MathematicaSession._session = WolframLanguageSession()
          MathematicaSession._session.ensure_started()
        except:
          raise SolverAPINotFound
      else:
        logging.debug("Mathematica Kernel not found")
        raise SolverAPINotFound

    return MathematicaSession._session

class MathematicaOptions(SolverOptions):
  """Options for the Mathematica Solver.
  """

  def __init__(self, **base_options):
    SolverOptions.__init__(self, **base_options)

    self.budget_time = 0
    for k,v in self.solver_options.items():
      if k == "budget_time":
        try:
          v_float = float(v)
        except:
          raise ValueError("Invalid value for %s: %s" % \
                           (str(k),str(v)))
      else:
        raise ValueError("Unrecognized option '%s'." % k)
      # Store option
      setattr(self, k, v)

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

    self.used_time = 0

    self.backtrack = []
    self.assertions_stack = []
    self.reset_assertions()

    self._exit_callback = None

    self.session = MathematicaSession.get_session()

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
    free_vars = to_solve.get_free_variables()
    exists_formula = self.mgr.Exists(free_vars, to_solve)
    mathematica_exists_formula = self.converter.convert(exists_formula)

    reduce_cmd = wl.Reduce(mathematica_exists_formula, wlexpr('Reals'))

    budget_time = self.options.budget_time
    if (self.options.budget_time > 0):
      remaining_time = (
        self.options.budget_time -
        self.used_time)

      if (remaining_time <= 0):
        raise OutOfTimeSolverError(budget_time)

      timed_eval_cmd = wl.TimeConstrained(reduce_cmd,
                                          remaining_time)
      exist_res = self.session.evaluate(timed_eval_cmd)

      if (type(exist_res) != bool):
        if (exist_res.name == '$Aborted'):
          raise OutOfTimeSolverError(self.options.budget_time)
      self.used_time = self.session.evaluate(wl.TimeUsed())
    else:
      exist_res = self.session.evaluate(reduce_cmd)

    # Invalidate cached model
    self.latest_model = None
    return exist_res

  def get_value(self, item):
    if self.latest_model is None:
      self.get_model()
    return self.latest_model.get_value(item)

  def get_model(self):
    # We should call FindInstance to find a model (instead o resolve)
    # The main issue is to parse algebraic numbers
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

  def set_exit_callback(self, callback):
    self._exit_callback = callback

  def _exit(self):
    if (not None is self._exit_callback):
      self._exit_callback(self)

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
    assert(len(args) == 2)
    return wl.Plus(args[0], wl.Minus(args[1]))

  def walk_times(self, formula, args, **kwargs):
    return wl.Times(*args)

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


def get_mathematica(env=get_env(), budget_time=0, exit_callback=None):
  try:
    import wolframclient
  except:
    raise SolverAPINotFound

  solver = MathematicaSolver(env, QF_NRA,
                             solver_options={"budget_time" : budget_time})

  if (not exit_callback is None):
    solver.set_exit_callback(exit_callback)

  return solver



