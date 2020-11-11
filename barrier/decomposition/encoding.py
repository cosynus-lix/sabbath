""" Implements the (linear) encoding of the semi-algebraic decomposition.
"""

import logging
from functools import partial

from pysmt.shortcuts import (
    TRUE, FALSE,
    Real,
    Minus,
    Not, And, Or, Implies, Iff, Equals,
    Equals, GE, GT, LT, LE,
    Exists,
    Symbol,
    get_atoms
)

from pysmt.typing import BOOL, REAL

from barrier.lzz.lzz import (
    get_inf_dnf, get_ivinf_dnf,
    get_lzz_encoding,
    debug_print_max_degree
)
from barrier.lie import Derivator
from barrier.formula_utils import (
    FormulaHelper,
)

from barrier.decomposition.utils import (
    get_poly_from_pred,
    get_unique_poly_list,
    sort_poly_by_degree,
    print_abs_stats,
    add_poly_from_formula,
    sort_poly_by_degree,
    get_neighbors
)

from barrier.ts import TS, ImplicitAbstractionEncoder

def _get_preds_list(poly):
    zero = Real(0)
    return (
        [GT(p, zero) for p in poly] +
        [LT(p, zero) for p in poly] +
        [And(GE(p, zero), LE(p, zero)) for p in poly]
    )

def _get_preds_ia_list(poly):
    zero = Real(0)
    return (
        [GE(p, zero) for p in poly] +
        [LE(p, zero) for p in poly]
    )

def _get_lzz_in(derivator, preds_list, next_f, lzz_f):
    current_impl = lambda p : Implies(p, lzz_f(p))
    next_impl = lambda p : Implies(next_f(p),
                                   get_inf_dnf(derivator, lzz_f(p)))
    and_not_inf = lambda p : And(p,
                                 Not(get_inf_dnf(derivator, lzz_f(p))))

    return And([And(list(map(current_impl, preds_list))),
                And(list(map(next_impl, preds_list))),
                Or(list(map(and_not_inf, preds_list)))])


def _get_lzz_out(derivator, preds_list, next_f, lzz_f):
    current_impl = lambda p : Implies(p, get_ivinf_dnf(derivator, lzz_f(p)))
    next_impl = lambda p : Implies(next_f(p), lzz_f(p))
    and_not_inf = lambda p : And(p, Not(lzz_f(p)))

    return And([And(list(map(current_impl, preds_list))),
                And(list(map(next_impl, preds_list))),
                Or(list(map(and_not_inf, preds_list)))])


def _get_abs_rel(preds, preds_f):
    rel = TRUE()
    for p in preds:
        pred_trans = preds_f(p)
        rel = And(rel, pred_trans)
    return rel


def _get_neigh_encoding(poly, get_next_formula):
    zero = Real(0)

    def _change_noteq(p, get_next):
        next_p = get_next(p)
        return And(
            Implies(GT(p, zero), Or( Equals(next_p, zero),
                                     GT(next_p, zero))),
            And(Implies(LT(p, zero), Or( Equals(next_p, zero),
                                         LT(next_p, zero))),
                Implies(Equals(p, zero),Equals(next_p, zero)))
        )

    def _change_eq(p, get_next):
        next_p = get_next(p)
        return And(Implies(GT(p, zero), GT(next_p, zero)),
                   Implies(LT(p, zero), LT(next_p, zero)))

    def _iter(poly, p_fun):
        res = TRUE()
        for p in poly:
            res = And(res, p_fun(p))
        return res

    return Or(_iter(poly, partial(_change_noteq,
                                  get_next = get_next_formula)),
              _iter(poly, partial(_change_eq, get_next = get_next_formula)))


def _get_explicit_encoding(derivator, polynomials, next_f, lzz_f):
    """
    Builds the explicit encoding for the decomposition.

    """
    def _enum_states(polynomials):

        stack = [(0, [])]

        while len(stack) != 0:
            (index, preds_trail) = stack.pop()

            if (index == len(polynomials)):
                yield set(preds_trail)
            else:
                a = polynomials[index]
                for (sign, first) in [(LT,True), (LT,False), (Equals,True)]:
                    predicate = sign(a, Real(0)) if first else sign(Real(0), a)
                    new_preds_trail = list(preds_trail)
                    new_preds_trail.append(predicate)
                    stack.append((index+1, new_preds_trail))

    trans_list = []
    for s1_list in _enum_states(polynomials):
        s1_abs = And(s1_list)
        s1_lzz = lzz_f(s1_abs)
        for s2_list in get_neighbors(polynomials, s1_list):
            s2_abs = And(s2_list)
            s2_lzz = lzz_f(s2_abs)
            lzz = get_lzz_encoding(s1_lzz, derivator, Or(s1_lzz, s2_lzz))
            trans_list.append(And(s1_abs, next_f(s2_abs), Not(lzz)))

    return Or(trans_list)

class DecompositionOptions:
    def __init__(self,
                 rewrite_init = False,
                 rewrite_property = False,
                 add_init_prop_predicates = False,
                 explicit_encoding = False):
        """
        Options for the decomposition:
        - rewrite_init: add a reset states for the initial states of the
          resulting ts
        - rewrite_property: rewrite the property with a boolean variable
          and an implication in the resulting ts
        - add_init_prop_predicates: add automatically the initial and property
          predicates
        - explicit encoding: enumerates explicitly all the transitions
          between abstract states.
        """
        self.rewrite_init = rewrite_init
        self.rewrite_property = rewrite_property
        self.add_init_prop_predicates = add_init_prop_predicates
        self.explicit_encoding = explicit_encoding

# EOC DecompositionOptions

class DecompositionEncoder:
    def __init__(self, env, dyn_sys, invar, poly, init, safe,
                 options = DecompositionOptions(),
                 stats_stream = None,
                 quantified_ts = False):
        """
        Input (a safety verification problem):
        - a polynomial dynamical system der(X) = p(X)
        - a set of invariant sates Inv(X)
        - a set of polynomials (not predicates) defining the abstraction
        - a set of initial states I(X)
        - a safety property P(X)
        """

        logger = logging.getLogger(__name__)

        self.env = env
        self.options = options
        self.dyn_sys = dyn_sys
        self.invar = invar
        self.stats_stream = stats_stream
        self.quantified_ts = False

        # Set the list of polynomials
        # The implicit abstraction encoding takes care of adding the
        # predicates for the init and the safety property or adding a reset
        # state/rewriting the property.
        #
        # However, in the case we need to add new predicates then the transition
        # relation using the decomposition changes.
        #
        # So, here we already add the predicates of init and safe if needed.
        #
        self.poly = poly

        if (options.add_init_prop_predicates):
            add_poly_from_formula(self.poly, And(init, invar), env)
            add_poly_from_formula(self.poly, safe, env)
        # normalize the list of polynomials (e.g., x and -x creates the same decomposition)
        self.poly = get_unique_poly_list(self.poly)
        logger.debug("Total of polynomials %d" % len(self.poly))

        self.preds = _get_preds_list(self.poly)

        self.init = init
        self.safe = safe

        self.vars = []
        for var in dyn_sys.states():
            self.vars.append(var)
        for var in dyn_sys.inputs():
            self.vars.append(var)

        self.next_f = lambda x : partial(FormulaHelper.rename_formula,
                                         env = env,
                                         vars = self.vars,
                                         suffix = "_next")(formula=x)

        self.lzz_f = lambda x : partial(FormulaHelper.rename_formula,
                                        env = env,
                                        vars = self.vars,
                                        suffix = "_lzz")(formula=x)

        # From predicate (all over X or all over X') to the predicate
        # variables
        def build_preds_rec(preds, index, res):
            if (index < len(preds)):
                pred_var = FormulaHelper.get_fresh_var_name(env.formula_manager, "pred")
                res[preds[index]] = pred_var
                self.vars.append(pred_var)
                res[self.next_f(preds[index])] = self.next_f(pred_var)

                build_preds_rec(preds, index + 1, res)


        if (self.quantified_ts):
            pred_map = {}
            build_preds_rec(self.preds, 0, self.pred_map)
            self.pred_vars_f = lambda x : self.pred_map[x]


    def get_ts_ia(self):
        """
        Output:
        - TS a symbolic transition system,
        - P property
        - List of abstraction polynomials
        """
        new_trans = self._get_trans_enc()
        new_init = And([self.init, self.invar])
        new_prop = self.safe

        preds_for_ia = _get_preds_ia_list(self.poly)
        ts_vars = self.vars
        ts_next = self.next_f

        ts = TS(self.env, self.vars, self.next_f, new_init, new_trans)

        enc = ImplicitAbstractionEncoder(ts,
                                         new_prop,
                                         preds_for_ia,
                                         self.env,
                                         self.options.rewrite_init,
                                         self.options.rewrite_property,
                                         self.options.add_init_prop_predicates)

        ts = enc.get_ts_abstract()
        new_prop = enc.get_prop_abstract()
        preds_for_ia = enc.get_predicates()

        return (ts, new_prop, preds_for_ia)


    def get_direct_ts_ia(self):
        """
        Output:
        - A transition system where:
          - init: initial state expressed over the abstraction predicates
          - prop: property expressed over the abstraction predicates
          - trans: the transition relation
        - List of abstraction polynomials
        """
        new_trans = self._get_trans_enc()
        new_init = And([self.init, self.invar])
        new_prop = self.safe

        preds_for_ia = _get_preds_ia_list(self.poly)
        ts_vars = self.vars
        ts_next = self.next_f

        print("CAVALLO")
        print(", ".join([str(v) for v in ts_vars]))

        ts = TS(self.env, self.vars, self.next_f, new_init, new_trans)

        return (ts, new_prop, preds_for_ia)


    def get_quantified_ts(self):
        assert self.quantified_ts
        abs_rel = _get_abs_rel(self.preds,
                               self.pred_vars_f)
        abs_rel_next = self.next_f(abs_rel)
        new_trans = And(And(abs_rel, abs_rel_next),
                        self._get_trans_enc())
        new_init = And([self.init, self.invar, abs_rel])
        new_prop = And([self.safe, abs_rel])

        to_quantify = (self.vars +
                       [self.next_f(v) for v in self.vars] +
                       [self.lzz_f(v) for v in self.vars])

        new_trans = Exists(to_quantify, new_trans)
        new_init = Exists(to_quantify, new_init)
        new_prop = Exists(to_quantify, new_prop)

        return (TS(self.env,
                   [self.pred_vars_f(p) for p in self.preds],
                   self.next_f,
                   new_init, new_trans),
                new_prop)

    def _get_trans_enc(self):
        logger = logging.getLogger(__name__)
        logger.debug("Encoding transition using lzz...")

        sys = self.dyn_sys.get_renamed(self.lzz_f)

        derivator = sys.get_derivator()
        # Not needed
        # sort_poly_by_degree(derivator, self.poly)

        if (not self.stats_stream is None):
            print_abs_stats(self.stats_stream, derivator, self.poly)

        if (len(self.preds) > 0):
            if (not self.options.explicit_encoding):
                lzz_in = _get_lzz_in(derivator, self.preds,
                                     self.next_f, self.lzz_f)

                lzz_out = _get_lzz_out(derivator, self.preds,
                                       self.next_f, self.lzz_f)

#                 # DEBUG
#                 print("Checking trans is sat")
#                 from pysmt.shortcuts import Solver
#                 from pysmt.logics import QF_NRA
#                 from barrier.mathematica.mathematica import get_mathematica
#                 from pysmt.shortcuts import get_env
#                 solver = get_mathematica(get_env())
#                 solver = Solver(logic=QF_NRA, name="z3")
#                 print("check in...")
#                 print(lzz_in.serialize())
#                 assert(solver.is_sat(lzz_in))
#                 print("check out...")
#                 assert(solver.is_sat(lzz_out))
#                 print("checked trans...")

                lzz_encoding = Or(lzz_in, lzz_out)
            else:
                lzz_encoding = _get_explicit_encoding(derivator,
                                                      self.poly,
                                                      self.next_f,
                                                      self.lzz_f)
        else:
            # corner case
            lzz_encoding = TRUE()

        # frame condition for the time-independent parameters
        fc_list = [Equals(var, self.next_f(var)) for var in sys.inputs()]
        if (len(fc_list) == 0):
            fc = TRUE()
        else:
            fc = And(fc_list)

        res = And([_get_neigh_encoding(self.poly, self.next_f),
                   self.invar,
                   self.next_f(self.invar),
                   fc,
                   lzz_encoding])

        debug_print_max_degree(logger, lzz_encoding)
        logger.debug("Encoded transition using lzz...")

        return res

# EOC DecompositionEncoder
