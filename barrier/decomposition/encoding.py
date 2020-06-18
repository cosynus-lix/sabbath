""" Implements the (linear) encoding of the semi-algebraic decomposition.
"""

from functools import partial
import copy

from pysmt.shortcuts import (
    TRUE, FALSE,
    Real,
    Not, And, Or, Implies, Iff, Equals,
    Equals, GE, GT, LT, LE,
    Exists,
    Symbol,
    get_atoms
)

from pysmt.typing import BOOL, REAL

from barrier.lzz.lzz import get_inf_dnf, get_ivinf_dnf
from barrier.formula_utils import FormulaHelper

from barrier.ts import TS

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



def _get_lzz_in(dyn_sys, preds_list, next_f, lzz_f):
    current_impl = lambda p : Implies(p, lzz_f(p))
    next_impl = lambda p : Implies(next_f(p),
                                   get_inf_dnf(dyn_sys, lzz_f(p)))
    and_not_inf = lambda p : And(p,
                                 Not(get_inf_dnf(dyn_sys, lzz_f(p))))

    list(map(next_impl, preds_list))

    return And([And(list(map(current_impl, preds_list))),
                And(list(map(next_impl, preds_list))),
                Or(list(map(and_not_inf, preds_list)))])


def _get_lzz_out(dyn_sys, preds_list, next_f, lzz_f):
    current_impl = lambda p : Implies(p, get_ivinf_dnf(dyn_sys, lzz_f(p)))
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


def get_preds(formula):
    print(get_atoms(formula))
    return []


def rewrite_init(env, ts, prop):
    reset = FormulaHelper.get_fresh_var_name(env.formula_manager, "reset")

    new_vars = set(ts.state_vars)
    new_vars.add(reset)
    next_f = lambda x : partial(FormulaHelper.rename_formula,
                                env = env,
                                vars = set(new_vars),
                                suffix = "_next")(formula=x)

    new_init = reset
    new_trans = And(Not(reset),
                    And(Or(reset, next_f(ts.init)),
                        Or(Not(reset), ts.trans)))

    new_ts = TS(new_vars, next_f, new_init, new_trans)
    return (new_ts, prop, [reset])

def rewrite_prop(env, ts, prop):
    new_prop = FormulaHelper.get_fresh_var_name(env.formula_manager, "new_prop")

    new_vars = set(ts.state_vars)
    new_vars.add(new_prop)

    next_f = lambda x : partial(FormulaHelper.rename_formula,
                                env = env,
                                vars = set(new_vars),
                                suffix = "_next")(formula=x)

    new_init = And(ts.init, Iff(new_prop, prop))
    new_trans = And([ts.trans,
                     Iff(new_prop, prop),
                     Iff(next_f(new_prop), next_f(prop))])

    new_ts = TS(new_vars, next_f, new_init, new_trans)
    return (new_ts, new_prop, [new_prop])


class DecompositionOptions:
    def __init__(self, rewrite_init = True,
                 rewrite_property = True):
        self.rewrite_init = rewrite_init
        self.rewrite_property = rewrite_property

class DecompositionEncoder:
    def __init__(self, env, dyn_sys, invar, poly, init, safe,
                 options = DecompositionOptions()):
        """
        Input (a safety verification problem):
        - a polynomial dynamical system der(X) = p(X)
        - a set of invariant sates Inv(X)
        - a set of polynomials (not predicates) defining the abstraction
        - a set of initial states I(X)
        - a safety property P(X)
        """

        self.env = env
        self.options = options
        self.dyn_sys = dyn_sys
        self.invar = invar
        self.poly = poly
        self.preds = _get_preds_list(poly)
        self.init = init
        self.safe = safe
        self.vars = list(dyn_sys._states)

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

        self.pred_map = {}
        build_preds_rec(self.preds, 0, self.pred_map)
        self.pred_vars_f = lambda x : self.pred_map[x]


    def get_ts(self):
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

        ts = TS(self.vars, self.next_f, new_init, new_trans)

        if (not (self.options.rewrite_init and
                 self.options.rewrite_property)):
            # we need to add the predicate from init and property
            # to the decomposition if we want to use IA later
            #
            raise NotImplementedException()

        if (self.options.rewrite_init):
            (ts, new_prop, new_preds) = rewrite_init(self.env, ts, new_prop)
            preds_for_ia += new_preds

        if (self.options.rewrite_property):
            (ts, new_prop, new_preds) = rewrite_prop(self.env, ts, new_prop)
            preds_for_ia += new_preds

        return (ts, new_prop, preds_for_ia)


    def get_quantified_ts(self):
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

        return (TS([self.pred_vars_f(p) for p in self.preds],
                   self.next_f,
                   new_init, new_trans),
                new_prop)

    def _get_trans_enc(self):
        sys = self.dyn_sys.get_renamed(self.lzz_f)

        lzz_in = _get_lzz_in(sys, self.preds,
                             self.next_f, self.lzz_f)

        lzz_out = _get_lzz_out(sys, self.preds,
                               self.next_f, self.lzz_f)

        return And(And(_get_neigh_encoding(self.poly, self.next_f),
                       And(self.invar, self.next_f(self.invar))),
                   Or(lzz_in, lzz_out))
