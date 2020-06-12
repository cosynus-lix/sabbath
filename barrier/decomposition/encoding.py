""" Implements the (linear) encoding of the semi-algebraic decomposition.
"""

from functools import partial
import copy

from pysmt.shortcuts import (
    TRUE, FALSE,
    Real,
    Not, And, Or, Implies, Iff, Equals,
    Equals, GE, GT, LT, LE,
    Symbol
)

from pysmt.typing import BOOL, REAL

from barrier.lzz.lzz import get_inf_dnf, get_ivinf_dnf
from barrier.formula_utils import FormulaHelper

def _get_preds_list(poly):
    zero = Real(0)
    return (
        [GT(p, zero) for p in poly] +
        [LT(p, zero) for p in poly] +
        [And(GE(p, zero), LE(p, zero)) for p in poly]
    )


def _get_lzz_in(dyn_sys, poly, next_f, lzz_f):
    preds_list = _get_preds_list(poly)

    current_impl = lambda p : Implies(p, lzz_f(p))
    next_impl = lambda p : Implies(next_f(p),
                                   get_inf_dnf(dyn_sys, lzz_f(p)))
    and_not_inf = lambda p : And(p,
                                 Not(get_inf_dnf(dyn_sys, lzz_f(p))))

    list(map(next_impl, preds_list))

    return And([And(list(map(current_impl, preds_list))),
                And(list(map(next_impl, preds_list))),
                Or(list(map(and_not_inf, preds_list)))])


def _get_lzz_out(dyn_sys, poly, next_f, lzz_f):
    preds_list = _get_preds_list(poly)

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


class DecompositionEncoder:
    def __init__(self, env, dyn_sys, invar, poly, init, safe):
        self.env = env
        self.dyn_sys = dyn_sys
        self.invar = invar
        self.poly = poly
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
                name = FormulaHelper.get_fresh_var_name(env.formula_manager,
                                                        "pred",
                                                        index)
                pred_var = Symbol(name, BOOL)
                res[preds[index]] = pred_var
                self.vars.append(pred_var)
                res[self.next_f(preds[index])] = self.next_f(pred_var)

                build_preds_rec(preds, index + 1, res)

        self.pred_map = {}
        build_preds_rec(_get_preds_list(poly), 0, self.pred_map)
        self.pred_vars_f = lambda x : self.pred_map[x]


    def get_symbolic_decomposition(self):
        """
        Input (a safety verification problem):
        - a polynomial dynamical system der(X) = p(X)
        - a set of initial states I(X)
        - a set of invariant sates Inv(X)
        - a safety property P(X)
        - a set of polynomials defining the abstraction

        Output (a symbolic transition system):
        - I'(X)
        - T'(X,X',Z)
        - P'(X)
        can be used for predicate abstraction.
        """

        new_init = And(self.init, self.invar)
        new_trans = self._get_trans_enc()
        new_prop = self.safe

        return (new_init, new_trans, new_prop)

    def _get_trans_enc(self):
        sys = self.dyn_sys.get_renamed(self.lzz_f)

        abs_rel = _get_abs_rel(_get_preds_list(self.poly), self.pred_vars_f)
        abs_rel_next = self.next_f(abs_rel)

        lzz_in = _get_lzz_in(sys, self.poly,
                             self.next_f, self.lzz_f)

        lzz_out = _get_lzz_out(sys, self.poly,
                               self.next_f, self.lzz_f)

        return And(And(And(_get_neigh_encoding(self.poly, self.next_f),
                           And(self.invar, self.next_f(self.invar))),
                       And(abs_rel, abs_rel_next)),
                   Or(lzz_in, lzz_out))
