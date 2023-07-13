""" Implements the (linear) encoding of the semi-algebraic decomposition.
"""

import logging
from functools import partial

from pysmt.shortcuts import (
    TRUE, FALSE,
    Real,
    Minus,
    Not, And, Or, Implies, Iff, Equals,
    EqualsOrIff,
    Equals, GE, GT, LT, LE,
    Exists,
    Symbol,
    get_atoms,
    ExactlyOne
)

from pysmt.typing import BOOL, REAL

from barrier.lzz.lzz import (
    get_inf_dnf, get_ivinf_dnf,
    get_lzz_encoding,
    debug_print_max_degree,
    LzzOpt
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

def _get_lzz_in(opt, derivator, preds_list, next_f, lzz_f):
    bound = None
    current_impl = lambda p : Implies(p, lzz_f(p))
    next_impl = lambda p : Implies(next_f(p),
                                   get_inf_dnf(opt, derivator, bound, lzz_f(p)))
    and_not_inf = lambda p : And(p,
                                 Not(get_inf_dnf(opt, derivator, bound, lzz_f(p))))

    return And([And(list(map(current_impl, preds_list))),
                And(list(map(next_impl, preds_list))),
                Or(list(map(and_not_inf, preds_list)))])


def _get_lzz_out(opt, derivator, preds_list, next_f, lzz_f):
    bound = None
    current_impl = lambda p : Implies(p, get_ivinf_dnf(opt, derivator, bound, lzz_f(p)))
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
                 explicit_encoding = False,
                 lzz_opt = LzzOpt()):
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
        self.lzz_opt = lzz_opt

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
        self.quantified_ts = quantified_ts

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
            self.pred_map = {}
            build_preds_rec(self.preds, 0, self.pred_map)
            self.pred_vars_f = lambda x : self.pred_map[x]


    def get_ts_ia(self, use_simplified_ia=False):
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
                                         self.options.add_init_prop_predicates,
                                         use_simplified_ia)

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
          - List of abstraction polynomials (to be used in verification)
        """
        new_trans = self._get_trans_enc()
        new_init = And([self.init, self.invar])
        new_prop = self.safe

        preds_for_ia = _get_preds_ia_list(self.poly)
        ts_vars = self.vars
        ts_next = self.next_f

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
        return DecompositionEncoder._get_dyn_sys_enc(self.dyn_sys,
                                                     self.next_f, self.lzz_f,
                                                     self.poly, self.preds,
                                                     self.invar,
                                                     self.options,
                                                     self.stats_stream)

    @staticmethod
    def _get_dyn_sys_enc(dyn_sys,next_f,lzz_f,poly,preds,invar,
                         options,stats_stream):
        """
        sys: dynamical system
        """
        logger = logging.getLogger(__name__)
        logger.debug("Encoding transition using lzz...")

        sys = dyn_sys.get_renamed(lzz_f)
        derivator = sys.get_derivator()

        if (not stats_stream is None):
            print_abs_stats(stats_stream, derivator, poly)

        if (len(preds) > 0 and len(sys._states) > 0):
            if (not options.explicit_encoding):
                lzz_in = _get_lzz_in(options.lzz_opt, derivator, preds,
                                     next_f, lzz_f)

                lzz_out = _get_lzz_out(options.lzz_opt, derivator, preds,
                                       next_f, lzz_f)

                lzz_encoding = Or(lzz_in, lzz_out)
            else:
                lzz_encoding = _get_explicit_encoding(derivator,
                                                      poly,
                                                      next_f,
                                                      lzz_f)
        else:
            # corner case
            lzz_encoding = TRUE()

        # frame condition for the time-independent parameters
        fc_list = [Equals(var, next_f(var)) for var in sys.inputs()]

        if (len(fc_list) == 0):
            fc = TRUE()
        else:
            fc = And(fc_list)

        res = And([_get_neigh_encoding(poly, next_f),
                   invar,
                   next_f(invar),
                   fc,
                   lzz_encoding])

        debug_print_max_degree(logger, lzz_encoding)
        logger.debug("Encoded transition using lzz...")

        return res

# EOC DecompositionEncoder

class DecompositionEncoderHA:

    def __init__(self, env, ha, poly, ha_prop,
                 options = DecompositionOptions(),
                 stats_stream = None):
        logger = logging.getLogger(__name__)

        self.env = env
        self.ha = ha
        self.options = options

        # TODO: add implementation for initial predicates
        self.poly = poly
        self.poly = get_unique_poly_list(self.poly)
        logger.debug("Total of polynomials %d" % len(self.poly))

        self.preds = _get_preds_list(self.poly)

        self.ha_prop = ha_prop
        self.stats_stream = stats_stream

        # Declare the variables
        def _get_locs(env, ha):
            loc_vars = {}
            for loc in ha._locations:
                loc_name = "loc_%s" % str(loc)
                loc_var = FormulaHelper.get_fresh_var_name(env.formula_manager, loc_name)
                loc_vars[loc] = loc_var
            return loc_vars

        self.loc_vars_map = _get_locs(env, ha)
        self.disc_vars = [var for var in ha._disc_vars]
        self.disc_vars += [v for (k,v) in self.loc_vars_map.items()]
        self.cont_vars = [var for var in ha._cont_vars]
        self.vars = self.disc_vars + self.cont_vars

        self.next_f = lambda x : partial(FormulaHelper.rename_formula,
                                         env = env,
                                         vars = self.vars,
                                         suffix = "_next")(formula=x)
        self.lzz_f = lambda x : partial(FormulaHelper.rename_formula,
                                        env = env,
                                        vars = self.cont_vars,
                                        suffix = "_lzz")(formula=x)


    def get_ts_ia(self):
        """
        Get the implicit abstraction encoding for the hybrid automaton.
        """

        safe = self.ha_prop.global_prop
        for loc, loc_prop in self.ha_prop.prop_by_loc.items():
            safe = And(safe, Implies(self.loc_vars_map[loc], loc_prop))

        # Invar
        # - exactly one location
        # - invar for every location
        one_loc = ExactlyOne([v for (k,v) in self.loc_vars_map.items()])
        new_invar = one_loc
        for (q,loc) in self.ha._locations.items():
            new_invar = And(new_invar,
                            Implies(self.loc_vars_map[q], loc.invar))

        # Init
        # - init for every location
        new_init = new_invar
        for q,init in self.ha._init.items():
            new_init = And(new_init, Implies(self.loc_vars_map[q], init))

        # Trans_disc
        trans_list_disc = []
        for q, edges in self.ha._edges.items():
            for edge in edges:
                trans_list_disc.append(And([self.loc_vars_map[q],
                                            self.next_f(self.loc_vars_map[edge.dst]),
                                            edge.trans]))
        # Cont_trans
        trans_list_cont = []
        for q, loc in self.ha._locations.items():

            loc_invar = self.ha._locations[q].invar
            lzz_loc = DecompositionEncoder._get_dyn_sys_enc(loc.vector_field,
                                                            self.next_f,
                                                            self.lzz_f,
                                                            self.poly,
                                                            self.preds,
                                                            loc_invar,
                                                            self.options,
                                                            self.stats_stream)

            trans_list_cont.append(And([self.loc_vars_map[q],
                                        self.next_f(self.loc_vars_map[q]),
                                        lzz_loc]))

        # Add the self transition in the abstract space
        #
        # The semialgebraic decomposition encodes a transition system without a self
        # transition ("s1 -> [x' = f(x) & (s1 | s1)] s1" always holds)
        #
        # This is not a problem when we prove invariance of a dynamical system, but
        # we need the self transition in the encoding of the hybrid automaton.
        #
        # This is because we need to check what happens in the whole abstract state
        # s1 due to the continuous transition.
        #
        # fc_p = for p in preds. p(x) & p(x')
        # This is abstracted later
        #
        fc_p = And([Iff(p, self.next_f(p)) for p in _get_preds_ia_list(self.poly)])
        trans_list_cont.append(fc_p)

        # keep te discrete transition relation concrete
        invar_trans = And(new_invar, self.next_f(new_invar))
        # fc_loc = And([Iff(v, self.next_f(v)) for (k,v) in self.loc_vars_map.items()])
        fc_loc = And([EqualsOrIff(v, self.next_f(v)) for v in self.disc_vars])

        ts_disc = And(invar_trans, Or(trans_list_disc))
        ts = TS(self.env, self.vars, self.next_f, new_init,
                And([invar_trans,
                     fc_loc,
                     Or(trans_list_cont)]))

        preds_for_ia = _get_preds_ia_list(self.poly)
        # Make the discrete state concrete
        for var in self.disc_vars:
            preds_for_ia.append(var)

        enc = ImplicitAbstractionEncoder(ts,
                                         safe,
                                         preds_for_ia,
                                         self.env,
                                         self.options.rewrite_init,
                                         self.options.rewrite_property,
                                         self.options.add_init_prop_predicates,
                                         True,
                                         ts_disc)
        ts = enc.get_ts_abstract()
        new_prop = enc.get_prop_abstract()
        preds_for_ia = enc.get_predicates()
        return (ts, new_prop, preds_for_ia)


# EOC DecompositionEncoderHA

