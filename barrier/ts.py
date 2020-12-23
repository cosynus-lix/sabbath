# Representation of a transition system
# Mainly used to export in vmt.
#

from functools import partial
from io import StringIO
import logging

import pysmt.smtlib.commands as smtcmd
from pysmt.smtlib.script import smtlibscript_from_formula
from pysmt.smtlib.script import SmtLibScript, SmtLibCommand
from pysmt.logics import QF_NRA
from pysmt.environment import get_env
from pysmt.smtlib.annotations import Annotations
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter, quote
from pysmt.smtlib.parser import SmtLibParser, get_formula
from pysmt.shortcuts import (
    TRUE, FALSE, Iff, And, Or, Not,
    EqualsOrIff,
    Symbol, substitute,
)

from barrier.formula_utils import FormulaHelper, PredicateExtractor

class TS:
    """
    Transition system representation using first-order-logic formulas.
    """
    def __init__(self, env, state_vars, next_f, init, trans):
        self.env = env
        self.init = init
        self.next_f = next_f
        self.trans = trans
        self.state_vars = set(state_vars)

    def copy_ts(self):
        next_f_map = {}
        for v in self.state_vars:
            next_f_map[v] = self.next_f(v)

        next_f = lambda x : partial(substitute,
                                    subs = next_f_map)(formula = x)
        return TS(self.env, self.state_vars, next_f, self.init, self.trans)

    def to_vmt(self, outstream, safety_property):
        """
        Dump the transition system in VMT format
        """

        # compute next
        printer = SmtDagPrinter(outstream)
        cmds = []
        cmds.append(SmtLibCommand(name=smtcmd.SET_LOGIC,args=[QF_NRA]))

        # Declare all types
        for formula in [self.init, self.trans]:
            types = get_env().typeso.get_types(formula, custom_only=True)
            for type_ in types:
                cmds.append(SmtLibCommand(name=smtcmd.DECLARE_SORT, args=[type_.decl]))

        # Declare all variables
        nvcount=0
        visited = set()
        for formula in [self.init, self.trans]:
            deps = formula.get_free_variables()
            # Declare all variables
            for symbol in deps:
                if not symbol in visited:
                    visited.add(symbol)
                    assert symbol.is_symbol()
                    if not symbol in self.state_vars:
                        cmds.append(SmtLibCommand(name=smtcmd.DECLARE_FUN, args=[symbol]))

        for symbol in self.state_vars:
            cmds.append(SmtLibCommand(name=smtcmd.DECLARE_FUN, args=[symbol]))

            nv_name = "nvdef_%d" % nvcount
            nvcount = nvcount + 1
            next_s = self.next_f(symbol)

            cmds.append(SmtLibCommand(name=smtcmd.DECLARE_FUN, args=[next_s]))
            visited.add(next_s)

            cmds.append("(define-fun %s () %s (! %s :next %s))\n" %
                        (nv_name, symbol.symbol_type(),
                         symbol, self.next_f(symbol)))

        # Assert formulas
        for cmd in cmds:
            if isinstance(cmd, str):
                outstream.write(cmd)
            else:
                cmd.serialize(outstream=outstream)
            outstream.write("\n")

        def print_formula(outstream, printer, def_name, annotation, formula,
                          annotation_value = "true"):
            outstream.write("(define-fun %s () Bool (! " % def_name)
            printer.printer(formula)
            outstream.write(" :%s %s))\n" % (annotation,
                                             annotation_value))

        print_formula(outstream, printer, ".init", "init", self.init)
        print_formula(outstream, printer, ".trans", "trans", self.trans)
        print_formula(outstream, printer, ".invar-property", "invar-property",
                      safety_property, "0")
        outstream.flush()
        return

    def read_predicates(self, instream):
        """ read a list of predicates from an input stream
        """

        env = get_env()
        outstream = StringIO()
        self.to_vmt(outstream, TRUE())

        for predline in instream.readlines():
            # skip empty line and comments
            if predline.find(";;") >= 0:
                predline = predline[:predline.find(";;")]
            predine = predline.strip()
            if not predline:
                continue
            last_assert = "(assert %s)\n" % predline
            outstream.write(last_assert)
        outstream.seek(0)

        parser = SmtLibParser(env)
        script = parser.get_script(outstream)

        predicates = []
        for cmd in script.commands:
            if cmd.name == smtcmd.ASSERT:
                pred = cmd.args[0]
                predicates.append(pred)

        return predicates


    @staticmethod
    def from_vmt(instream, env=get_env()):
        """
        Parse a transition system from VMT
        """
        parser = SmtLibParser(env)
        script = parser.get_script(instream)

        # read next
        state_vars = []
        next_f_map = {}
        state_vars = script.annotations.all_annotated_formulae("next")

        for s in state_vars:
            next_vars_str_list = script.annotations.annotations(s)["next"]
            assert((not next_vars_str_list is None) and len(next_vars_str_list) == 1)
            next_var_str = next(iter(next_vars_str_list))
            next_var = Symbol(next_var_str, s.symbol_type())
            next_f_map[s] = next_var
        next_f = lambda f : next_f_map[f]


        def get_formula(script, label):
            formula = script.annotations.all_annotated_formulae(label)
            assert((not formula is None) and len(formula) == 1)
            return next(iter(formula))

        init_f = get_formula(script, "init")
        trans_f = get_formula(script, "trans")
        # May be more --- now ignore them
        safe_f = get_formula(script, "invar-property")

        return (TS(env, state_vars, next_f, init_f, trans_f), safe_f)

    @staticmethod
    def get_next_f(vars_list, env):
        next_f = lambda x : partial(FormulaHelper.rename_formula,
                                    env = env,
                                    vars = vars_list,
                                    suffix = "_next")(formula=x)
        return next_f


    @staticmethod
    def extend_next_f(env, state_vars, next_f, new_vars):
        next_f_map = {}
        for v in state_vars:
            next_f_map[v] = next_f(v)

        for new_var in new_vars:
            FormulaHelper.get_new_var(new_var, env.formula_manager,
                                      next_f_map, "", "_next")
        next_f = lambda x : partial(substitute,
                                    subs = next_f_map)(formula = x)
        return next_f

    def rewrite(self, prop, rewrite_init=False, rewrite_prop=False):
        """
        Rewrite the initial states and properties to ensure soundeness or
        add the predicates from init and prop.

        Rewriting of prop:
        new_prop = prop_var
        new_init = init and (prop_var <-> prop)
        new_trans = trans and (prop_var <-> prop) and (prop_var' <-> prop')

        Rewriting of init:

        init = reset
        new_prop = reset or prop
        new_trans = not(reset') and (reset -> init') and (!reset -> trans)
                  = not(reset') and (not reset or init') and (reset or trans)
        """
        new_vars = []

        if rewrite_prop:
            prop_var = FormulaHelper.get_fresh_var_name(self.env.formula_manager,
                                                        "new_prop")
            new_vars.append(prop_var)

        if rewrite_init:
            reset = FormulaHelper.get_fresh_var_name(self.env.formula_manager, "reset")
            new_vars.append(reset)


        self.next_f = TS.extend_next_f(self.env,
                                       self.state_vars,
                                       self.next_f,
                                       new_vars)
        for new_var in new_vars:
            self.state_vars.add(new_var)

        if rewrite_prop:
            new_prop = prop_var
            new_init = And(self.init, Iff(prop_var, prop))
            new_trans = And([self.trans,
                             Iff(prop_var, prop),
                             Iff(self.next_f(prop_var), self.next_f(prop))])

            prop = new_prop
            self.init = new_init
            self.trans = new_trans

        if rewrite_init:
            new_prop = Or(reset, prop)
            new_init = reset
            new_trans = And([Not(self.next_f(reset)),
                             Or(Not(reset), self.next_f(self.init)),
                             Or(reset, self.trans)])
            prop = new_prop
            self.init = new_init
            self.trans = new_trans


        return (prop, new_vars)


    @staticmethod
    def dump_predicates(outstream, predicates):
        """ Print the list of predicates to outstream
        """
        printer = SmtDagPrinter(outstream)
        for p in predicates:
            printer.printer(p)
            outstream.write("\n")
        outstream.flush()

# EOC TS


class ImplicitAbstractionEncoder():
    """
    Encode the implicit predicate abstraction as a transition system.
    """
    def __init__(self, ts_concrete, prop, predicates, env = get_env(),
                 rewrite_init=False, rewrite_prop=False,
                 add_init_prop_predicates = False,
                 use_simplified_encoding = False,
                 ts_to_keep_concrete = None):
        self.env = env
        self.ts_concrete = ts_concrete.copy_ts()
        self.prop = prop
        self.predicates = set(predicates)

        self.rewrite_init = rewrite_init
        self.rewrite_prop = rewrite_prop
        self.add_init_prop_predicates = add_init_prop_predicates

        self._ts_abstract = None
        self._prop_abstract = None

        if (not use_simplified_encoding):
            assert (ts_to_keep_concrete is None)
            (self._ts_abstract, self._prop_abstract) = self._build_ts_abstract(self.ts_concrete,
                                                                               self.prop,
                                                                               self.predicates,
                                                                               self.rewrite_init,
                                                                               self.rewrite_prop,
                                                                               self.add_init_prop_predicates)
        else:
            (self._ts_abstract, self._prop_abstract) = self._build_ts_abstract_simple(self.ts_concrete,
                                                                                      FALSE() if ts_to_keep_concrete is None else ts_to_keep_concrete,
                                                                                      self.prop,
                                                                                      self.predicates,
                                                                                      self.rewrite_init,
                                                                                      self.rewrite_prop,
                                                                                      self.add_init_prop_predicates)


    @staticmethod
    def _init_and_prop_pred_handling(env, ts, prop, predicates,
                                     rewrite_init, rewrite_property,
                                     add_init_prop_predicates):

        if (add_init_prop_predicates):
            prop_preds = PredicateExtractor.extract_predicates(prop, env)
            predicates.update(prop_preds)
            init_preds = PredicateExtractor.extract_predicates(ts.init, env)
            predicates.update(init_preds)

        if (rewrite_init or rewrite_property):
            (prop, new_preds) = ts.rewrite(prop, rewrite_init, rewrite_property)
            predicates.update(new_preds)

        return (prop, predicates)


    @staticmethod
    def get_eq(abs_f_map, predicates):
        """ EQ(V,V_abs) := \bigwedge_{p \in predicates}{p(V) <-> p(V_abs)}
        """
        iffs = []
        for p in predicates:
            iffs.append(EqualsOrIff(p, p.substitute(abs_f_map)))
        return And(iffs)


    def _build_ts_abstract(self, ts_concrete, prop, predicates,
                           rewrite_init, rewrite_prop,
                           add_init_prop_predicates):
        """
        TS := (V, Init(V), Trans(V,V'))
        P(V)
        predicates expressed over variables V

        The abstract system is:
        TS_abs := (V \cup V_abs,
                   Init(V) \land EQ(V,V_abs),
                   EQ(V,V_abs) \land
                   Trans(V_abs,V') \land
                   EQ(V',V_abs')
                  )

        P_abs := P(V_abs)
        """

        (prop, predicates) = (
            ImplicitAbstractionEncoder._init_and_prop_pred_handling(self.env,
                                                                    ts_concrete,
                                                                    prop,
                                                                    predicates,
                                                                    rewrite_init = rewrite_init,
                                                                    rewrite_property = rewrite_prop,
                                                                    add_init_prop_predicates = add_init_prop_predicates)
        )
        vars_concrete = list(ts_concrete.state_vars)


        # define the abstract variables
        # abs(v) = v_abs
        # abs(v_next) = v_abs_next
        abs_map = {}
        for var in vars_concrete:
            for symb in [var, ts_concrete.next_f(var)]:
                abs_symb = FormulaHelper.get_fresh_var_name(self.env.formula_manager,
                                                            "%s_abs" % symb.symbol_name(),
                                                            symb.symbol_type())
                abs_map[symb] = abs_symb
        abs_concrete_map = {v : abs_map[v] for v in vars_concrete}
        vars_abstract = [abs_map[v] for v in vars_concrete]
        state_vars = vars_concrete + vars_abstract

        # re-define next function
        # next(v) = v_next, next(v_abs) = v_abs_next
        next_map = {}
        for v in vars_concrete:
            next_map[v] = ts_concrete.next_f(v)
            next_map[abs_map[v]] = abs_map[ts_concrete.next_f(v)]
        next_f = lambda x : partial(substitute,
                                    subs = next_map)(formula = x)
        abs_concrete_map_next = {next_f(v) : abs_map[next_f(v)] for v in vars_concrete}

        eq_pred = ImplicitAbstractionEncoder.get_eq(abs_map, predicates)

        # Init(V) \land EQ(V,V_abs)
        init_abs = And(eq_pred, ts_concrete.init)

        # From T(V,V') to T(V_abs,V')
        trans_renamed = substitute(ts_concrete.trans, abs_concrete_map)
        # EQ(V,V_abs) \land EQ(V_abs',V') \land Trans(V_abs,V')
        trans_abs = And([eq_pred, next_f(eq_pred), trans_renamed])

        ts_abstract = TS(self.env, state_vars, next_f, init_abs, trans_abs)

        # From P(V) to P(V_abs)
        # prop_renamed = substitute(prop, abs_concrete_map)
        # Assume prop goes always with trans or init
        prop_abstract = substitute(prop, abs_concrete_map)

        # print("ABS ENCODING")
        # print("Init: " + init_abs.serialize())
        # print("Prop: " + prop_abstract.serialize())
        # print("trans: " + trans_abs.serialize())
        # print("Eqpred: " + eq_pred.serialize())
        # print("Eqpred: " + next_f(eq_pred).serialize())
        # print("END ABS ENCODING")

        return (ts_abstract, prop_abstract)


    def _build_ts_abstract_simple(self,
                                  ts_concrete,
                                  ts_to_keep_concrete,
                                  prop,
                                  predicates,
                                  rewrite_init,
                                  rewrite_prop,
                                  add_init_prop_predicates):
        """
        TS := (V, Init(V), Trans(V,V'))
        P(V)
        predicates expressed over variables V

        The of the abstract system is:
        TS_abs := (V \cup V_abs,
                   Init(V),
                   EQ(V,V_abs) \land
                   Trans(V_abs,V') \land
                  )
        P_abs := P(V)
        """

        # print("concrete")
        # print(ts_concrete.trans.serialize())

        # print("to keep concrete")
        # print(ts_to_keep_concrete.serialize())

        # print("predicates")
        # print(predicates)



        (prop, predicates) = (
            ImplicitAbstractionEncoder._init_and_prop_pred_handling(self.env,
                                                                    ts_concrete,
                                                                    prop,
                                                                    predicates,
                                                                    rewrite_init = rewrite_init,
                                                                    rewrite_property = rewrite_prop,
                                                                    add_init_prop_predicates = add_init_prop_predicates)
        )
        vars_concrete = list(ts_concrete.state_vars)

        # define the abstract variables
        # here they're used only as input, so no next
        # abs(v) = v_abs
        abs_map = {}
        for var in vars_concrete:
            for symb in [var]:
                abs_symb = FormulaHelper.get_fresh_var_name(self.env.formula_manager,
                                                            "%s_abs" % symb.symbol_name(),
                                                            symb.symbol_type())
                abs_map[symb] = abs_symb

        state_vars = vars_concrete

        # next(v) = v_next
        # No need for next of v_abs
        next_map = {}
        for v in vars_concrete:
            next_map[v] = ts_concrete.next_f(v)
        next_f = lambda x : partial(substitute,
                                    subs = next_map)(formula = x)

        # EQ(V,V_abs)
        eq_pred = ImplicitAbstractionEncoder.get_eq(abs_map, predicates)

        # Init(V)
        init_abs = ts_concrete.init

        # From T(V,V') to T(V_abs,V')
        rename_map = {v : abs_map[v] for v in vars_concrete}
        trans_renamed = substitute(ts_concrete.trans, rename_map)

        # DEBUG
        # print("Renamed")
        # print(And(eq_pred, trans_renamed).serialize())

        trans_abs = Or(ts_to_keep_concrete, And(eq_pred, trans_renamed))
        ts_abstract = TS(self.env, state_vars, next_f, init_abs, trans_abs)

        # Use the concrete prop
        prop_abstract = prop

        return (ts_abstract, prop_abstract)


    def get_ts_abstract(self):
        return self._ts_abstract

    def get_prop_abstract(self):
        return self._prop_abstract

    def get_predicates(self):
        return self.predicates

# EOC ImplicitAbstractionEncoder
