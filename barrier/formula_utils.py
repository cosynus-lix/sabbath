"""Helper functions, to understand where to put them.

TODO: memoization needs to be aware of the prefix
"""

from pysmt import shortcuts
from pysmt.shortcuts import Symbol, substitute

import pysmt.typing as types
from pysmt.exceptions import UndefinedSymbolError
from pysmt.walkers import DagWalker
from pysmt.walkers import handles
import pysmt.operators as op


class FormulaHelper:
    def __init__(self,env):
        self.env = env
        self.time_memo = {}

    @staticmethod
    def get_fresh_var_name(mgr, var_name, typename=types.BOOL):
        base_name = var_name + "_%d"
        return mgr.new_fresh_symbol(typename, base=base_name)

    @staticmethod
    def get_new_var(var, mgr, old2new_map, prefix, suffix, type=None):
        """Returns a variable named as
        <prefix>_var_<suffix> of the same type of var.

        If the variable does not exists it is created from scratch
        (so, do NOT expect a fresh variable here)
        """
        assert var.is_symbol()
        base = "%s%s%s" % (prefix, var.symbol_name(), suffix)
        try:
            new_symbol = mgr.get_symbol(base)
        except UndefinedSymbolError as e:
            new_symbol = Symbol(base,
                                var.symbol_type() if type is None else type)
            assert new_symbol != None
        if None != old2new_map:
            old2new_map[var] = new_symbol

        if not type is None:
            assert(new_symbol.symbol_type() == type)

        return new_symbol

    @staticmethod
    def get_new_variables(vars, mgr, old2new_map, prefix, suffix, type=None):
        """As get_new_var for a list of variables"""
        var_list = []
        for v in vars:
            assert v.is_symbol()
            new_symbol = FormulaHelper.get_new_var(v, mgr, old2new_map, prefix, suffix, type)
            var_list.append(new_symbol)
        return frozenset(var_list)

    @staticmethod
    def rename_formula(env, vars, suffix, formula, type=None):
        """Given a formula returns the same formula where all the variables
        in vars are renamed to var_ + suffix.
        """
        symb_map = {}
        FormulaHelper.get_new_variables(vars, env.formula_manager, symb_map, "", suffix, type)

        sub_formula = substitute(formula, symb_map)
        return sub_formula

    # stateful methods (used for memo)

    def get_formula_at_i(self, vars, formula, i, prefix = "bmc_"):
        """Change formula replacing every variable var in vars with a variable
        named <prefix>_var_i and every variable var_next with a
        variable named <prefix>_var_j, where j is i+1.

        Example for i = 0, prefix = bmc_

        Input: (v & v_next) | p
        Output: (bmc_v_0 & bmc_v_1) | bmc_p_0
        """


        def get_next_var(var, mgr):
            """Given a variable returns the correspondent variable with the next suffix.
            It is used when describing transition relations (over var and var_next)
            """
            return FormulaHelper.get_new_var(var, mgr, None, "", "_next")

        if i in self.time_memo:
            time_i_map = self.time_memo[i]
        else:
            time_i_map = {}

            FormulaHelper.get_new_variables(vars,
                                            self.env.formula_manager,
                                            time_i_map,
                                            prefix,
                                            "_%d" % i)

            app_map = {}
            FormulaHelper.get_new_variables(vars,
                                            self.env.formula_manager,
                                            app_map,
                                            prefix,
                                            "_%d" % (i+1))
            for k,v in app_map.iteritems():
                next_var = FormulaHelper.get_next_var(k, self.env.formula_manager)
                time_i_map[next_var] = v
            app_map = None

            self.time_memo[i] = time_i_map

        f_at_i = substitute(formula, time_i_map)
        return f_at_i

    def get_next_formula(self, vars, formula):
        """Given a formula returns the same formula where all the variables
        in vars are renamed to var_next"""
        return FormulaHelper.rename_formula(self.env.formula_manager,
                                            vars, "_next", formula,
                                            type=None)

# EOC FormulaHelper

class PredicateExtractor(DagWalker):
    @staticmethod
    def extract_predicates(formula,env):
        pe = PredicateExtractor(env)
        pe.add_predicates_from(formula)
        return pe.get_predicates()

    def __init__(self, env=None):
        DagWalker.__init__(self, env=env)
        self.manager = self.env.formula_manager
        self._predicates = set()

    def add_predicates_from(self, formula):
        self.walk(formula)

    def get_predicates(self):
        return self._predicates

    @handles(op.AND, op.OR, op.IFF, op.NOT, op.IMPLIES)
    def walk_prop_op(self, formula, args, **kwargs):
        return True

    def walk_symbol(self, formula, args, **kwargs):
        if (formula.symbol_type() == types.BOOL):
            self._predicates.add(formula)
        return True

    @handles(op.EQUALS, op.LE, op.LT, op.FORALL, op.EXISTS)
    def walk_predicates(self, formula, args, **kwargs):
        self._predicates.add(formula)
        return True

    @handles(op.PLUS, op.TIMES, op.POW, op.MINUS, op.DIV, op.TOREAL)
    def walk_operators(self, formula, args, **kwargs):
        return True

    def walk_ite(self, formula, args, **kwargs):
        raise NotImplementedError

    @handles(op.BV_AND,op.BV_NOT,op.BV_NEG,op.BV_OR)
    @handles(op.BV_XOR,op.BV_ADD,op.BV_MUL,op.BV_UDIV)
    @handles(op.BV_UREM,op.BV_ULT,op.BV_ULE,op.BV_EXTRACT)
    @handles(op.BV_ROR,op.BV_ROL,op.BV_SEXT,op.BV_ZEXT)
    @handles(op.BV_CONCAT,op.BV_LSHL,op.BV_LSHR,op.BV_SUB)
    @handles(op.BV_SLT,op.BV_SLE,op.BV_COMP,op.BV_SDIV)
    @handles(op.BV_SREM,op.BV_ASHR,op.STR_LENGTH,op.STR_CONCAT)
    @handles(op.STR_CHARAT,op.STR_INDEXOF,op.STR_REPLACE,op.STR_TO_INT)
    @handles(op.INT_TO_STR,op.BV_TONATURAL,op.ARRAY_SELECT,op.ARRAY_STORE)
    @handles(op.ARRAY_VALUE,op.STR_SUBSTR,op.STR_CONTAINS,op.STR_PREFIXOF)
    @handles(op.STR_SUFFIXOF)
    def walk_not_supported(self, formula, args, **kwargs):
        raise NotImplementedError

    def walk_function(self, formula, args, **kwargs):
        raise NotImplementedError

    @handles(op.REAL_CONSTANT, op.INT_CONSTANT, op.BOOL_CONSTANT)
    @handles(op.BV_CONSTANT, op.STR_CONSTANT, op.ALGEBRAIC_CONSTANT)
    def walk_identity(self, formula, args, **kwargs):
        return formula


# EOC PredicateExtractor
