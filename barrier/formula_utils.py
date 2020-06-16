"""Helper functions, to understand where to put them.

TODO: memoization needs to be aware of the prefix
"""

from pysmt import shortcuts
from pysmt.shortcuts import Symbol, substitute

import pysmt.typing as types
from pysmt.exceptions import UndefinedSymbolError


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
