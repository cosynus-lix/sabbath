# Representation of a transition system
# Mainly used to export in vmt.
#

import pysmt.smtlib.commands as smtcmd
from pysmt.smtlib.script import smtlibscript_from_formula
from pysmt.smtlib.script import SmtLibScript, SmtLibCommand
from pysmt.logics import QF_NRA
from pysmt.environment import get_env
from pysmt.smtlib.annotations import Annotations
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter, quote
from pysmt.smtlib.parser import SmtLibParser

class TS:
    def __init__(self, state_vars, next_f, init, trans):
        self.init = init
        self.next_f = next_f
        self.trans = trans
        self.state_vars = set(state_vars)


    def to_vmt(self, outstream, safety_property):
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
                    cmds.append(SmtLibCommand(name=smtcmd.DECLARE_FUN, args=[symbol]))

                    if symbol in self.state_vars:
                        nv_name = "nvdef_%d" % nvcount
                        nvcount = nvcount + 1

                        next_s = self.next_f(symbol)
                        cmds.append(SmtLibCommand(name=smtcmd.DECLARE_FUN, args=[next_s]))
                        visited.add(next_s)

                        cmds.append("(define-fun %s () %s (! %s :next %s))" %
                                    (nv_name, symbol.symbol_type(),
                                     symbol, self.next_f(symbol)))

        # Assert formulas
        for cmd in cmds:
            if isinstance(cmd, str):
                outstream.write(cmd)
            else:
                cmd.serialize(printer=printer)
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


    @staticmethod
    def from_vmt(instream, env=get_env()):
        parser = SmtLibParser(env)
        script = parser.get_script(instream)

        # read next
        state_vars = []
        next_f_map = {}
        state_vars = script.annotations.all_annotated_formulae("next")
        for s in state_vars:
            next_vars = script.annotations.annotations(s)["next"]
            assert((not next_vars is None) and len(next_vars) == 1)
            next_var = next(iter(next_vars))
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

        return (TS(state_vars, next_f, init_f, trans_f), safe_f)

    @staticmethod
    def dump_predicates(outstream, predicates):
        """ Print the list of predicates
        """
        printer = SmtDagPrinter(outstream)
        for p in predicates:
            printer.printer(p)
            outstream.write("\n")
        outstream.flush()
