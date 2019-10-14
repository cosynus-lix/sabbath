# -*- coding: utf-8 -*-
"""
Printers
- from pysmt to qepcad
-from qepcad to pysmt
"""

from pysmt.printers import SmtPrinter

class QepcadPrinter(SmtPrinter):
    
    def walk_and(self, formula): return self.walk_nary(formula, "/\ ")
    def walk_or(self, formula): return self.walk_nary(formula, "\/")
    def walk_not(self, formula): return self.walk_nary(formula, "~")
    def walk_implies(self, formula): return self.walk_nary(formula, "==>")
    def walk_iff(self, formula): return self.walk_nary(formula, "<==>")
    def walk_plus(self, formula): return self.walk_nary(formula, "+")
    def walk_minus(self, formula): return self.walk_nary(formula, "-")
    def walk_times(self, formula): return self.walk_nary(formula, " ")
    def walk_equals(self, formula): return self.walk_nary(formula, "=")
    def walk_le(self, formula): return self.walk_nary(formula, "<=")
    def walk_lt(self, formula): return self.walk_nary(formula, "<")
    def walk_div(self, formula): return self.walk_nary(formula, "/")
    def walk_pow(self, formula): return self.walk_nary(formula, "^")
    
    
    def walk_forall(self, formula):
        return self._walk_quantifier("A", formula)

    def walk_exists(self, formula):
        return self._walk_quantifier("E", formula)
    
    
    def printer(self,formula):
        self.write("[")
        self.walk(formula)
        self.write("].")
    
    
def PsymtToQepcadPrinter(formula):
    test = open("FormulasQepcad.txt",'w')
    QepcadPrinter.printer(formula) 
    test.close()
    return test

    
        
        
        
        
    
