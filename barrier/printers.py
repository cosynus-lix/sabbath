# -*- coding: utf-8 -*-
"""
Printers
- from pysmt to qepcad
-from qepcad to pysmt
"""

from pysmt.smtlib.printers import SmtPrinter
from pysmt.typing import BOOL 
from pysmt.oracles import QuantifierOracle
from pysmt.operators import BOOL_CONNECTIVES

class QepcadPrinter(SmtPrinter):
    
    def walk_nary(self, formula, operator):
        assert len(formula.args()) > 0 
        for i in range(len(formula.args())-1):
            yield formula.args()[i]
            self.write( " %s " %operator)
            yield formula.args()[i+1]
            self.write(" ")

    
    def walk_bool_connect(self,formula,operator):
        assert len(formula.args()) > 0 
        for i in range(len(formula.args())-1):
            self.write("[ ")
            yield formula.args()[i]
            self.write(" ]"+" %s [ " %operator)
            yield formula.args()[i+1]
            self.write(" ]")
            
        

    def walk_and(self, formula): return self.walk_bool_connect(formula, "/\ ")
    def walk_or(self, formula): return self.walk_bool_connect(formula, "\/")
    def walk_implies(self, formula): return self.walk_bool_connect(formula, "==>")
    def walk_iff(self, formula): return self.walk_bool_connect(formula, "<==>")
    
    def walk_plus(self, formula): return self.walk_nary(formula, "+")
    def walk_minus(self, formula): return self.walk_nary(formula, "-")
    def walk_times(self, formula): return self.walk_nary(formula, " ")
    def walk_equals(self, formula): return self.walk_nary(formula, "=")
    def walk_le(self, formula): return self.walk_nary(formula, "<=")
    def walk_lt(self, formula): return self.walk_nary(formula, "<")
    def walk_pow(self, formula): return self.walk_nary(formula, "^") 
    def walk_div(self, formula): return self.walk_nary(formula, "/")

    def walk_not(self, formula): 
        if formula.arg(0).is_equals() is False:
            for s in formula.args():
                self.write("~[")
                yield s
                self.write("]")
        else:
            u,v = formula.arg(0).args()
            yield u
            self.write("/=")
            yield v
            
    
    def walk_real_constant(self, formula, **kwargs):
        if formula.constant_value() < 0:
            template = "(- %s)"
        else:
            template= "%s"

        (n,d) = abs(formula.constant_value().numerator), \
                formula.constant_value().denominator
        
        if d != 1:
            res = template % ( str(n) +  "/" + str(d) )
        else:
            res =  template % str(n)

        self.write(res)
    
    def walk_forall(self, formula):
        return self._walk_quantifier("A", formula)

    def walk_exists(self, formula):
        return self._walk_quantifier("E", formula)
    
    def _walk_quantifier(self,operator,formula):
        assert len(formula.quantifier_vars()) > 0

        for s in formula.quantifier_vars():
            self.write("(%s " % operator)
            yield s
            self.write(" ) ")
        
        if formula.arg(0).is_quantifier() is False:
           self.write("[")
        yield formula.arg(0)
        

    def printer(self,formula):
        q = QuantifierOracle()
        if q.is_qf(formula):
            self.write("[ ")
        self.walk(formula)
        self.write("].")
    
    
def PysmtToQepcadPrinter(formula):
    strm = open("FormulasQepcad.txt",'a')
    res = QepcadPrinter(strm)
    res.printer(formula)
    strm.write("\nfinish.")
    strm.close()
    return res

    
        
        
        
        
    
