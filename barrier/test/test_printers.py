import unittest


from pysmt.typing import (REAL, INT, BOOL)
from pysmt.shortcuts import ( Not, Equals, Div,
        Int, Symbol, Implies, GE, Times, Real, ForAll, Exists, And, Plus, LE )

from barrier.test import TestCase
from barrier.printers import ( QepcadPrinter, PysmtToQepcadPrinter)

class testprint(TestCase):
    def test_printer_1(self):
        #Test case 1
        case1 = [ "[Test 1]", "\n(x1,x2)", "\n0\n"]
        x1, x2 = [Symbol("x%s" % (i+1), REAL) for i in range(2)] 
        formula = Implies( GE(x1+x2,x2), GE(x1, x2))
        f = open("FormulasQepcad.txt",'w')
        for s in case1:
            f.write(s)
        f.close()  
        res = PysmtToQepcadPrinter(formula)

    def test_printer_2(self):       
        """Test case 2 with integers"""
        case2 = [ "\n[Test 2:integers]", "\n(x1,x2)", "\n0\n"]
        x1, x2 = [Symbol("x%s" % (i+1), REAL) for i in range(2)] 
        formula = Implies( GE(x1+x2,Real(2)*x2), GE(x1,Real(-1)*x2))
        f = open("FormulasQepcad.txt",'w') 
        for s in case2:
            f.write(s)
        f.close()  
        res = PysmtToQepcadPrinter(formula)

    def test_printer_3(self):       
        """Test case 3 with reals"""
        case3 = [ "\n[Test 3: reals]", "\n(x1,x2)", "\n0\n"]
        x1, x2 = [Symbol("x%s" % (i+1), REAL) for i in range(2)] 
        formula = ForAll([x1,x2],Implies( GE(x1+x2,Real(3.5)*x2), GE(x1,Real(24.6)*x2)))
        f = open("FormulasQepcad.txt",'w') 
        for s in case3:
            f.write(s)
        f.close()  
        res = PysmtToQepcadPrinter(formula)
    
    def test_printer_4(self):
        """Test case 4 : quantifiers succession"""
        case = [ "\n[Test 4: quantifiers]", "\n(x1,x2)", "\n0\n"]
        x1, x2 = [Symbol("x%s" % (i+1), REAL) for i in range(2)] 
        formula = ForAll([x1],Exists([x2],Implies( GE(x1+x2,Real(3.5)*x2), GE(x1,Real(24.6)*x2))))
        f = open("FormulasQepcad.txt",'w') 
        for s in case:
            f.write(s)
        f.close()  
        res = PysmtToQepcadPrinter(formula)


    def test_printer_5(self):
        """Test case 5 : testing =""" 
        case = [ "\n[Test 5: = ]", "\n(x2)", "\n0\n"]
        x2 = Symbol("x2", REAL)
        formula = Equals(x2,Real(3))
        f = open("FormulasQepcad.txt",'w') 
        for s in case:
            f.write(s)
        f.close()
        res = PysmtToQepcadPrinter(formula)


     
    def test_printer_6(self):
        """Test case 6 : testing not""" 
        case = [ "\n[Test 6: ~ ]", "\n(A)", "\n0\n"]
        A = Symbol("A", BOOL)
        formula = Not(A)
        f = open("FormulasQepcad.txt",'w') 
        for s in case:
            f.write(s)
        f.close()
        res = PysmtToQepcadPrinter(formula)


    def test_printer_7(self):
        """Test case 7 : testing /=""" 
        case = [ "\n[Test 7: /= ]", "\n(x2)", "\n0\n"]
        x2 = Symbol("x2", REAL)
        formula = Not(Equals(x2,Real(3)))
        f = open("FormulasQepcad.txt",'w') 
        for s in case:
            f.write(s)
        f.close()
        res = PysmtToQepcadPrinter(formula)


    def test_printer_8(self):
        """Test case 8 : testing div""" 
        case = [ "\n[Test 8: / ]", "\n(x2)", "\n0\n"]
        x2 = Symbol("x2", REAL)
        formula = Div(x2,Real(3))
        formula = Div(Real(4),Real(5))

        f = open("FormulasQepcad.txt",'w') 
        for s in case:
            f.write(s)
        f.close()
        res = PysmtToQepcadPrinter(formula)

    def test_printer_9(self):
        """Test case 8 : testing boolean connectives: AND,OR, IMPLIES,
        IFF, NOT
        """ 
        case = [ "\n[Test 9: bool connections ]", "\n(x1,x2)", "\n0\n"]
        x2 = Symbol("x2", REAL)
        x1 = Symbol("x1",REAL)
        formula_1 = LE(x2,Real(3))
        formula_2 = GE(x1,Real(5))
        formula_3 = Equals(Plus(x1,x2),Real(14))
        formula = And(formula_1,Implies(formula_3,formula_2))
        f = open("FormulasQepcad.txt",'w') 
        for s in case:
            f.write(s)
        f.close()
        res = PysmtToQepcadPrinter(formula)
