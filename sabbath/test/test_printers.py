import unittest


from pysmt.typing import (REAL, INT, BOOL)
from pysmt.shortcuts import ( Not, Equals, Div,
        Int, Symbol, Implies, GE, Times, Real, ForAll, Exists, And, Plus, LE, TRUE, FALSE )

from sabbath.test import TestCase
from sabbath.printers import ( QepcadPrinter, PysmtToQepcadPrinter)
import os

class testprint(TestCase):
    def tearDown(self):
        if os.path.exists("TestingFormulasQepcad.txt"):
            os.remove("TestingFormulasQepcad.txt")

    def test_printer_1(self):
        #Test case 1
        x1, x2 = [Symbol("x%s" % (i+1), REAL) for i in range(2)]
        formula = Implies( GE(x1+x2,x2), GE(x1, x2))
        PysmtToQepcadPrinter(formula,"TestingFormulasQepcad.txt")
        f = open("TestingFormulasQepcad.txt",'r')
        res = f.readline()
        expected = "[[x2<=x1+x2] ==> [x2<=x1]]."
        f.close()
        open("TestingFormulasQepcad.txt",'w').close()
        self.assertEqual(expected,res.strip())

    def test_printer_2(self):
        """Test case 2 with integers"""
        x1, x2 = [Symbol("x%s" % (i+1), REAL) for i in range(2)]
        formula = Implies( GE(x1+x2,Real(2)*x2), GE(x1,Real(-1)*x2))
        PysmtToQepcadPrinter(formula,"TestingFormulasQepcad.txt")
        f = open("TestingFormulasQepcad.txt",'r')
        res = f.readline()
        expected = "[[2 x2<=x1+x2] ==> [(- 1) x2<=x1]]."
        open("TestingFormulasQepcad.txt",'w').close()
        self.assertEqual(expected,res.strip())

    def test_printer_3(self):
        """Test case 3 with reals"""
        x1, x2 = [Symbol("x%s" % (i+1), REAL) for i in range(2)]
        formula = ForAll([x1,x2],Implies( GE(x1+x2,Real(3.5)*x2), GE(x1,Real(24.6)*x2)))
        PysmtToQepcadPrinter(formula,"TestingFormulasQepcad.txt")
        f = open("TestingFormulasQepcad.txt",'r')
        res = f.readline()
        expected = "(A x1 ) (A x2 ) [[7/2 x2<=x1+x2] ==> [3462142213541069/140737488355328 x2<=x1]]."
        open("TestingFormulasQepcad.txt",'w').close()
        self.assertEqual(expected,res.strip())

    def test_printer_4(self):
        """Test case 4 : quantifiers succession"""
        x1, x2 = [Symbol("x%s" % (i+1), REAL) for i in range(2)]
        formula = ForAll([x1],Exists([x2],Implies( GE(x1+x2,Real(3.5)*x2), GE(x1,Real(24.6)*x2))))
        PysmtToQepcadPrinter(formula,"TestingFormulasQepcad.txt")
        f = open("TestingFormulasQepcad.txt",'r')
        res = f.readline()
        expected = "(A x1 ) (E x2 ) [[7/2 x2<=x1+x2] ==> [3462142213541069/140737488355328 x2<=x1]]."
        open("TestingFormulasQepcad.txt",'w').close()
        self.assertEqual(expected,res.strip())

    def test_printer_5(self):
        """Test case 5 : testing ="""
        x2 = Symbol("x2", REAL)
        formula = Equals(x2,Real(3))
        PysmtToQepcadPrinter(formula,"TestingFormulasQepcad.txt")
        f = open("TestingFormulasQepcad.txt",'r')
        res = f.readline()
        expected = "[x2=3]."
        open("TestingFormulasQepcad.txt",'w').close()
        self.assertEqual(expected,res.strip())



    def test_printer_6(self):
        """Test case 6 : testing not"""
        A = Symbol("A", BOOL)
        formula = Not(A)
        PysmtToQepcadPrinter(formula,"TestingFormulasQepcad.txt")
        f = open("TestingFormulasQepcad.txt",'r')
        res = f.readline()
        expected = "[~[A]]."
        open("TestingFormulasQepcad.txt",'w').close()
        self.assertEqual(expected,res.strip())


    def test_printer_7(self):
        """Test case 7 : testing /="""
        x2 = Symbol("x2", REAL)
        formula = Not(Equals(x2,Real(3)))
        PysmtToQepcadPrinter(formula,"TestingFormulasQepcad.txt")
        f = open("TestingFormulasQepcad.txt",'r')
        res = f.readline()
        expected = "[x2/=3]."
        open("TestingFormulasQepcad.txt",'w').close()
        self.assertEqual(expected,res.strip())


    def test_printer_8(self):
        """Test case 8 : testing div"""
        x2 = Symbol("x2", REAL)
        formula = Div(x2,Real(3))
        PysmtToQepcadPrinter(formula,"TestingFormulasQepcad.txt")
        f = open("TestingFormulasQepcad.txt",'r')
        res = f.readline()
        expected = "[x2 1/3]."
        open("TestingFormulasQepcad.txt",'w').close()
        self.assertEqual(expected,res.strip())

    def test_printer_9(self):
        """Test case 9 : testing boolean connectives: AND,OR, IMPLIES,
        IFF, NOT
        """
        x2 = Symbol("x2", REAL)
        x1 = Symbol("x1",REAL)
        formula_1 = LE(x2,Real(3))
        formula_2 = GE(x1,Real(5))
        formula_3 = Equals(Plus(x1,x2),Real(14))
        formula = ForAll([x1,x2],And(formula_1,Implies(formula_3,formula_2)))
        PysmtToQepcadPrinter(formula,"TestingFormulasQepcad.txt")
        f = open("TestingFormulasQepcad.txt",'r')
        res = f.readline()
        expected = "(A x1 ) (A x2 ) [[x2<=3] /\  [[x1+x2=14] ==> [5<=x1]]]."
        open("TestingFormulasQepcad.txt",'w').close()
        self.assertEqual(expected,res.strip())

    def test_printer_10(self):
        """Test case 10 : testing boolean constant(True,False)
        """
        x2 = Symbol("x2", REAL)
        x1 = Symbol("x1",REAL)
        formula_1 = LE(x2,Real(3))
        formula_2 = GE(x1,Real(5))
        formula_3 = Equals(Plus(x1,x2),Real(14))
        formula = ForAll([x1,x2],And(TRUE(), FALSE(),formula_1,Implies(formula_3,formula_2)))
        PysmtToQepcadPrinter(formula,"TestingFormulasQepcad.txt")
        f = open("TestingFormulasQepcad.txt",'r')
        res = f.readline()
        expected = "(A x1 ) (A x2 ) [[x2<=3] /\  [[x1+x2=14] ==> [5<=x1]]]."
        open("TestingFormulasQepcad.txt",'w').close()
        self.assertEqual(expected,res.strip())


    def test_printer_11(self):
        """Test case 11 : testing x*(x+2*y)
        """
        x2 = Symbol("x2", REAL)
        x1 = Symbol("x1",REAL)
        formula = (x2+Real(3)*x1)*(Real(3)*x1-Real(5))*x2
        PysmtToQepcadPrinter(formula,"TestingFormulasQepcad.txt")
        f = open("TestingFormulasQepcad.txt",'r')
        res = f.readline()
        expected = "[((x2+3 x1) (3 x1-5)) x2]."
        open("TestingFormulasQepcad.txt",'w').close()
        self.assertEqual(expected,res.strip())
