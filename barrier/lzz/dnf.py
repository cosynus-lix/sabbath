# Dumb dnf converter

from pysmt.simplifier import BddSimplifier

from pysmt.shortcuts import (
    Not, And, Or, TRUE, FALSE
)

class BddDNFSimplifier(BddSimplifier):
    def __init__(self, env=None, static_ordering=None, bool_abstraction=True):
        BddSimplifier.__init__(self, env=env,
                               static_ordering=static_ordering,
                               bool_abstraction=True)

        self.dnf = True

    def abstract_and_simplify(self, formula):
        abs_formula = self.walk(formula)


        bdd_formula = self.convert(abs_formula)

        try:
            import repycudd

            if (self.dnf):
                # build DNF using cubes
                m = self.s.ddmanager
                repycudd.set_iter_meth(0)


                abs_res = FALSE()
                for cube in repycudd.ForeachCubeIterator(m, bdd_formula):
                    print(repycudd.cube_tuple_to_str(cube))

                    bdd_cube = TRUE()

                    i = -1
                    for cube in cube:
                        i = i + 1
                        var = self.back(m.IthVar(i))

                        if cube == 1:
                            bdd_cube = And(bdd_cube, var)
                        elif cube == 0:
                            bdd_cube = And(bdd_cube, Not(var))
                    abs_res = Or(abs_res, bdd_cube)
            else:
                abs_res = self.back(bdd_formula)

            res = abs_res.substitute(self.ba_map)
            return res

        except:
            raise Exception("Cannot load BDD package")

class DNFConverter(object):
    def get_dnf(self, formula):
        """
        Returns a DNF representation of formula
        """
        try:
            import repycudd
        except:
            raise Exception("Cannot load BDD Package")

        # Very expensive DNF-ization, enumerates all the models
        # Equivalent DNF is the one ok for LZZ
        s = BddDNFSimplifier(bool_abstraction=True)
        simplified_formula = s.simplify(formula)
        return simplified_formula
