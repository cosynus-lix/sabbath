# Dumb dnf converter

from pysmt.simplifier import BddSimplifier

class BddDNFSimplifier(BddSimplifier):
    def __init__(self, env=None, static_ordering=None, bool_abstraction=True):
        BddSimplifier.__init__(self, env=env,
                               static_ordering=static_ordering,
                               bool_abstraction=True)

        self.dnf = True

    def abstract_and_simplify(self, formula):
        abs_formula = self.walk(formula)
        bdd_formula = self.convert(abs_formula)

        # try:
        #     import repycudd

        import repycudd
        if (self.dnf):
            # build DNF using cubes
            m = self.s.ddmanager
            dnf = m.One()
            for cube in repycudd.ForeachCubeIterator(m, bdd_formula):
                bdd_cube = m.Zero()
                for i in cube:
                    if i == 1:
                        new_cube = m.Or(bdd_cube, m.IthVar(i))
                        bdd_cube = new_cube
            bdd_formula = dnf

        abs_res = self.back(bdd_formula)
        res = abs_res.substitute(self.ba_map)
        return res

        # except:
        #     raise Exception("Cannot load BDD package")

class DNFConverter(object):
    def get_dnf(self, formula):
        """
        Returns a DNF representation of formula
        """
        try:
            import repycudd
        except:
            raise Exception("Cannot load BDD Package")

        s = BddDNFSimplifier(bool_abstraction=True)
        simplified_formula = s.simplify(formula)
        return simplified_formula
