from sympy.polys.monomials import itermonomials
from sympy import Poly

def gen_template_sympy(get_new, vars_list, degree, min_degree):
    coefficients = []
    template = 0

    for l in itermonomials(vars_list, degree, min_degree):
        coeff = get_new()
        template = template + coeff * l
        coefficients.append(coeff)
    return (template, coefficients)

def make_positive_definite(get_new, prob, p, vars_list):
    def _make_positive_definite(get_new, p, vars_list):
        """
        Takes as input a polynomial p of degree 2*d and returns:
        1. the polynomial p' := p - f

        where f is a new polynomial: sum_{i = 1}^{n} sum_{j = 1}^{d} e_ij xi^2j
        with e_ij a list of new coefficients

        2. the list of polynomials g := [sum_{j = 1}^{d} e_1j - gamma, ..., sum_{j = 1}^{d} e_nj - gamma]
        Each sum "sum_{j = 1}^{d} e_nj - gamma" must be positive

        3. The list of coefficients E := [...eij...]
        All coefficients must be non-negative

        4. The coefficient gamma
        Gamma must be positive
        """

        p_degreee = Poly(p, vars_list).total_degree()
        if (p_degreee % 2 != 0):
            raise Exception("Polynomial degree should be divisible by 2")
        p_degreee = int(p_degreee)
        degree = int(p_degreee / 2)


        # Generate the new polynomial, E, and the constraints on E
        E_list = []
        g_list = []
        gamma = get_new()

        f = 0
        for v in vars_list:
            c_v = 0
            for j in range(degree):
                j += 1

                e = get_new()
                E_list.append(e)

                f += e * (v**(2*j))
                c_v += e
            c_v = c_v - gamma
            g_list.append(c_v)
        p_prime = p - f

        return (p_prime, g_list, E_list, gamma)

    (p_prime, g_list, E_list, gamma) = _make_positive_definite(get_new, p, vars_list)

    prob.add_sos_constraint(p_prime, vars_list)
    for g in g_list:
        prob.add_sos_constraint(g, vars_list)
    for e in E_list:
        prob.add_sos_constraint(e, vars_list)
    prob.add_sos_constraint(gamma, vars_list)

    return (p_prime, g_list, E_list, gamma)
