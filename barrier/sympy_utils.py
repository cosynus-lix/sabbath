from sympy.polys.monomials import itermonomials

def gen_template_sympy(get_new, vars_list, degree, min_degree):
    coefficients = []
    template = 0

    for l in itermonomials(vars_list, degree, min_degree):
        coeff = get_new()
        template = template + coeff * l
        coefficients.append(coeff)
    return (template, coefficients)
