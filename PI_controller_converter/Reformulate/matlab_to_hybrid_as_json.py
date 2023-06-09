import numpy as np
from scipy import io
from collections import namedtuple
import json

def vector_field_description(A, b):
    # We convert the matricial formalism into SMT-LIB strings
    odes = []
    num_vars = np.shape(A)[0]
    for index_var in range(num_vars):
        ode_this_var = f"(* x_0 {A[index_var][0]}) "
        for index_var2 in range(1,num_vars):
            ode_this_var = "(+ " + ode_this_var + f" (* x_{index_var2} {A[index_var][index_var2]})) "
        ode_this_var = "(+ " + ode_this_var + f" {b[index_var][0]})"
        odes.append("(+ " + ode_this_var + " 0)")
    return odes

def scalar_product(c):
    # We convert the scalar product into SMT-LIB strings
    num_vars = np.shape(c)[0]
    index_var = 0
    term_this_var = f"(* x_{index_var} {c[index_var]}) "
    scalar_prod = term_this_var
    for index_var in range(1, num_vars):
        term_this_var = f"(* x_{index_var} {c[index_var]}) "
        scalar_prod = "(+ " + term_this_var + " " + scalar_prod + " )"
    return scalar_prod

def export_to_matlab(As_homo, bs_homo, Cs_homo, Guards_homo):
    dic = {}
    dic['A_0_homo'] = As_homo[0]
    dic['A_1_homo'] = As_homo[1]
    dic['b_0_homo'] = bs_homo[0]
    dic['b_1_homo'] = bs_homo[1]
    dic['C_0_homo'] = Cs_homo[0]
    dic['C_1_homo'] = Cs_homo[1]
    dic['Guards_0_homo'] = Guards_homo[0]
    dic['Guards_1_homo'] = Guards_homo[1]
    io.savemat("Reformulated_to_matlab.mat", dic )
    return 0

def string_no_change(num_variables):
    result = ""
    for ind_var in range(num_variables):
        result += f" (= x_{ind_var}_next x_{ind_var})"
    return result


def reformulate_PI(A_or, B_or, C_or, Invar_or, KP_or, KI_or, num_var, num_con, num_out, ref_val):
    # We reformulate a PI controller of the form x' = A_or * x + B_or * u 
    # (_or stands for original)
    # in the new variable w = [x; u], obtaining the dynsys of the form
    #  w' = A_homo * w + b_homo.
    # Also the linear condition of the switch is modified accordingly (does not
    # care about the value of u).

    A_homo_top = np.hstack([A_or, B_or])
    N = -1 * np.dot(KP_or, np.dot(C_or, A_or)) - np.dot(KI_or, C_or)
    M = -1 * np.dot(KP_or, np.dot(C_or, B_or))
    A_homo_bot = np.hstack([N, M])
    A_homo = np.vstack([A_homo_top, A_homo_bot])

    b_bot = np.dot(KI_or, ref_val)
    b_homo = np.vstack([np.zeros([num_var,1]), b_bot])

    C_homo = np.hstack([C_or, np.zeros([num_out, num_con])])
    
    Invar_geq0_homo = np.hstack([Invar_or[:,:num_var], np.zeros([len(Invar_or), num_con]), Invar_or[:,[-1]] ])

    return (A_homo, b_homo, C_homo, Invar_geq0_homo)

def main():
    
    # We import the Hybrid System form the .mat file. Also other exstension should
    # be addressed.
    # FIXME fare in modo di poter passare un argomento
    for size_system in [3,5,10,15,18]:
        HybridSystemMatlab = io.loadmat(f"./data_matlab/data_to_python_size_{size_system}")
        
        # We format the loaded data in python files
        num_modes = HybridSystemMatlab["num_modes"][0][0]
        num_variables = HybridSystemMatlab["num_variables"][0][0]
        num_controllers = HybridSystemMatlab["num_controllers"][0][0]
        num_outputs = HybridSystemMatlab["num_outputs"][0][0]
        reference_values = HybridSystemMatlab["reference_values"]
        reference_values = np.asarray(np.matrix([[0.5],[0],[-1],[20]]))
        As = []
        Bs = []
        Cs = []
        KIs = []
        KPs = []
        Invars_geq0 = []
        for ind_mode in range(num_modes):
            As.append(HybridSystemMatlab[f"A_{ind_mode}"])
            Bs.append(HybridSystemMatlab[f"B_{ind_mode}"])
            Cs.append(HybridSystemMatlab[f"C_{ind_mode}"])
            KIs.append(HybridSystemMatlab[f"KI_{ind_mode}"])
            KPs.append(HybridSystemMatlab[f"KP_{ind_mode}"])
            Invars_geq0.append(HybridSystemMatlab[f"Invar_{ind_mode}_geq0"])

        num_homo_variables = num_variables + num_controllers

        # We reformulate the system with PI controller in a homogenous system
        As_homo = []
        bs_homo = []
        Cs_homo = []
        Invars_geq0_homo = []

        for ind_mode in range(num_modes):
            (A_homo, b_homo, C_homo, Invar_geq0_homo) = reformulate_PI(As[ind_mode], Bs[ind_mode], Cs[ind_mode], 
                                                                    Invars_geq0[ind_mode], KPs[ind_mode], KIs[ind_mode], 
                                                                    num_variables, num_controllers, num_outputs, reference_values)

            As_homo.append(A_homo)
            bs_homo.append(b_homo)
            Cs_homo.append(C_homo)
            Invars_geq0_homo.append(Invar_geq0_homo)
        
        np.savez(f'variabili_size_{size_system}_refs_{np.transpose(reference_values)}.npz', As_homo=As_homo, bs_homo=bs_homo, Cs_homo=Cs_homo, Invars_geq0_homo=Invars_geq0_homo)
        # np.savez(f'variables_size_{size_system}.npz', As_homo=As_homo, bs_homo=bs_homo, Cs_homo=Cs_homo, Invars_geq0_homo=Invars_geq0_homo)

        export_to_matlab(As_homo, bs_homo, Cs_homo, Invars_geq0_homo)
        
        
        
        # We create the file .hyb to give the problem to Sabbath

        # General case, at the moment it does not work
        # problem = {}
        # problem["name"] = "Reformulated Homogenous System"
        # problem["contVars"] = []
        # for index_var in range(num_homo_variables):
        #     problem["contVars"].append(f"(declare-fun x_{index_var} () Real)")
        # problem["varsDecl"] = []
        # for index_var in range(num_homo_variables):
        #     problem["varsDecl"].append(f"(declare-fun x_{index_var} () Real)")
        # problem["init"] = {}
        # for index_mode in range(num_modes):
        #     problem["init"][f"{index_mode}"]= "true"
        # problem["locations"] = {} 
        # for index_mode in range(num_modes):
        #     problem["locations"][f"{index_mode}"] = {}
        #     problem["locations"][f"{index_mode}"]["invar"] = "true"
        #     problem["locations"][f"{index_mode}"]["vectorField"] = vector_field_description(As_homo[index_mode], bs_homo[index_mode])
        # problem["edges"] = {}
        # for index_mode in range(num_modes):
        #     problem["edges"][f"{index_mode}"]= [{}]
        #     problem["edges"][f"{index_mode}"][0]["dst"] = "1"
        #     problem["edges"][f"{index_mode}"][0]["trans"] = "(and (>= x_0 0.5) (= x_0 x_0) (= x_0 x_0) )"
        # problem["predicates"]= []
        # with open('prova.hyb', 'w', encoding='utf-8') as f:
        #     json.dump(problem, f, ensure_ascii=False, indent=2)

        # Case with only 2 modes
        problem = {}
        problem["name"] = "Reformulated Homogenous System"
        problem["contVars"] = []
        for index_var in range(num_homo_variables):
            problem["contVars"].append(f"(declare-fun x_{index_var} () Real)")
        problem["varsDecl"] = []
        for index_var in range(num_homo_variables):
            problem["varsDecl"].append(f"(declare-fun x_{index_var} () Real)")
        problem["init"] = {}
        for index_mode in range(num_modes):
            problem["init"][f"{index_mode}"]= "true"
        problem["locations"] = {} 
        
        index_mode = 0
        problem["locations"][f"{index_mode}"] = {}
        problem["locations"][f"{index_mode}"]["invar"] = "( < " + scalar_product(-Invars_geq0_homo[0][0][:-1]) + f"{Invars_geq0_homo[0][0][-1]}" + " )"
        problem["locations"][f"{index_mode}"]["vectorField"] = vector_field_description(As_homo[index_mode], bs_homo[index_mode])
        index_mode = 1
        problem["locations"][f"{index_mode}"] = {}
        problem["locations"][f"{index_mode}"]["invar"] = "( >= " + scalar_product(Invars_geq0_homo[1][0][:-1]) + f"{-Invars_geq0_homo[1][0][-1]}" + " )"
        problem["locations"][f"{index_mode}"]["vectorField"] = vector_field_description(As_homo[index_mode], bs_homo[index_mode])

        problem["edges"] = {}
        index_mode = 0
        problem["edges"][f"{index_mode}"]= [{}]
        problem["edges"][f"{index_mode}"][0]["dst"] = "1"
        problem["edges"][f"{index_mode}"][0]["trans"] = "(and ( >= " + scalar_product(-Invars_geq0_homo[0][0][:-1]) + f"{Invars_geq0_homo[0][0][-1]}" + " ) " + string_no_change(num_homo_variables) + " )"
        index_mode = 1
        problem["edges"][f"{index_mode}"]= [{}]
        problem["edges"][f"{index_mode}"][0]["dst"] = "0"
        problem["edges"][f"{index_mode}"][0]["trans"] = "(and ( < " + scalar_product(Invars_geq0_homo[1][0][:-1]) + f"{-Invars_geq0_homo[1][0][-1]}" + " ) " + string_no_change(num_homo_variables) + " )"


        problem["predicates"]= []
        problem["property"]= []

        with open(f'./hybrid_reformulation/reformulation_size_{size_system}.hyb', 'w', encoding='utf-8') as f:
            json.dump(problem, f, ensure_ascii=False, indent=2)

        # We create the file .invar for each mode to give the problem to Sabbath
        for index_mode in range(num_modes):
            problem = {}
            problem["name"] = "Reformulated Homogenous System"
            problem["antecedent"] = "true"
            problem["consequent"] = "true"
            problem["constraints"] = "true"
            problem["contVars"] = []
            for index_var in range(num_homo_variables):
                problem["contVars"].append(f"(declare-fun x_{index_var} () Real)")
            problem["varsDecl"] = []
            for index_var in range(num_homo_variables):
                problem["varsDecl"].append(f"(declare-fun x_{index_var} () Real)")
            problem["predicates"]= []
            problem["vectorField"] = vector_field_description(As_homo[index_mode], bs_homo[index_mode])
            with open(f"./single_mode_reformulation/mode_{index_mode}_size_{size_system}.invar", "w", encoding='utf-8') as f:
                json.dump([problem], f, ensure_ascii=False, indent=2)

    return 0


if __name__ == "__main__":
    main()
