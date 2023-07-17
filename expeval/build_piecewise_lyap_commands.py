import sys
from pathlib import Path

scmd = "sbatch --nice=100 --partition=cpu-generic --cpus-per-task=2"
if __name__ == "__main__":

    Ns = [3, 5, 10, 15, 18]
    solvers = ['mathematica', 'z3', 'cvc5']
    validation_methods = ['sympy', 'sylvester', 'smt']

    TO = 2 * 3600

    expeval_dir = Path(__file__).parent.resolve()
    share_dir = expeval_dir.parent
    resdir = expeval_dir / 'piecewise_lyap_results'

    singpath = '/home/lbattista/piecewise_lyap/semialgebraic_invariants/sing'
    run_sing = Path.home() / 'run_singularity.sh'
    verifypath = share_dir.resolve() / 'piecewise_lyap_expeval.py'
    main_cmd = f"{run_sing} exec --writable {singpath} timeout {TO}s python3 {verifypath}"

    fout = open("run.sh", 'w')

    def write(n, validation_method, solver, normalization, sdp_solver):
        name = f"model_{n}_validation_method_{validation_method}_solver_{solver}_normalization_{normalization}_sdp_solver_{sdp_solver}"

        out = (resdir / f"{name}.out").resolve()
        log = (resdir / f"{name}.log").resolve()
        outputname = (resdir / f"{name}.mat").resolve()


        mem = '16000' if solver == 'mathematica' else '16000'

        fout.write(f"{scmd} --mem={mem} --job-name=valu3s --output={out} --error={log} ")
        fout.write(f"{main_cmd} /home/lbattista/piecewise_lyap/semialgebraic_invariants/Reformulated_systems/reformulation_size_{n}.hyb --solver {solver} --validation-method {validation_method} ")
        fout.write(f"--output {outputname} --normalize_lyap_in_sdp_problem {normalization} --sdp-solver {sdp_solver} ")
        fout.write("\n")
    # eof
    # for n in Ns: # [3,5,10,15,18]
    #     for validation_method in ['smt']: # ['sylvester', 'sympy', 'smt']
    #         for normalization in ['True', 'False']: # ['True', 'False']
    #             for sdp_solver in ['mosek', 'cvxopt']: # ['cvxopt', 'mosek', 'smcp']
    for (n, validation_method, normalization, sdp_solver) in [(10, 'smt', 'False', 'mosek'),(10, 'smt', 'True', 'cvxopt'),(15, 'smt', 'False', 'cvxopt'),(15, 'smt', 'False', 'mosek'), (18, 'smt', 'True', 'cvxopt')]:
        if validation_method == "smt":
            for solver in ['mathematica']: # ['mathematica', 'z3', 'mathsat', 'cvc5']
                write(n, validation_method, solver, normalization, sdp_solver)
        else:
            write(n, validation_method, 'z3', normalization, sdp_solver)

    fout.close()
