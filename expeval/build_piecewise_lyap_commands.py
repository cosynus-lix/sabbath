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

    singpath = '/home/abecchi/valu3s/model_checking_paper/share/sing'
    run_sing = Path.home() / 'run_singularity.sh'
    verifypath = share_dir.resolve() / 'piecewise_lyap_expeval.py'
    # main_cmd = f"{run_sing} exec --writable {singpath} timeout {TO}s python3 {verifypath}"
    main_cmd = f"{run_sing} exec --writable {singpath} python3 {verifypath}"

    fout = open("run.sh", 'w')

    def write(n, validation_method, solver):
        name = f"model_{n}"

        out = (resdir / f"{name}.out").resolve()
        log = (resdir / f"{name}.log").resolve()
        outputname = (resdir / f"{name}.mat").resolve()


        mem = '60000' if solver == 'mathematica' else '16000'

        fout.write(f"{scmd} --mem={mem} --job-name=valu3s --output={out} --error={log} ")
        fout.write(f"{main_cmd} Reformulated_systems/reformulation_size_{n}.hyb --solver {solver} --validation-method {validation_method} ")
        fout.write(f"--output {outputname}")
        fout.write("\n")
    # eof
    for n in [3, 10]:
        for validation_method in ['sympy']:
            if validation_method == "smt":
                for solver in ['mathematica', 'z3']:
                    write(n, validation_method, solver)
            else:
                write(n, validation_method, 'z3')

    fout.close()
