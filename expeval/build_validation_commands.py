import sys
from pathlib import Path

scmd = "sbatch --nice=100 --partition=identical-4 --cpus-per-task=2"
if __name__ == "__main__":

    Ns = [3, 5, 10, 15, 18]
    rounds = [True, False]
    methods = ['transpose', 'control', 'exponential', 'simple', 'linear']
    solvers = ['mathematica', 'z3', 'cvc5']

    TO = 2 * 3600

    expeval_dir = Path(__file__).parent.resolve()
    share_dir = expeval_dir.parent
    resdir = expeval_dir / 'validation_results10'
    singpath = share_dir / 'sing'
    run_sing = Path.home() / 'run_singularity.sh'
    verifypath = share_dir.resolve() / 'verify_po.py'
    main_cmd = f"{run_sing} exec --writable {singpath} timeout {TO}s python3 {verifypath}"

    fout = open("run.sh", 'w')

    def write(n, round, method, validation_method, solver, det, only=None, sdp_solver=None, alpha0=None, norobust=None):
        if method == 'linear':
            return

        rname = 'int' if round else 'float'
        methodname = method
        expopts = ''
        if method == 'exponential':
            assert alpha0 is not None
            assert norobust is not None
            if alpha0:
                expopts += '--alpha0 '
                methodname += '-alpha0'
            else:
                methodname += '-alphaok'
            if norobust:
                expopts += '--no-robust '
                methodname += '-norobust'
            else:
                methodname += '-robust'

        if method == 'simple' or method == 'exponential':
            assert sdp_solver is not None
            expopts += f'--sdp-solver {sdp_solver} '
            methodname += f'-{sdp_solver}'

        if validation_method == 'smt':
            validationname = solver + ('_det' if det else '_nodet')
        else:
            validationname = validation_method
        name = f"model_{n}_{rname}_mode{only}_{methodname}_{validationname}"
        out = (resdir / f"{name}.out").resolve()
        log = (resdir / f"{name}.log").resolve()
        mode0 = (resdir / f'lyap_{n}_{rname}_mode{only}_{methodname}.npy').resolve()
        mode1 = (resdir / f'lyap_{n}_{rname}_mode{only}_{methodname}.npy').resolve()
        mayberound = ' --round' if round else ''

        mem = '60000' if solver == 'mathematica' else '16000'

        fout.write(f"{scmd} --mem={mem} --job-name=valu3s --output={out} --error={log} ")
        fout.write(f"{main_cmd} --solver {solver} --size {n} {mayberound} --skip-synthesis ")
        if not det:
            fout.write("--no-det ")
        if validation_method == 'sympy':
            fout.write(f"--write-on-file0 {mode0} --write-on-file1 {mode1} ")
        if only is not None:
            fout.write(f"--only {only} ")
        fout.write(f"--use-{method} {expopts} --validation-method {validation_method}\n")
    # eof helper write

    for method in methods:
        for validation_method in ['sylvester', 'sympy', 'smt'] if method != 'linear' else ['smt']:
            for det in [True, False] if method != 'linear' and validation_method == 'smt' else [False]:
                for solver in solvers if validation_method == 'smt' else ['mathematica']:
                    for n in Ns:
                        for round in rounds:
                            if n == 15 and round:
                                continue
                            if n == 18 and round:
                                continue
                            for mode in [0, 1]:
                                if method != 'exponential' and method != 'simple':
                                    write(n, round, method, validation_method, solver, det, mode)
                                    continue
                                for sdp_solver in ['mosek', 'cvxopt', 'smcp']:
                                    for alpha0 in [False]: #[False, True] if method == 'exponential' else [False]:
                                        for norobust in [False, True] if method == 'exponential' else [False]: 
                                            write(n, round, method, validation_method, solver, det, mode, sdp_solver, alpha0, norobust)
    fout.close()
