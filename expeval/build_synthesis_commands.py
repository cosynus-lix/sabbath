import sys
from pathlib import Path

scmd = "sbatch --nice=100 --partition=identical-4 --cpus-per-task=2"
if __name__ == "__main__":

    Ns = [3, 5, 10, 15, 18]
    rounds = [True, False]
    methods = ['transpose', 'control', 'exponential', 'simple' ]
    solvers = ['mathematica', 'z3', 'cvc5']

    TO = 2 * 3600

    expeval_dir = Path(__file__).parent.resolve()
    share_dir = expeval_dir.parent
    valid_list = expeval_dir / 'valid_names'
    resdir = expeval_dir / 'synthesis_results'
    lyapdir = expeval_dir / 'validation_results10'
    numdir = expeval_dir / 'numeric_synthesis'

    singpath = share_dir / 'sing'
    run_sing = Path.home() / 'run_singularity.sh'
    verifypath = share_dir.resolve() / 'verify_po.py'
    # main_cmd = f"{run_sing} exec --writable {singpath} timeout {TO}s python3 {verifypath}"
    main_cmd = f"{run_sing} exec --writable {singpath} python3 {verifypath}"

    fout = open("run.sh", 'w')

    with open(valid_list, 'r') as fin:
        valid_names = [ name.replace('\n', '') for name in fin.readlines() ]

    def write(n, round, method, solver, sdp_solver=None, alpha0=None, norobust=None):
        refs = "6,5,-1,20"

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

        name = f"model_{n}_{rname}_{methodname}"

        sylvester_name0 = f"model_{n}_{rname}_mode0_{methodname}_sylvester"
        sylvester_name1 = f"model_{n}_{rname}_mode1_{methodname}_sylvester"
        if sylvester_name0 not in valid_names or sylvester_name1 not in valid_names:
            print('skipping', name)
            return

        out = (resdir / f"{name}.out").resolve()
        log = (resdir / f"{name}.log").resolve()
        outputname = (resdir / f"{name}.mat").resolve()
        input_num_info_name = (numdir / f"{name}.mat").resolve()
        mode0 = (lyapdir / f'lyap_{n}_{rname}_mode0_{methodname}.npy').resolve()
        mode1 = (lyapdir / f'lyap_{n}_{rname}_mode1_{methodname}.npy').resolve()
        assert mode0.exists()
        assert mode1.exists()

        mayberound = ' --round' if round else ''

        mem = '60000' if solver == 'mathematica' else '16000'

        fout.write(f"{scmd} --mem={mem} --job-name=valu3s --output={out} --error={log} ")
        fout.write(f"{main_cmd} --solver {solver} --size {n} {mayberound} --skip-validation ")
        fout.write(f"--read-from-file0 {mode0} --read-from-file1 {mode1} ")
        fout.write(f"--references {refs} --output {outputname} --input-num-info {input_num_info_name} ")
        fout.write("\n")
    # eof

    for method in methods:
        for solver in ['mathematica']:
            for n in Ns:
                for round in rounds:
                    if method != 'exponential' and method != 'simple':
                        write(n, round, method, solver)
                        continue
                    for sdp_solver in ['mosek', 'cvxopt', 'smcp']:
                        for alpha0 in [False]: #[False, True] if method == 'exponential' else [False]:
                            for norobust in [False, True] if method == 'exponential' else [False]:
                                write(n, round, method, solver, sdp_solver, alpha0, norobust)

    fout.close()
