import sys
import os
import argparse
from collections import namedtuple
import process_res_common as prc

tests = [ 3, 5, 10, 15, 18 ]
types = ['float', 'int']
lyap_order = [ 'linear', 'control', 'transpose', 'simple', 'exponential', 'exponentialrobust']
solver_order = [ 'z3', 'cvc5', 'mathematica', 'sympy', 'sylvester']
sdp_order = [ None, 'cvxopt', 'mosek', 'smcp' ]
robust_order = [ None, True, False ]
mode_order = [ None, 0, 1 ]

TO = 2 * 3600

def cut_timeout(num):
    if num > TO:
        return TO
    return num

def extract_number(l):
    ll = l.replace('\n', '').rsplit(' ', 1)[1]
    return round(float(ll), 3)

class KResult(prc.Result):
    def __init__(self, fname):        
        # helper
        test_name, _ = os.path.splitext(os.path.basename(fname))
        self.test_file = test_name
        import subprocess
        from pathlib import Path
        # matscript = Path(__file__).parent / "compute_k" / "compute_k.m"
        matscript = 'compute_k'
        cmd = f"addpath compute_k; {matscript} {fname}; exit;"
        matlab = ['matlab', "-nodesktop", "-nodisplay", "-r", cmd]
        res = subprocess.Popen(matlab).wait()

    def __str__(self):
        return self.test_file

    def check_consistency_with(self, r):
        return True

    def get_compare_idx(self):
        return 0
# eoc KResult


class SynthesisResult(prc.Result):
    def __init__(self, fname):        
        # helper
        test_name, _ = os.path.splitext(os.path.basename(fname))
        self.test_file = test_name
        self.matfile = fname

        if self.get_json_file().exists():
            import json
            with open(self.get_json_file(), 'r') as fin:
                self.__dict__ = json.load(fin)
            return

        self.precision = 6

        tsplit = test_name.split('_', 4)
        _, self.n, self.type, self.method = tsplit
        self.n = int(self.n)

        msplit = self.method.split('-')
        self.robust = None
        self.sdpsolver = None
        if len(msplit) == 2: # simple
            self.method, self.sdpsolver = msplit
        elif len(msplit) == 4: # exponential
            self.method, alpha, robust, self.sdpsolver = msplit
            assert alpha == 'alphaok'
            if robust == 'robust':
                self.method += 'robust'

        self.vol = [None, None]
        self.robust_eps = [None, None]
        self.synth_time = [None, None]
        
        i = 0
        with open(self.get_log_file(), 'r') as fin:
            for l in fin.readlines():
                if 'Time for computing level set' in l:
                    self.synth_time[i] = extract_number(l)
                    i += 1

    def __str__(self):
        return self.test_file

    def compute_robustness(self):
        print(f"computing robustness of {self.test_file}")
        import subprocess, io
        cmd = f"load(\"{self.matfile}\"); try; run(\"Robustness_parameter_changes/main_robustness.m\"); end; exit;"
        matlab = ['matlab', "-nodesktop", "-nodisplay", "-r", cmd]
        res = subprocess.Popen(matlab, stdout=subprocess.PIPE)
        wait = False
        i = 0
        for l in io.TextIOWrapper(res.stdout, encoding='utf-8'):
            # if l.strip() != '':
            #     print(l)
            if 'ERROR' in l or 'assert' in l:
                print ("Error in ", self.test_file)
                return
            if "Robustness =" in l:
                wait = True
                continue
            if not wait:
                continue 
            l = l.strip()
            try:
                num = float(l)
            except:
                continue
            self.robust_eps[i] = num
            wait = False
            i += 1


    def compute_volume(self):
        print(f"computing volume of {self.test_file}")
        import subprocess, io
        cmd = f"load(\"{self.matfile}\"); try; run(\"Truncated_ellipsoid_volume/main.m\"); end; exit;"
        matlab = ['matlab', "-nodesktop", "-nodisplay", "-r", cmd]
        res = subprocess.Popen(matlab, stdout=subprocess.PIPE)
        wait_vol = False
        i = 0
        for l in io.TextIOWrapper(res.stdout, encoding='utf-8'):
            if 'ERROR' in l or 'assert' in l:
                print ("Error in ", self.test_file)
                return
            if "vol =" in l:
                wait_vol = True
                continue
            if not wait_vol:
                continue 
            l = l.strip()
            try:
                num = float(l)
            except:
                continue
            self.vol[i] = num
            wait_vol = False
            i += 1

    def check_consistency_with(self, r):
        return True

    def get_compare_idx(self):
        return int(
            str(tests.index(self.n)) + 
            str(types.index(self.type)) +
            str(lyap_order.index(self.method)) +
            str(robust_order.index(self.robust)) +
            str(sdp_order.index(self.sdpsolver))
        )

    def get_log_file(self):
        from pathlib import Path
        dirname = Path(self.matfile).parent
        return dirname / f"{self.test_file}.log"

    def get_json_file(self):
        from pathlib import Path
        dirname = Path(self.matfile).parent
        return dirname / f"{self.test_file}.json"

    def dump_in_json(self):
        import json
        with open(self.get_json_file(), 'w') as fout: 
            json.dump(self.__dict__, fout)

    def same_test(self, y):
        return self.n == y.n and self.type == y.type

# eoc SynthesisResult

def maybe_save_volumes(synth_results):
    for r in synth_results:
        if r.get_json_file().exists():
            continue
        r.compute_volume()
        r.compute_robustness()
        r.dump_in_json()

class ValidationResult(prc.Result):
    def __init__(self, fname):
        # helper
        test_name, _ = os.path.splitext(os.path.basename(fname))

        self.test_file = test_name

        self.mode = None
        self.det = None

        self.precision = 6

        tsplit = test_name.split('_', 5)
        _, self.n, self.type, self.mode, self.method, valid_method = tsplit
        self.n = int(self.n)
        assert self.mode in ['mode0', 'mode1']
        self.mode = 0 if self.mode == 'mode0' else 1

        msplit = self.method.split('-')
        self.robust = None
        self.sdpsolver = None
        if len(msplit) == 2: # simple
            self.method, self.sdpsolver = msplit
        elif len(msplit) == 4: # exponential
            self.method, alpha, robust, self.sdpsolver = msplit
            assert alpha == 'alphaok'
            if robust == 'robust':
                self.method += 'robust'
        
        validsplit = valid_method.split('_')
        if len(validsplit) > 1:
            self.solver, self.det = validsplit
            assert self.det in ['nodet', 'det']
            self.det = False if self.det == 'nodet' else True
        else:
            self.det = None
            self.solver = valid_method

        self.found_lyap = None
        self.find_time = None
        
        self.valid_lyap = None
        self.validation_time = [None, None, None]

        self.finish = False
        self.failure = False

        with open(fname, 'r') as fin:
            for l in fin.readlines():
                if 'Traceback' in l:
                    self.finish = True
                if 'pysmt.exceptions.SolverReturnedUnknownResultError' in l:
                    self.failure = True
                
                if 'DEFAULT PRECISION' in l:
                    self.precision = int(extract_number(l))

                if 'All modes are stable' in l:
                    self.valid_lyap = True

                if 'Synthesizing lyapunov with' in l or 'Synthesizing the lyapunov' in l:
                    self.find_time = TO

                if 'Time for synthesizing lyapunov' in l:
                    self.find_time = extract_number(l)
                    self.found_lyap = True

                if 'Validating the Lyapunov' in l:
                    self.validation_time[0] = TO
                    self.validation_time[1] = TO

                if 'Time for validating' in l:
                    assert self.method != 'linear', self.test_file
                    if 'c1' in l:
                        self.validation_time[1] = extract_number(l)
                        self.validation_time[2] = TO
                    elif 'c2' in l:
                        self.validation_time[2] = extract_number(l)
                    else:
                        assert 'lyapunov' in l
                        self.validation_time[0] = extract_number(l)

                elif 'The lyapunov function is not valid (SMT check failed)' in l:
                    if self.validation_time[1] == TO:
                        self.validation_time[1] = False
                    else:
                        assert self.validation_time[2] == TO, breakpoint()
                        self.validation_time[2] = False
                    self.valid_lyap = False
                    assert self.validation_time[0] != TO

                elif 'Serializing the results' in l:
                    self.finish = True

        if self.method == 'linear':
            self.valid_lyap = self.found_lyap
            self.validation_time[0] = self.find_time

    def __str__(self):
        return self.test_file + ' ' + str(self.found_lyap) + ' ' + str(self.valid_lyap)

    def check_consistency_with(self, r):
        if not self.same_test(r):
            return True
        if not self.finish or not r.finish or not self.failure or not r.failure:
            return True
        if self.found_lyap != r.found_lyap:
            print (self, r)
            return False
        if self.valid_lyap != r.valid_lyap:
            print (self, r)
            return False
        if self.validation_time[1] is False and type(r.validation_time[1]) == float:
            print (self, r)
            return False
        if self.validation_time[2] is False and type(r.validation_time[2]) == float:
            print (self, r)
            return False
        return True

    def get_compare_idx(self):
        return int(
            str(tests.index(self.n)) + 
            str(types.index(self.type)) +
            str(lyap_order.index(self.method)) +
            str(solver_order.index(self.solver)) +
            str(robust_order.index(self.robust)) +
            str(sdp_order.index(self.sdpsolver)) +
            str(mode_order.index(self.mode))
        )

    def same_test(self, y):
        return self.n == y.n and self.type == y.type and self.mode == y.mode and \
            self.same_method(y)

    def same_method(self, y):
        return self.method == y.method and self.sdpsolver == y.sdpsolver

# eoc StabilityResult

# --------------------------------------------------------------------------- #
# Presentation

def collect_methods():
    tests = []
    for m in lyap_order:
        if m == 'simple' or 'exponential' in m:
            for sdpsolver in sdp_order:
                if sdpsolver:
                    tests.append([m, sdpsolver])
        else:
            tests.append([m])
    return tests

def collect_tests(res):
    tests = []
    for r in res:
        if not any(r.same_test(t) for t in tests):
            tests.append(r)
    return tests

def collect_methods_tests(res):
    tests = []
    for r in res:
        if not any(r.same_method(t) for t in tests):
            tests.append(r)
    return tests

def find_all_that(results, n=None, type=None, method=None, solver=None, sdpsolver=None, mode=None, finish=None, found=None, valid=None, det=None, failure=None):
    res = []
    for r in results:
        if n is not None and r.n != n:
            continue
        if type is not None and r.type != type:
            continue
        if method is not None and r.method != method:
            continue
        if solver is not None and r.solver != solver:
            continue
        if sdpsolver is not None and r.sdpsolver != sdpsolver:
            continue
        if mode is not None and r.mode != mode:
            continue
        if finish is not None and r.finish != finish:
            continue
        if failure is not None and r.failure != failure:
            continue
        if found is not None and r.found_lyap is not None and r.found_lyap != found:
            continue
        if valid is not None and r.valid_lyap != valid:
            continue
        if det is not None and r.det != det:
            continue
        res.append(r)
    return res

def get_best_validation_res(res_complete, n=None):
    res = find_all_that(res_complete, n=n)
    synth_times = [ r.find_time for r in res if r.find_time is not None]
    if len(synth_times) == 0:
        avg_synth_time = 0
    else:
        avg_synth_time = round(sum(synth_times) / len(synth_times), 2)
        if avg_synth_time == TO:
            avg_synth_time = 'TO'

    method_tests = collect_methods_tests(res)
    tests = collect_tests(res)
    all_n = len(tests)

    synth = 0
    valid = []
    invalid = []
    to = 0
    all_good_methods = []

    for m in method_tests:
        equivalent = [r for r in res if r.same_method(m) and r.solver == 'sylvester']
        if all(r.found_lyap and r.valid_lyap for r in equivalent):
            all_good_methods.append(m)

    for t in tests:
        equivalent = [r for r in res if r.same_test(t)]
        if any(r.found_lyap for r in equivalent):
            synth += 1
        if any(r.valid_lyap for r in equivalent):
            valid.append(t)
        else:
            invalid.append(t)
        if not any(r.finish for r in equivalent):
            to += 1

    return all_n, avg_synth_time, synth, valid, invalid, to, all_good_methods

def print_valid_instances(ffname, results):
    valid = find_all_that(results, solver='sylvester', valid=True, finish=True)
    with open(ffname, 'w') as fout:
        for r in valid:
            fout.write(r.test_file)
            fout.write('\n')

def print_short_valid_latex_results(fname, results):
    # test_name = f'sys{n}_r' if type == 'int' else f'sys{n}'
    with open(fname, 'w') as fout:
        fout.write('\\begin{tabular}{c c |cc |cc |cc |cc |cc}\n')
        # fout.write(' & & \multicolumn{5}{c}{valid (not synth./ invalid / TO)} \\\\ \n')
        fout.write('\\cline{3-12}\n')
        fout.write('\multicolumn{2}{c}{} & \multicolumn{2}{c}{size 3} & \multicolumn{2}{c}{size 5} & \multicolumn{2}{c}{size 10} & \multicolumn{2}{c}{size 15} & \multicolumn{2}{c}{size 18} \\\\ \n')
        fout.write('\\hline\n')
        fout.write('method & solver & synth.time & valid & synth.time & valid& synth.time & valid& synth.time & valid& synth.time & valid \\\\ \n')
        fout.write("\\hline\n")
        methods = collect_methods()
        prev = None
        for m in methods:
            if prev is None or m[0] != prev[0]:
                fout.write("\\hline\n")
            prev = m
            fout.write(f"\\{m[0]} & ")
            if len(m) == 1:
                fout.write('&')
                res = find_all_that(results, method = m[0])
            else:
                fout.write(f'{m[1]} &')
                res = find_all_that(results, method = m[0], sdpsolver=m[1])

            for n in [3, 5, 10, 15, 18]:
                all, avg_synth_time, synth, valid, invalid, to, _ = get_best_validation_res(res, n)
                fout.write(f'{avg_synth_time} & {valid} / {all}')
                if n != 18:
                    fout.write('&')
            fout.write('\\\\ \n')

        fout.write('\\hline\n')
        fout.write('\\end{tabular}')

def print_validation_cumulative_plots(ffname, results):
    import numpy
    import matplotlib.pyplot as plt
    import matplotlib.ticker as ticker

    colors = {
        'sylvester' : 'green',
        'sympy' : 'blue',
        'mathematica' : 'red',
        'cvc5' : 'orange',
        'z3' : 'black',
    }

    legend = []
    N = [0]
    plt.xlabel("nr of validated instances")
    plt.ylabel("time")

    def fix_to(timing):
        return timing if timing < TO else TO

    # helper
    def print_line_plot(solver, det):
        res = find_all_that(results, solver=solver, det=det)
        res = [ r for r in res if r.method != 'linear' ]
        # res = sorted(res, key=lambda r : r.validation_time[0][0])
        N[0] = max(N[0], len(res))

        ys = sorted([
            fix_to(r.validation_time[0])
            for r in res
            if r.validation_time[0] is not None
        ])
        xs = range(len(ys))
        if solver == 'sympy' or solver == 'sylvester':
            linestyle = '-'
        else:
            linestyle = '-' if det else '--'
        plt.plot(
            xs, ys,
            color=colors[solver], linestyle=linestyle,
        )
        legend.append(f"{solver}" + (" +det" if det else ''))

    for solver in colors:
        for det in [True, False] if (solver != 'sympy' and solver != 'sylvester') else [None]:
            print_line_plot(solver, det)

    plt.plot(
        range(N[0]), [TO] * N[0],
        color='gray', linestyle='--',
    )

    plt.yscale('log')
    plt.ylim(0.01, TO+2000)
    plt.xlim(0, N[0])
    plt.legend(legend)
    #plt.grid(True)
    plt.savefig(ffname, bbox_inches='tight')
    plt.close()

def print_validation_scatter_plots(ffname, results):
    import numpy
    import matplotlib.pyplot as plt
    import matplotlib.ticker as ticker

    colors = {
        'mathematica' : 'red',
        'z3' : 'blue',
        'cvc5' : 'green',
        'mosek' : 'blue',
        'cvxopt' : 'red',
        'smcp' : 'green',
        None : 'orange'
    }

    markers = {
        'mathematica' : 'x',
        'z3' : '+',
        'cvc5' : 'o',
        True : 'o',
        False : 'x',
        None : 'x'
    }

    # helper
    legend = []
    def print_scatter_plot_det():
        plt.xlabel("det")
        plt.ylabel("nodet")

        all = find_all_that(results, found = True)
        res_det = find_all_that(all, det = True)
        res_nodet = find_all_that(all, det = False)
        # res = sorted(res, key=lambda r : r.validation_time[0][0])
        for r in res_det:
            if r.method == 'linear':
                continue
            rnd = find_all_that(res_nodet, solver=r.solver, n=r.n, type=r.type, method=r.method, sdpsolver=r.sdpsolver, mode=r.mode)
            assert len(rnd) <= 1, [str(r) for r in rnd]
            if len(rnd) == 0:
                continue
            rnd = rnd[0]

            rdt = r.validation_time[0]
            rndt = rnd.validation_time[0]
            plt.plot(
                rdt, rndt,
                color=colors[r.solver],
                marker=markers[r.valid_lyap],
                markersize=4
            )

    print_scatter_plot_det()

    plt.yscale('log')
    plt.xscale('log')
    plt.ylim(0.25, TO+8000)
    plt.xlim(0.25, TO+8000)
    plt.legend(legend)
    #plt.grid(True)
    plt.savefig(ffname, bbox_inches='tight')
    plt.close()

# ----------------------------------------------------------------------------- #

def argmax(xs, f):
    max = xs[0]
    for x in xs:
        if f(x) > f(max):
            max = x
    return max

def print_synthesis_latex_results(fname, results, ns):
    from decimal import Decimal
    results = find_all_that(results, type='float')
    num = len(ns)
    # test_name = f'sys{n}_r' if type == 'int' else f'sys{n}'
    with open(fname, 'w') as fout:
        fout.write('\\begin{tabular}{c c' + ('|ccc' * 2*num) + '}\n')
        # fout.write(' & & \multicolumn{5}{c}{valid (not synth./ invalid / TO)} \\\\ \n')
        fout.write(f'\\cline{{3-{num*6+2}}}\n')
        fout.write('\multicolumn{2}{c}{}')
        for n in ns:
            fout.write(f' & \multicolumn{{6}}{{c}}{{size {n}}}')
        fout.write('\\\\ \n')
        fout.write(f'\\cline{{3-{num*6+2}}}\n')
        fout.write(
            '\multicolumn{2}{c}{}' +
            (' & \multicolumn{3}{c}{mode 0} & \multicolumn{3}{c}{mode 1}' * num) +
            '\\\\ \n'
        )
        fout.write('\\hline\n')
        fout.write('method & solver ' + ("& time & vol & $\epsilon$" * 2*num) + '\\\\ \n')
        fout.write("\\hline\n")
        methods = collect_methods()

        # collect max
        max = {}
        for n in ns:
            res = find_all_that(results, n=n, type='float')
            vol0 = argmax(res, lambda x : x.vol[0])
            vol1 = argmax(res, lambda x : x.vol[1])
            rob0 = argmax(res, lambda x : x.robust_eps[0])
            rob1 = argmax(res, lambda x : x.robust_eps[1])
            mvol0 = [vol0.method, vol0.sdpsolver]
            mvol1 = [vol1.method, vol1.sdpsolver]
            mrob0 = [rob0.method, rob0.sdpsolver]
            mrob1 = [rob1.method, rob1.sdpsolver]
            max[n] = {'vol' : [mvol0, mvol1], 'rob' : [mrob0, mrob1] }


        def maybe_max(r, column, mode, val):
            best = max[r.n][column][mode]
            if best[0] == r.method and best[1] == r.sdpsolver:
                return "\\textbf{{{:.0e}}}".format(Decimal(val))
            return "{:.0e}".format(Decimal(val))

        prev = None
        for m in methods:
            if m[0] == 'linear':
                continue
            if prev is None or m[0] != prev[0]:
                fout.write("\\hline\n")
            prev = m
            fout.write(f"\\{m[0]} & ")
            if len(m) == 1:
                res = find_all_that(results, method = m[0])
            else:
                fout.write(f'{m[1]}')
                res = find_all_that(results, method = m[0], sdpsolver=m[1])

            for n in ns:
                rs = find_all_that(res, n=n, type='float')
                if len(rs) == 0:
                    fout.write(" & - & - & - & - & - & -")
                else:
                    r = rs[0]
                    fout.write(" & {:.0f}".format(r.synth_time[0]))
                    fout.write(' & ' + maybe_max(r, 'vol', 0, r.vol[0]))
                    fout.write(' & ' + maybe_max(r, 'rob', 0, r.robust_eps[0]))
                    fout.write(' & ' + "{:.0f}".format(r.synth_time[1]))
                    fout.write(' & ' + maybe_max(r, 'vol', 1, r.vol[1]))
                    fout.write(' & ' + maybe_max(r, 'rob', 1, r.robust_eps[1]))
            fout.write('\\\\ \n')

        fout.write('\\hline\n')
        fout.write('\\end{tabular}')


def print_synthesis_results(fname, results):
    # test_name = f'sys{n}_r' if type == 'int' else f'sys{n}'
    with open(fname, 'w') as fout:
        fout.write(', , , control, , , transpose, , , simple, , , , , , , exponential, , , , , , ,exponentialrobust, , , , , , \n')
        fout.write(', , , , , , , , , cvxopt, , , mosek, , , smcp, , , cvxopt, , , mosek , , ,smcp , , ,cvxopt, , ,mosek , , ,smcp , , \n')
        fout.write('method, solver, mode, time, vol, eps, time, vol, eps, time, vol, eps, time, vol, eps, time, vol, eps, time, vol, eps, time, vol, eps, time, vol, eps, time, vol, eps, time, vol, eps, time, vol, eps \n')
        tests = collect_tests(results)
        for t in tests:
            for mode in [0, 1]:
                fout.write(f'{t.n}, {t.type}, {mode},')
                tres = find_all_that(results, n=t.n, type=t.type)
                for method in ['control', 'transpose', 'simple', 'exponential', 'exponentialrobust']:
                    for sdpsolver in [ 'cvxopt', 'mosek', 'smcp' ] if method != 'transpose' and method != 'control' else [None]:
                        res = find_all_that(tres, method=method, sdpsolver=sdpsolver)
                        if len(res) == 0:
                            fout.write(', , ,')
                            continue
                        assert len(res) == 1
                        r = res[0]
                        fout.write(f'{r.synth_time[mode]}, {r.vol[mode]}, {r.robust_eps[mode]},')
                fout.write('\n')



def print_simulations(fname, results):
    with open(fname, 'w') as fout:
        prev = None
        for r in results:
            fout.write(f"{r.n} {r.type} {r.method}, ")
            for i, k in enumerate(r.sample_ks):
                fout.write(f'{k},')
            fout.write('\n')
            fout.write(f"{r.n} {r.type} {r.method}, ")
            for i, v in enumerate(r.sample_verified):
                fout.write(('V' if v else '') + ',')
            fout.write('\n')

def print_simulations_plots(simul_results, synth_results, out_dir):
    import numpy
    import matplotlib.pyplot as plt
    import matplotlib.ticker as ticker

    colors = {
        'simple' : 'red',
        'exponential' : 'blue',
        'transpose' : 'green',
        'control' : 'orange',
        'linear' : 'gray'
    }

    def get_name(n, type):
        return f'{n}_{type}'
    
    slopes = {}

    # helper
    def print_line_plot(ffname, n, type):
        legend = []
        plt.xlabel("time")
        plt.ylabel("k")
        size = 101
        
        # for each method
        for r in simul_results:
            if r.n != n or r.type != type or r.method == 'linear':
                continue
            if not r.sample_ks:
                continue
            xk = range(len(r.sample_ks))
            yk = r.sample_ks
            plt.plot(
                xk, yk,
                color=colors[r.method], linestyle='-',
            )
            legend.append(f"{r.method}")

            rs = [
                _rs for _rs in synth_results
                if _rs.n == r.n and _rs.type == r.type and _rs.method == r.method
            ][0]
            plt.plot(
                range(size), [rs.synthesis_k[0]] * size,
                color=colors[rs.method], linestyle='--',
            )
            legend.append(f"{rs.method}")

            xk_below = [ iy for iy, y in enumerate(yk) if ((y <= rs.synthesis_k[0]) or (iy > 20)) and y > 0.01 ]
            if not xk_below:
                xk_below = xk[int(len(xk)/10):]
            assert xk_below, (n, t, r.method)
            yk_below = [ y for iy, y in enumerate(yk) if iy in xk_below ]
            a, b = numpy.polyfit(xk_below, numpy.log(yk_below), 1)
            slopes[get_name(n, type)][r.method] = (a, b)

        if len(legend) == 0:
            plt.clf()
            return
        plt.yscale('log')
        plt.ylim(0.001, 10000000)
        plt.xlim(0, size)
        plt.legend(legend)
        #plt.grid(True)
        plt.savefig(ffname, bbox_inches='tight')
        

    for n in tests:
        for t in types:
            name = get_name(n, t)
            slopes[name] = {}
            print_line_plot(out_dir / f'{name}.png', str(n), t)

# --------------------------------------------------------------------------- #

def main(args):
    from pathlib import Path
    this_dir = Path(__file__).parent

    out_dir = this_dir / 'results'
    out_dir.mkdir(exist_ok=True)

    # # COMPUTE K
    # _ = prc.collect_results(
    #     this_dir / 'synthesis_results', CResult=KResult, extension='mat'
    # )

    synth_results = prc.collect_results(
        this_dir / 'synthesis_results', CResult=SynthesisResult, extension='mat'
    )
    maybe_save_volumes(synth_results)
    
    print_synthesis_latex_results(out_dir / "synthesis_table.tex", synth_results, [15, 18])
    print_synthesis_latex_results(out_dir / "synthesis_table_appendix.tex", synth_results, [3, 5, 10])
    print_synthesis_results(out_dir / "synthesis_results.csv", synth_results)

    # collect results from files in directory
    valid_results6 = prc.collect_results(
        this_dir / 'validation_results6', CResult=ValidationResult, extension='log'
    )
    valid_results4 = prc.collect_results(
        this_dir / 'validation_results4', CResult=ValidationResult, extension='log'
    )
    valid_results10 = prc.collect_results(
        this_dir / 'validation_results10', CResult=ValidationResult, extension='log'
    )

    nonlin10 = [r for r in valid_results10 if r.method != 'linear']

    all, _, synth, valid, invalid, to, all_good = get_best_validation_res(nonlin10)
    print(f"precision 10:\t all: {all},\t synth: {synth},\t valid: {len(valid)},\t invalid: {len(invalid)},\t to: {to}")

    all, _, synth, valid, invalid, to, all_good = get_best_validation_res(valid_results6)
    print(f"precision 6:\t all: {all},\t synth: {synth},\t valid: {len(valid)},\t invalid: {len(invalid)},\t to: {to}")

    all, _, synth, valid, invalid, to, all_good = get_best_validation_res(valid_results4)
    print(f"precision  4:\t all: {all},\t synth: {synth},\t valid: {len(valid)},\t invalid: {len(invalid)},\t to: {to}")

    print_valid_instances(out_dir / 'valid_names', valid_results10)
    print_short_valid_latex_results(out_dir / "short_table.tex", valid_results10)
    print_validation_cumulative_plots(out_dir / "valid_solvers.png", valid_results10)
    print_validation_scatter_plots(out_dir / "valid_scatter.png", valid_results10)
    # print_long_valid_latex_table(out_dir / "short_table.tex", valid_results)

    # print_latex_results(out_dir / "table.tex", synth_results)
    # print_valid_results(out_dir / "valid_results.csv", valid_results)
    #print_simulations(out_dir / 'simulations.csv', simul_results)
    #print_simulations_plots(simul_results, synth_results, out_dir)
    return 0

# =========================================================================== #

def handle_args():
    parser = argparse.ArgumentParser(
        description=("Generates list of commands."),
        formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )

    parser.add_argument(
        '--res-dir', dest='res_dir',
        default="results",
        help='Name of the directory where to find the results.')

    parser.add_argument(
        '-o', '--out-file', dest='out_file',
        default="result.csv",
        help='Name of the file where to print the results.')

    args = parser.parse_args()
    return args

# =========================================================================== #

if "__main__" == __name__:
    args = handle_args()
    rv = main(args)
    sys.exit(rv)
