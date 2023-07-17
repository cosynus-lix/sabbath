sbatch --nice=100 --partition=cpu-generic --cpus-per-task=2 --mem=16000 --job-name=valu3s --output=/home/lbattista/piecewise_lyap/semialgebraic_invariants/expeval/piecewise_lyap_results/model_10_validation_method_smt_solver_mathematica_normalization_False_sdp_solver_mosek.out --error=/home/lbattista/piecewise_lyap/semialgebraic_invariants/expeval/piecewise_lyap_results/model_10_validation_method_smt_solver_mathematica_normalization_False_sdp_solver_mosek.log /home/lbattista/run_singularity.sh exec --writable /home/lbattista/piecewise_lyap/semialgebraic_invariants/sing timeout 7200s python3 /home/lbattista/piecewise_lyap/semialgebraic_invariants/piecewise_lyap_expeval.py /home/lbattista/piecewise_lyap/semialgebraic_invariants/Reformulated_systems/reformulation_size_10.hyb --solver mathematica --validation-method smt --output /home/lbattista/piecewise_lyap/semialgebraic_invariants/expeval/piecewise_lyap_results/model_10_validation_method_smt_solver_mathematica_normalization_False_sdp_solver_mosek.mat --normalize_lyap_in_sdp_problem False --sdp-solver mosek 
sbatch --nice=100 --partition=cpu-generic --cpus-per-task=2 --mem=16000 --job-name=valu3s --output=/home/lbattista/piecewise_lyap/semialgebraic_invariants/expeval/piecewise_lyap_results/model_10_validation_method_smt_solver_mathematica_normalization_True_sdp_solver_cvxopt.out --error=/home/lbattista/piecewise_lyap/semialgebraic_invariants/expeval/piecewise_lyap_results/model_10_validation_method_smt_solver_mathematica_normalization_True_sdp_solver_cvxopt.log /home/lbattista/run_singularity.sh exec --writable /home/lbattista/piecewise_lyap/semialgebraic_invariants/sing timeout 7200s python3 /home/lbattista/piecewise_lyap/semialgebraic_invariants/piecewise_lyap_expeval.py /home/lbattista/piecewise_lyap/semialgebraic_invariants/Reformulated_systems/reformulation_size_10.hyb --solver mathematica --validation-method smt --output /home/lbattista/piecewise_lyap/semialgebraic_invariants/expeval/piecewise_lyap_results/model_10_validation_method_smt_solver_mathematica_normalization_True_sdp_solver_cvxopt.mat --normalize_lyap_in_sdp_problem True --sdp-solver cvxopt 
sbatch --nice=100 --partition=cpu-generic --cpus-per-task=2 --mem=16000 --job-name=valu3s --output=/home/lbattista/piecewise_lyap/semialgebraic_invariants/expeval/piecewise_lyap_results/model_15_validation_method_smt_solver_mathematica_normalization_False_sdp_solver_cvxopt.out --error=/home/lbattista/piecewise_lyap/semialgebraic_invariants/expeval/piecewise_lyap_results/model_15_validation_method_smt_solver_mathematica_normalization_False_sdp_solver_cvxopt.log /home/lbattista/run_singularity.sh exec --writable /home/lbattista/piecewise_lyap/semialgebraic_invariants/sing timeout 7200s python3 /home/lbattista/piecewise_lyap/semialgebraic_invariants/piecewise_lyap_expeval.py /home/lbattista/piecewise_lyap/semialgebraic_invariants/Reformulated_systems/reformulation_size_15.hyb --solver mathematica --validation-method smt --output /home/lbattista/piecewise_lyap/semialgebraic_invariants/expeval/piecewise_lyap_results/model_15_validation_method_smt_solver_mathematica_normalization_False_sdp_solver_cvxopt.mat --normalize_lyap_in_sdp_problem False --sdp-solver cvxopt 
sbatch --nice=100 --partition=cpu-generic --cpus-per-task=2 --mem=16000 --job-name=valu3s --output=/home/lbattista/piecewise_lyap/semialgebraic_invariants/expeval/piecewise_lyap_results/model_15_validation_method_smt_solver_mathematica_normalization_False_sdp_solver_mosek.out --error=/home/lbattista/piecewise_lyap/semialgebraic_invariants/expeval/piecewise_lyap_results/model_15_validation_method_smt_solver_mathematica_normalization_False_sdp_solver_mosek.log /home/lbattista/run_singularity.sh exec --writable /home/lbattista/piecewise_lyap/semialgebraic_invariants/sing timeout 7200s python3 /home/lbattista/piecewise_lyap/semialgebraic_invariants/piecewise_lyap_expeval.py /home/lbattista/piecewise_lyap/semialgebraic_invariants/Reformulated_systems/reformulation_size_15.hyb --solver mathematica --validation-method smt --output /home/lbattista/piecewise_lyap/semialgebraic_invariants/expeval/piecewise_lyap_results/model_15_validation_method_smt_solver_mathematica_normalization_False_sdp_solver_mosek.mat --normalize_lyap_in_sdp_problem False --sdp-solver mosek 
sbatch --nice=100 --partition=cpu-generic --cpus-per-task=2 --mem=16000 --job-name=valu3s --output=/home/lbattista/piecewise_lyap/semialgebraic_invariants/expeval/piecewise_lyap_results/model_18_validation_method_smt_solver_mathematica_normalization_True_sdp_solver_cvxopt.out --error=/home/lbattista/piecewise_lyap/semialgebraic_invariants/expeval/piecewise_lyap_results/model_18_validation_method_smt_solver_mathematica_normalization_True_sdp_solver_cvxopt.log /home/lbattista/run_singularity.sh exec --writable /home/lbattista/piecewise_lyap/semialgebraic_invariants/sing timeout 7200s python3 /home/lbattista/piecewise_lyap/semialgebraic_invariants/piecewise_lyap_expeval.py /home/lbattista/piecewise_lyap/semialgebraic_invariants/Reformulated_systems/reformulation_size_18.hyb --solver mathematica --validation-method smt --output /home/lbattista/piecewise_lyap/semialgebraic_invariants/expeval/piecewise_lyap_results/model_18_validation_method_smt_solver_mathematica_normalization_True_sdp_solver_cvxopt.mat --normalize_lyap_in_sdp_problem True --sdp-solver cvxopt 
sbatch --nice=100 --partition=cpu-generic --cpus-per-task=2 --mem=16000 --job-name=valu3s --output=/home/lbattista/piecewise_lyap/semialgebraic_invariants/expeval/piecewise_lyap_results/model_18_validation_method_smt_solver_mathematica_normalization_False_sdp_solver_cvxopt.out --error=/home/lbattista/piecewise_lyap/semialgebraic_invariants/expeval/piecewise_lyap_results/model_18_validation_method_smt_solver_mathematica_normalization_False_sdp_solver_cvxopt.log /home/lbattista/run_singularity.sh exec --writable /home/lbattista/piecewise_lyap/semialgebraic_invariants/sing timeout 7200s python3 /home/lbattista/piecewise_lyap/semialgebraic_invariants/piecewise_lyap_expeval.py /home/lbattista/piecewise_lyap/semialgebraic_invariants/Reformulated_systems/reformulation_size_18.hyb --solver mathematica --validation-method smt --output /home/lbattista/piecewise_lyap/semialgebraic_invariants/expeval/piecewise_lyap_results/model_18_validation_method_smt_solver_mathematica_normalization_False_sdp_solver_cvxopt.mat --normalize_lyap_in_sdp_problem False --sdp-solver cvxopt 
