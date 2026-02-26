import shutil
import multiprocessing as mp
from pathlib import Path
import pandas as pd
from gasol_asm import optimize_from_sfs, OptimizationParams
import sys

def initialize_params(input_file: str, seqs_file: str):
    optimization_params = OptimizationParams()

    optimization_params.input_file = input_file

    optimization_params.input_format = "sfs"
    optimization_params.contract = None

    # --- Output & Paths ---
    optimization_params.output_path = None
    optimization_params.seqs_file = seqs_file
    optimization_params.blocks_file = "blocks.csv"

    # --- General Flags ---
    optimization_params.optimization_enabled = True
    optimization_params.keep_files = False
    optimization_params.verbose = False
    optimization_params.debug_flag = False
    optimization_params.dot_generation = False

    optimization_params.generate_log = False
    optimization_params.log_file = None
    optimization_params.from_log = None

    optimization_params.smt_solver = "oms"
    optimization_params.timeout = 10
    optimization_params.direct_timeout = False
    optimization_params.push0 = True
    optimization_params.rules_enabled = True
    optimization_params.no_simp = False

    optimization_params.split_storage = False
    optimization_params.split_partition = False

    optimization_params.memory_encoding = "direct"
    optimization_params.push_basic = False
    optimization_params.pop_uninterpreted = False
    optimization_params.order_bounds = True
    optimization_params.empty = False
    optimization_params.encode_terms = "uninterpreted_uf"
    optimization_params.terminal = False
    optimization_params.ac_solver = False

    optimization_params.criteria = "gas"
    optimization_params.size_rules_enabled = True
    optimization_params.direct_soft = False

    optimization_params.at_most = False
    optimization_params.pushed_once = False
    optimization_params.no_output_before_pop = True
    optimization_params.order_conflicts = True

    optimization_params.bound_select = False
    optimization_params.opt_select = False
    optimization_params.forves_enabled = False
    optimization_params.greedy = False
    optimization_params.ub_greedy = False

    return optimization_params

def initialize_folders(final_dir: str):
    csv_dir = f'{final_dir}/csv'

    shutil.rmtree(final_dir, ignore_errors=True)
    for folder in (csv_dir, ):
        Path(folder).mkdir(parents=True, exist_ok=True)


def dict_file_to_contract(contract_csv_file):
    rows = pd.read_csv(contract_csv_file).to_dict(orient='records')
    return {row["ContractAddress"]: row["ContractName"] for row in rows}

def analyze_sfs(sfs_file: str, final_dir: str):
    csv_dir = Path(f'{final_dir}/csv')
    filename = Path(Path(sfs_file).name).stem

    opt_params = initialize_params(sfs_file, csv_dir.joinpath(f"{filename}.csv"))

    print(f'Analyzing {sfs_file}')
    optimize_from_sfs(opt_params)



def run_instance_language(input_file: str, final_dir: str):
    # For now, just considering executing the SFS version
    # Other versions could be added at this level
    analyze_sfs(input_file, final_dir)


def run_experiments(initial_dir: str, final_dir: str, n_cpus):
    # Set how many process to be running in parallel
    # Project folder
    run_combinations = [[file_, final_dir] for file_ in Path(initial_dir).glob("*.json") ]
    Path(final_dir).mkdir(parents=True, exist_ok=True)
    initialize_folders(final_dir)

    with mp.Pool(n_cpus) as p:
        p.starmap(run_instance_language, run_combinations)

if __name__ == "__main__":
    run_experiments(sys.argv[1], sys.argv[2], 10)