import json
import os
import multiprocessing as mp
import tempfile
from pathlib import Path
import sys
import uuid
from gasol_asm import optimize_from_sfs, OptimizationParams
import global_params.paths as paths

def modify_params():
    paths.gasol_folder = "gasol_" + uuid.uuid4().hex
    paths.gasol_path = paths.tmp_path + paths.gasol_folder + "/"
    paths.json_path = paths.gasol_path + "jsons"
    paths.smt_encoding_path = paths.gasol_path + "smt_encoding/"
    paths.solutions_path = paths.gasol_path + "solutions/"
    paths.dot_path = paths.gasol_path + "dot/"


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
    optimization_params.timeout = 240
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

def combine_jsons(original_folder: str):
    """
    Combines all SFS JSON into a single element
    """
    combined_json = {}

    for file_ in Path(original_folder).glob("*.json"):
        with open(file_, 'r') as f:
            json_file = json.load(f)

        # Modify the params for the current examples
        json_file["max_progr_len"] = 20
        json_file["init_progr_len"] = 20
        json_file["max_sk_sz"] = 8
        json_file["is_revert"] = False

        basename = Path(Path(file_).name).stem
        combined_json[basename] = json_file

    return combined_json

def initialize_folders(final_dir: str):
    csv_dir = f'{final_dir}/csv'

    # shutil.rmtree(final_dir, ignore_errors=True)
    for folder in (csv_dir, ):
        Path(folder).mkdir(parents=True, exist_ok=True)

def analyze_sfs(sfs_folder: str, final_dir: str):
    csv_dir = Path(f'{final_dir}/csv')
    folder_name = Path(sfs_folder).name

    combined_json = combine_jsons(sfs_folder)

    _, filename = tempfile.mkstemp(".json")

    with open(filename, 'w') as f:
        json.dump(combined_json, f)

    opt_params = initialize_params(filename, csv_dir.joinpath(f"{folder_name}.csv"))
    modify_params()

    print(f'Analyzing {folder_name} {paths.gasol_path}')
    optimize_from_sfs(opt_params)
    os.unlink(filename)


def run_instance_language(input_file: str, final_dir: str):
    # For now, just considering executing the SFS version
    # Other versions could be added at this level
    analyze_sfs(input_file, final_dir)


def run_experiments(initial_dir: str, final_dir: str, n_cpus):
    # Set how many process to be running in parallel
    # Project folder
    run_combinations = [[folder_, final_dir] for folder_ in Path(initial_dir).iterdir()
                        if Path(folder_).is_dir()
                        and not Path(final_dir).joinpath("csv").joinpath(Path(folder_).name + ".csv").exists()
                        ]
    Path(final_dir).mkdir(parents=True, exist_ok=True)
    initialize_folders(final_dir)

    with mp.Pool(n_cpus) as p:
        p.starmap(run_instance_language, run_combinations)

if __name__ == "__main__":
    run_experiments(sys.argv[1], sys.argv[2], 28)