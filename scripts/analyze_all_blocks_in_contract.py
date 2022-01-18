#!/usr/bin/python3
import argparse
import glob
import json
import os
import pathlib
import re
import resource
import shlex
import subprocess
import sys

import pandas as pd

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))

import global_params.paths as paths
from sfs_generator.utils import (compute_stack_size, get_ins_size,
                                 get_ins_size_seq)
from smt_encoding.encoding_utils import generate_phi_dict
from smt_encoding.gasol_encoder import execute_syrup_backend
from solution_generation.disasm_generation import generate_disasm_sol
from verification.sfs_verify import are_equals
from solution_generation.solver_output_generation import obtain_solver_output
from properties.properties_from_solver_output import analyze_file, get_tout_found_per_solver


def modifiable_path_files_init():
    parser = argparse.ArgumentParser()

    parser.add_argument("-solver", "--solver", help="Choose the solver", choices=["z3", "barcelogic", "oms"],
                        required=True)
    parser.add_argument("-tout", metavar='timeout', action='store', type=int, help="timeout in seconds", required=True)
    parser.add_argument("-jsons-folder", metavar='jsons_folder', action='store', type=str,
                        help="folder that contains the jsons to analyze. It must be in the proper format",
                        required=True)
    parser.add_argument("-csv-folder", metavar='csv_folder', action='store', type=str,
                        help="folder that will store the csvs containing the properties per file. Inside that folder, "
                             "another subfolder is created: solver_name + _ + timeout + 's'", required=True)
    parser.add_argument('-at-most', help='add a constraint for each uninterpreted function so that they are used at most once',
                    action='store_true', dest='at_most')
    parser.add_argument('-pushed-once', help='add a constraint to indicate that each pushed value is pushed at least once',
                    action='store_true', dest='pushed_once')
    parser.add_argument("-inequality-gas-model", dest='inequality_gas_model', action='store_true',
                    help="Soft constraints with inequalities instead of equalities")
    parser.add_argument("-no-output-before-pop", help='add a constraint representing the fact that the previous instruction'
                                                  'of a pop can only be a instruction that does not produce an element',
                    action='store_true', dest='no_output_before_pop')
    parser.add_argument("-disable-default-encoding", dest='default_encoding', action='store_false',
                    help="Disable the constraints added for the default encoding")
    parser.add_argument("-instruction-order", help='add a constraint representing the order among instructions',
                    action='store_true', dest='instruction_order')
    parser.add_argument("-storage", "--storage", help="Split using SSTORE, MSTORE and MSTORE8", action="store_true")
    parser.add_argument("-bytecode-size-soft-constraints", dest='bytecode_size_soft_constraints', action='store_true',
                    help="")
    parser.add_argument("-memory-encoding", help="Choose the memory encoding model", choices = ["l_vars","direct"], default="l_vars")
    parser.add_argument("-number-instruction-gas-model", dest='number_instruction_gas_model', action='store_true',
                    help="Soft constraints for optimizing the number of instructions instead of gas")



    global args
    args = parser.parse_args()

    # Selected solver. Only three possible values:
    # "oms", "z3", "barcelogic"
    global solver
    solver = args.solver

    # Timeout in s
    global tout
    tout = args.tout

    # Folder in which the csvs are stored. A csv is generated per each analyzed file
    global results_dir
    results_dir = args.csv_folder
    if results_dir[-1] != "/":
        results_dir += "/"

    results_dir += solver + "_" + str(tout) + "s/"

    # Folder which contains the json files to analyze. Must follow this structure:
    # - main_folder
    #   -- contract_1_folder
    #      --- jsons
    #          --- block_1.json
    #          --- block_2.json
    #      ...
    #   -- contract_2_folder
    #      --- jsons
    #          --- block_1.json
    #          --- block_2.json
    #      ...
    #   ...
    global contracts_dir_path
    contracts_dir_path = args.jsons_folder


def not_modifiable_path_files_init():
    global solver_output_file
    solver_output_file = paths.gasol_path + "solution.txt"

    global final_json_path
    final_json_path = paths.json_path + "block__block0_input.json"

    global final_disasm_blk_path
    final_disasm_blk_path = paths.gasol_path + "block.disasm_blk"


def init():
    modifiable_path_files_init()
    not_modifiable_path_files_init()


if __name__=="__main__":
    global args
    init()
    pathlib.Path(paths.gasol_path).mkdir(parents=True, exist_ok=True)
    pathlib.Path(results_dir).mkdir(parents=True, exist_ok=True)

    already_analyzed_contracts = glob.glob(results_dir + "/*.csv")

    for contract_path in [f.path for f in os.scandir(contracts_dir_path) if f.is_dir()]:
        rows_list = []
        log_dict = dict()
        contract_name = contract_path.split('/')[-1]
        csv_file = results_dir + contract_name + "_results_" + solver + ".csv"


        for file in glob.glob(contract_path + "/jsons/*.json"):
            with open(results_dir + "report.txt", 'w') as f:
                f.write("Last analyzed file: " + file)

            file_results = dict()
            block_id = file.split('/')[-1].rstrip(".json")
            file_results['block_id'] = block_id

            print("Optimizing block " + block_id + "...")
            print("")

            with open(file) as path:
                data = json.load(path)
                source_gas_cost = data['current_cost']
                file_results['source_gas_cost'] = int(source_gas_cost)
                init_program_length = data['init_progr_len']
                file_results['init_progr_len'] = int(init_program_length)
                bs = data['max_sk_sz']
                user_instr = data['user_instrs']
                final_stack = data['tgt_ws']
                file_results['number_of_necessary_uninterpreted_instructions'] = len(user_instr)
                file_results['number_of_necessary_push'] = len(generate_phi_dict(user_instr, final_stack))
                original_instrs = data['original_instrs']
                file_results['original_instrs'] = original_instrs
                old_bytes = get_ins_size_seq(original_instrs)
                file_results['original_bytes'] = old_bytes
                initial_stack = data['src_ws']

            bclt_timeout = 10 * ( 1 + sum([1 if instr['storage'] else 0 for instr in user_instr]))
            # When init_progr_length > 40, we assume a timeout is produced
            if init_program_length > 40:
                file_results['no_model_found'] = True
                file_results['shown_optimal'] = False
                file_results['solver_time_in_sec'] = bclt_timeout
                rows_list.append(file_results)
                continue

            try:
                execute_syrup_backend(args, file)
            except:
                with open(results_dir + "incorrect.txt", 'a') as f:
                    print(file,file=f)
                continue

            solution, executed_time = obtain_solver_output(block_id, solver, bclt_timeout)
            executed_time = round(executed_time, 3)
            tout_pattern = get_tout_found_per_solver(solution, solver)
            if tout_pattern:
                if re.search(re.compile("unsat"), solution):
                    with open(results_dir + "unsat.txt", 'a') as f:
                        print(file,file=f)

                file_results['no_model_found'] = True
                file_results['shown_optimal'] = False
                file_results['solver_time_in_sec'] = executed_time

            else:

                file_results['no_model_found'] = False
                file_results['solver_time_in_sec'] = executed_time

                target_gas_cost, shown_optimal = analyze_file(solution, solver)
                # Sometimes, solution reached is not good enough
                file_results['target_gas_cost'] = target_gas_cost
                file_results['shown_optimal'] = shown_optimal

                with open(solver_output_file, 'w') as f:
                    f.write(solution)

                generate_disasm_sol(contract_name, block_id, bs, user_instr, solution)
                instruction_final_solution = paths.solutions_path + contract_name + "/disasm/" + block_id + "_optimized.disasm_opt"
                gas_final_solution = paths.solutions_path + contract_name + "/total_gas/" + block_id + "_real_gas.txt"

                with open(instruction_final_solution, 'r') as f:
                    instructions_disasm = f.read()
                    file_results['target_disasm'] = instructions_disasm
                    number_bytes = get_ins_size_seq(instructions_disasm)
                    file_results['bytes_required'] = number_bytes
                    file_results['saved_bytes'] = file_results['original_bytes'] - number_bytes
                    file_results['final_progr_len'] = 0

                    # Generate the disasm_blk file, including the size of the initial stack in the first
                    # line and the disasm instructions in the second one. This will be used to check if the
                    # initial SFS and the new generated one are equivalent
                    with open(final_disasm_blk_path, 'w') as f2:
                        print(len(initial_stack), file=f2)
                        print(instructions_disasm, file=f2)

                with open(gas_final_solution, 'r') as f:
                    file_results['real_gas'] = f.read()
                    # It cannot be negative
                    file_results['saved_gas'] = file_results['source_gas_cost'] - int(file_results['real_gas'])

            rows_list.append(file_results)

        df = pd.DataFrame(rows_list, columns=['block_id', 'target_gas_cost', 'real_gas',
                                              'shown_optimal', 'no_model_found', 'source_gas_cost', 'saved_gas',
                                              'solver_time_in_sec', 'target_disasm', 'init_progr_len',
                                              'final_progr_len', 'number_of_necessary_uninterpreted_instructions',
                                              'number_of_necessary_push', 'bytes_required', 'original_instrs', 'original_bytes', 'saved_bytes'])
        df.to_csv(csv_file)

        print("Intermediate files stored at " + paths.gasol_path)

