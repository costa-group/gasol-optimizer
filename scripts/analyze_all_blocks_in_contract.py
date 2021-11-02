#!/usr/bin/python3
import argparse
import os
import glob
import pathlib
import shlex
import subprocess
import re
import json
import pandas as pd
import sys
import resource
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/global_params")
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/sfs_generator")
from utils import compute_stack_size
from paths import project_path, oms_exec, gasol_path, smt_encoding_path, json_path, z3_exec, bclt_exec, solutions_path
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/smt_encoding")
from encoding_utils import generate_phi_dict
from gasol_encoder import execute_syrup_backend
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/verification")
from sfs_verify import are_equals
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/scripts")
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/solution_generation")
from disasm_generation import generate_disasm_sol
import ir_block
from gasol_optimization import get_sfs_dict
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))
from gasol_asm import preprocess_instructions_plain_text



def modifiable_path_files_init():
    parser = argparse.ArgumentParser()

    parser.add_argument("-solver", "--solver", help="Choose the solver", choices=["z3", "barcelogic", "oms"],
                        required=True)
    parser.add_argument("-tout", metavar='timeout', action='store', type=int, help="timeout in seconds", required=True)
    parser.add_argument("-jsons-folder", metavar='jsons_folder', action='store', type=str,
                        help="folder that contains the jsons to analyze. It must be in the proper format",
                        required=True)
    parser.add_argument("-csv-folder", metavar='csv_folder', action='store', type=str,
                        help="folder that will store the csvs containing the statistics per file. Inside that folder, "
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
    #      --- block_1.json
    #      --- block_2.json
    #      ...
    #   -- contract_2_folder
    #      --- block_1.json
    #      --- block_2.json
    #      ...
    #   ...
    global contracts_dir_path
    contracts_dir_path = args.jsons_folder


def not_modifiable_path_files_init():
    global solver_output_file
    solver_output_file = gasol_path + "solution.txt"

    global final_json_path
    final_json_path = json_path + "block__block0_input.json"

    global final_disasm_blk_path
    final_disasm_blk_path = gasol_path + "block.disasm_blk"


def number_encoding_size(number):
    i = 0
    while number != 0:
        i += 1
        number = number >> 8
    return i


def bytes_required(op_name, val, address_length = 4):
    if op_name == "ASSIGNIMMUTABLE":
        # Number of PushImmutable's with the same hash. Assume 1 (?)
        m_immutableOccurrences = 1
        return 1 + (3 + 32) * m_immutableOccurrences
    elif not op_name.startswith("PUSH") or op_name == "tag":
        return 1
    elif op_name == "PUSH":
        return 1 + max(1, number_encoding_size(int(val,16)))
    elif op_name == "PUSH#[$]" or op_name == "PUSHSIZE":
        return 1 + 4
    elif op_name == "PUSHTAG" or op_name == "PUSHDATA" or op_name == "PUSH[$]":
        return 1 + address_length
    elif op_name == "PUSHLIB" or op_name == "PUSHDEPLOYADDRESS":
        return 1 + 20
    elif op_name == "PUSHIMMUTABLE":
        return 1 + 32
    else:
        raise ValueError("Opcode not recognized")


def bytes_required_initial(op_name, address_length = 4):
    push_match = re.match(re.compile('PUSH([0-9]+)'), op_name)
    if push_match:
        return 1 + max(1, int(push_match.group(1)))
    elif op_name == "ASSIGNIMMUTABLE":
        # Number of PushImmutable's with the same hash. Assume 1 (?)
        m_immutableOccurrences = 1
        return 1 + (3 + 32) * m_immutableOccurrences
    elif not op_name.startswith("PUSH") or op_name == "tag":
        return 1
    elif op_name == "PUSH#[$]" or op_name == "PUSHSIZE":
        return 1 + 4
    elif op_name == "PUSHTAG" or op_name == "PUSHDATA" or op_name == "PUSH[$]":
        return 1 + address_length
    elif op_name == "PUSHLIB" or op_name == "PUSHDEPLOYADDRESS":
        return 1 + 20
    elif op_name == "PUSHIMMUTABLE":
        return 1 + 32
    else:
        raise ValueError("Opcode not recognized")

def total_bytes(instructions_disasm):
    instructions = list(filter(lambda x: x != '', instructions_disasm.split(' ')))
    i, bytes, j = 0, 0, 0
    while i < len(instructions):
        j += 1
        if instructions[i] == "PUSH":
            bytes += bytes_required("PUSH", instructions[i+1])
            i += 2
        elif instructions[i].startswith("PUSH") and not instructions[i].startswith("PUSHDEPLOYADDRESS") \
                    and not instructions[i].startswith("PUSHSIZE"):
            bytes += bytes_required(instructions[i], None)
            i += 2
        else:
            bytes += bytes_required(instructions[i], None)
            i += 1
    return bytes, j


def init():
    modifiable_path_files_init()
    not_modifiable_path_files_init()


def run_command(cmd):
    FNULL = open(os.devnull, 'w')
    solc_p = subprocess.Popen(shlex.split(cmd), stdout=subprocess.PIPE,
                              stderr=FNULL)
    return solc_p.communicate()[0].decode()


def run_and_measure_command(cmd):
    usage_start = resource.getrusage(resource.RUSAGE_CHILDREN)
    solution = run_command(cmd)
    usage_stop = resource.getrusage(resource.RUSAGE_CHILDREN)
    return solution, usage_stop.ru_utime + usage_stop.ru_stime - usage_start.ru_utime - usage_start.ru_stime


def analyze_file_oms(solution):
    pattern = re.compile("\(gas (.*)\)")
    for match in re.finditer(pattern, solution):
        number = int(match.group(1))
        pattern2 = re.compile("range")
        if re.search(pattern2, solution):
            return number, False
        return number, True


def submatch_z3(string):
    subpattern = re.compile("\(interval (.*) (.*)\)")
    for submatch in re.finditer(subpattern, string):
        return int(submatch.group(2))
    return -1


def analyze_file_z3(solution):
    pattern = re.compile("\(gas (.*)\)")
    for match in re.finditer(pattern, solution):
        number = submatch_z3(match.group(1))
        if number == -1:
            return int(match.group(1)), True
        else:
            return number, False


def submatch_barcelogic(string):
    subpattern = re.compile("\(cost (.*)\)")
    for submatch in re.finditer(subpattern, string):
        return int(submatch.group(1))
    return -1


def analyze_file_barcelogic(solution):
    pattern = re.compile("\(optimal (.*)\)")
    for match in re.finditer(pattern, solution):
        return int(match.group(1)), True
    return submatch_barcelogic(solution), False


def analyze_file(solution):
    global solver
    if solver == "oms":
        return analyze_file_oms(solution)
    elif solver == "z3":
        return analyze_file_z3(solution)
    else:
        return analyze_file_barcelogic(solution)


def get_solver_to_execute(block_id):
    global tout

    encoding_file = smt_encoding_path + block_id + "_" + solver + ".smt2"

    if solver == "z3":
        return z3_exec + " -smt2 " + encoding_file
    elif solver == "barcelogic":
        if tout is None:
            return bclt_exec + " -file " + encoding_file
        else:
            return bclt_exec + " -file " + encoding_file + " -tlimit " + str(tout)
    else:
        return oms_exec + " " + encoding_file


def get_tout_found_per_solver(solution):
    global solver
    if solver == "z3":
        return re.search(re.compile("model is not"), solution)
    elif solver == "barcelogic":
        target_gas_cost, _ = analyze_file_barcelogic(solution)
        return target_gas_cost == -1
    else:
        return re.search(re.compile("not enabled"), solution)


if __name__=="__main__":
    global args
    init()
    pathlib.Path(gasol_path).mkdir(parents=True, exist_ok=True)
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
                file_results['original_bytes'] = sum([bytes_required_initial(instr) for instr in original_instrs])
                initial_stack = data['src_ws']

            # When init_progr_length > 40, we assume a timeout is produced
            if init_program_length > 40:
                file_results['no_model_found'] = True
                file_results['shown_optimal'] = False
                file_results['solver_time_in_sec'] = 10 * ( 1 + sum([1 if instr['storage'] else 0 for instr in user_instr]))
                rows_list.append(file_results)
                continue

            try:
                execute_syrup_backend(args, file)
            except:
                with open(results_dir + "incorrect.txt", 'a') as f:
                    print(file,file=f)
                continue

            smt_exec_command = get_solver_to_execute(block_id)
            solution, executed_time = run_and_measure_command(smt_exec_command)
            executed_time = round(executed_time, 3)
            tout_pattern = get_tout_found_per_solver(solution)

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

                target_gas_cost, shown_optimal = analyze_file(solution)
                # Sometimes, solution reached is not good enough
                file_results['target_gas_cost'] = target_gas_cost
                file_results['shown_optimal'] = shown_optimal

                with open(solver_output_file, 'w') as f:
                    f.write(solution)

                generate_disasm_sol(contract_name, block_id, bs, user_instr, solution)
                instruction_final_solution = solutions_path + contract_name + "/disasm/" + block_id + "_optimized.disasm_opt"
                gas_final_solution = solutions_path + contract_name + "/total_gas/" + block_id + "_real_gas.txt"

                with open(instruction_final_solution, 'r') as f:
                    instructions_disasm = f.read()
                    file_results['target_disasm'] = instructions_disasm
                    number_bytes, number_of_instructions = total_bytes(instructions_disasm)
                    file_results['bytes_required'] = number_bytes
                    file_results['saved_bytes'] = file_results['original_bytes'] - number_bytes
                    file_results['final_progr_len'] = number_of_instructions

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
