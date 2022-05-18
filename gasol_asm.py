#!/usr/bin/python3
import argparse
import collections
import json
import os
import shutil
import sys
from typing import Tuple
from copy import deepcopy
from timeit import default_timer as dtimer

import pandas as pd

import global_params.constants as constants
import global_params.paths as paths
import sfs_generator.ir_block as ir_block
import sfs_generator.opcodes as op
from properties.properties_from_asm_json import (
    bytes_required_asm, compute_number_of_instructions_in_asm_json_per_file,
    preprocess_instructions)
from properties.properties_from_solver_output import analyze_file
from sfs_generator.gasol_optimization import get_sfs_dict
from sfs_generator.parser_asm import (parse_asm,
                                      parse_asm_representation_from_blocks,
                                      parse_blocks_from_plain_instructions)
from sfs_generator.rebuild_asm import rebuild_asm
from sfs_generator.utils import (compute_stack_size, get_ins_size_seq,
                                 is_constant_instruction, isYulInstruction,
                                 isYulKeyword)
from smt_encoding.gasol_encoder import (execute_syrup_backend,
                                        execute_syrup_backend_combined,
                                        generate_theta_dict_from_sequence)
from solution_generation.disasm_generation import (
    generate_disasm_sol_from_output, generate_info_from_solution,
    generate_sub_block_asm_representation_from_log,
    generate_sub_block_asm_representation_from_output,
    obtain_log_representation_from_solution, read_initial_dicts_from_files)
from solution_generation.solver_output_generation import obtain_solver_output
from verification.sfs_verify import verify_block_from_list_of_sfs
from verification.solver_solution_verify import (
    check_solver_output_is_correct, generate_solution_dict)
from solution_generation.optimize_from_sub_blocks import rebuild_optimized_asm_block
from sfs_generator.asm_block import AsmBlock

def init():
    global previous_gas
    previous_gas = 0

    global new_gas
    new_gas = 0

    global previous_size
    previous_size = 0

    global new_size
    new_size = 0

    global statistics_rows
    statistics_rows = []

    global total_time
    total_time = 0

def clean_dir():
    ext = ["rbr", "csv", "sol", "bl", "disasm", "json"]
    if paths.gasol_folder in os.listdir(paths.tmp_path):
        for elem in os.listdir(paths.gasol_path):
            last = elem.split(".")[-1]
            if last in ext:
                os.remove(paths.gasol_path+elem)

        if "jsons" in os.listdir(paths.gasol_path):
            shutil.rmtree(paths.gasol_path + "jsons")

        if "disasms" in os.listdir(paths.gasol_path):
            shutil.rmtree(paths.gasol_path + "disasms")

        if "smt_encoding" in os.listdir(paths.gasol_path):
            shutil.rmtree(paths.gasol_path + "smt_encoding")

        if "solutions" in os.listdir(paths.gasol_path):
            shutil.rmtree(paths.gasol_path + "solutions")


def remove_last_constant_instructions(instructions):
    constant = True
    cons_instructions = []
    
    while constant and instructions != []:
        ins = instructions[-1]
        constant = is_constant_instruction(ins)
        if constant:
            cons_instructions.append(ins)
            instructions.pop()

    if instructions == []:
        instructions = cons_instructions
        cons_instructions =  []
        
    new_stack_size = compute_stack_size(instructions)
    return new_stack_size, cons_instructions[::-1]


def compute_original_sfs_with_simplifications(instructions, stack_size, block_id, block_name,
                                              storage, last_const, size_abs, partition, pop_flag, push_flag,revert_return):

    block_ins = list(filter(lambda x: x not in constants.beginning_block and x not in constants.end_block, instructions))

    if ("REVERT" in instructions or "RETURN" in instructions) and revert_return:
        revert_flag = True
    else:
        revert_flag = False
        
    if last_const:
        new_stack_size , rest_instructions = remove_last_constant_instructions(block_ins)
        
    else:
        new_stack_size = stack_size
    
    block_data = {"instructions": block_ins, "input": new_stack_size}

    fname = args.input_path.split("/")[-1].split(".")[0]
    exit_code, subblocks_list = \
        ir_block.evm2rbr_compiler(file_name = fname, block=block_data, block_name=block_name, block_id=block_id,
                                  simplification=True, storage=storage, size = size_abs, part = partition,pop =
                                  pop_flag, push = push_flag, revert = revert_flag)

    sfs_dict = get_sfs_dict()

    return sfs_dict, subblocks_list


# Given the sequence of bytecodes, the initial stack size, the contract name and the
# block id, returns the output given by the solver, the name given to that block and current gas associated
# to that sequence.
def optimize_block(sfs_dict, timeout, size = False):

    block_solutions = []
    # SFS dict of syrup contract contains all sub-blocks derived from a block after splitting
    for block_name in sfs_dict:
        sfs_block = sfs_dict[block_name]

        current_cost = sfs_block['current_cost']
        original_instr = sfs_block['original_instrs']
        current_size = get_ins_size_seq(original_instr)
        user_instr = sfs_block['user_instrs']
        initial_program_length = sfs_block['init_progr_len']

        args_i = argparse.Namespace()
        args_i.solver = "oms"
        args_i.instruction_order = True
        args_i.bytecode_size_soft_constraints = size
        args_i.default_encoding = True
        args_i.memory_encoding = "l_vars"
        execute_syrup_backend(args_i, sfs_block, block_name=block_name, timeout=timeout)

        if args.backend:

            if initial_program_length > 40:
                solver_output = "unsat"
                solver_time = 0
            # At this point, solution is a string that contains the output directly
            # from the solver
            else:
                solver_output, solver_time = obtain_solver_output(block_name, "oms", timeout)
            block_solutions.append((solver_output, block_name, original_instr, current_cost, current_size, user_instr, solver_time))

    return block_solutions


# Given the log file loaded in json format, current block and the contract name, generates three dicts: one that
# contains the sfs from each block, the second one contains the sequence of instructions and
# the third one is a set that contains all block ids.
def generate_sfs_dicts_from_log(block, json_log,storage, last_const, size_abs, partition, pop_flag, push_flag,revert_return):
    stack_size = block.source_stack
    block_name = block.block_name
    block_id = block.block_id

    instructions =  block.instructions_to_optimize_plain()

    contracts_dict, sub_block_list = compute_original_sfs_with_simplifications(instructions, stack_size, block_id, block_name,
                                                         storage, last_const, size_abs, partition, pop_flag,
                                                         push_flag,revert_return)
    syrup_contracts = contracts_dict["syrup_contract"]

    # Contains sfs blocks considered to check the SMT problem. Therefore, a block is added from
    # sfs_original iff solver could not find an optimized solution, and from sfs_dict otherwise.
    optimized_sfs_dict = {}

    # Dict that contains all instr sequences
    instr_sequence_dict = {}

    # Set that contains all ids
    ids = set()

    # We need to inspect all sub-blocks in the sfs dict.
    for block_id in syrup_contracts:

        ids.add(block_id)

        # If the id is not at json log, this means it has not been optimized
        if block_id not in json_log:
            continue

        instr_sequence = json_log[block_id]

        sfs_block = syrup_contracts[block_id]


        optimized_sfs_dict[block_id] = sfs_block
        instr_sequence_dict[block_id] = instr_sequence

    return syrup_contracts, optimized_sfs_dict, sub_block_list, instr_sequence_dict, ids


# Verify information derived from log file is correct
def check_log_file_is_correct(sfs_dict, instr_sequence_dict):
    execute_syrup_backend_combined(sfs_dict, instr_sequence_dict, "verify", "oms")

    solver_output, time_check = obtain_solver_output("verify", "oms", 0)

    return check_solver_output_is_correct(solver_output)



# Given a dict with the sfs from each block and another dict that contains whether previous block was optimized or not,
# generates the corresponding solution. All checks are assumed to have been done previously
def optimize_asm_block_from_log(block, sfs_dict, sub_block_list, instr_sequence_dict):
    # Optimized blocks. When a block is not optimized, None is pushed to the list.
    optimized_blocks = {}

    for sub_block_name, sfs_sub_block in sfs_dict.items():

        if sub_block_name not in instr_sequence_dict:
            optimized_blocks[sub_block_name] = None
        else:
            log_info = instr_sequence_dict[sub_block_name]
            user_instr = sfs_sub_block['user_instrs']
            bs = sfs_sub_block['max_sk_sz']

            _, instruction_theta_dict, opcodes_theta_dict, gas_theta_dict, values_dict = generate_theta_dict_from_sequence(
                bs, user_instr)

            new_sub_block = generate_sub_block_asm_representation_from_log(log_info, opcodes_theta_dict,
                                                                              instruction_theta_dict,
                                                                              gas_theta_dict, values_dict)
            optimized_blocks[sub_block_name] = new_sub_block

    new_block = rebuild_optimized_asm_block(block, sub_block_list, optimized_blocks)

    return new_block


def optimize_asm_from_log(file_name, json_log, output_file, storage = False, last_const = False, size_abs = False,
                          partition = False, pop_flag = False, push_flag = False, revert_return = False):
    asm = parse_asm(file_name)

    # Blocks from all contracts are checked together. Thus, we first will obtain the needed
    # information from each block
    sfs_dict_to_check, instr_sequence_dict, file_ids = {}, {}, set()
    contracts = []

    for c in asm.contracts:

        new_contract = deepcopy(c)

        # If it does not have the asm field, then we skip it, as there are no instructions to optimize
        if not c.has_asm_field:
            contracts.append(new_contract)
            continue

        contract_name = (c.contract_name.split("/")[-1]).split(":")[-1]
        init_code = c.init_code
        init_code_blocks = []

        print("\nAnalyzing Init Code of: " + contract_name)
        print("-----------------------------------------\n")
        for block in init_code:

            if block.instructions_to_optimize_plain() == []:
                init_code_blocks.append(deepcopy(block))
                continue

            sfs_all, sfs_optimized, sub_block_list, instr_sequence_dict_block, block_ids = \
                generate_sfs_dicts_from_log(block, json_log, storage, last_const, size_abs, partition, pop_flag,
                                            push_flag,revert_return)

            new_block = optimize_asm_block_from_log(block, sfs_all, sub_block_list, instr_sequence_dict_block)
            sfs_dict_to_check.update(sfs_optimized)
            instr_sequence_dict.update(instr_sequence_dict_block)
            file_ids.update(block_ids)
            init_code_blocks.append(new_block)

        new_contract.init_code = init_code_blocks

        print("\nAnalyzing Runtime Code of: " + contract_name)
        print("-----------------------------------------\n")
        for identifier in c.get_data_ids_with_code():
            blocks = c.get_run_code(identifier)

            run_code_blocks = []

            for block in blocks:

                if block.instructions_to_optimize_plain() == []:
                    run_code_blocks.append(deepcopy(block))
                    continue

                sfs_all, sfs_optimized, sub_block_list, instr_sequence_dict_block, block_ids = \
                    generate_sfs_dicts_from_log(block, json_log, storage,last_const, size_abs, partition, pop_flag,
                                                push_flag, revert_return)

                new_block = optimize_asm_block_from_log(block, sfs_all, sub_block_list, instr_sequence_dict_block)
                sfs_dict_to_check.update(sfs_optimized)
                instr_sequence_dict.update(instr_sequence_dict_block)
                file_ids.update(block_ids)
                run_code_blocks.append(new_block)

            new_contract.set_run_code(identifier, run_code_blocks)

        contracts.append(new_contract)

    # We check ids in json log file matches the ones generated from the source file
    if not set(json_log.keys()).issubset(file_ids):
        print("Log file does not match source file")
    else:
        not_empty = {k : v for k,v in sfs_dict_to_check.items() if v != []}
        correct = check_log_file_is_correct(not_empty, instr_sequence_dict)
        if correct:
            print("Solution generated from log file has been verified correctly")
            new_asm = deepcopy(asm)
            new_asm.contracts = contracts

            with open(output_file, 'w') as f:
                f.write(json.dumps(rebuild_asm(new_asm)))

            print("")
            print("Optimized code stored at " + output_file)
        else:
            print("Log file does not contain a valid solution")


def optimize_isolated_asm_block(block_name,output_file, csv_file, timeout=10, storage= False, last_const = False,
                                size_abs = False, partition = False, pop = False, push = False, revert = False):
    global statistics_rows

    with open(block_name,"r") as f:        
        instructions = f.read()

    blocks = parse_blocks_from_plain_instructions(instructions)
    asm_blocks = []

    for old_block in blocks:
        asm_block, _ = optimize_asm_block_asm_format(old_block, timeout, storage, last_const, size_abs, partition, pop, push, revert)

        if not compare_asm_block_asm_format(old_block, asm_block):
            print("Comparison failed, so initial block is kept")
            print(old_block.to_plain())
            print(asm_block.to_plain())
            print("")
            asm_block = old_block

        update_gas_count(old_block, asm_block)
        update_size_count(old_block, asm_block)
        asm_blocks.append(asm_block)

        
    if args.backend:
        df = pd.DataFrame(statistics_rows)
        df.to_csv(csv_file)
        print("")
        print("Initial sequence (basic block per line):")
        print('\n'.join([old_block.to_plain_with_byte_number() for old_block in blocks]))
        print("")
        print("Optimized sequence (basic block per line):")
        print('\n'.join([asm_block.to_plain_with_byte_number() for asm_block in asm_blocks]))
        with open(output_file, 'w') as f:
            f.write('\n'.join([asm_block.to_plain_with_byte_number() for asm_block in asm_blocks]))

        df = pd.DataFrame(statistics_rows)
        df.to_csv(csv_file)


def update_gas_count(old_block : AsmBlock, new_block : AsmBlock):
    global previous_gas
    global new_gas

    previous_gas += old_block.gas_spent
    new_gas += new_block.gas_spent


def update_size_count(old_block : AsmBlock, new_block : AsmBlock):
    global previous_size
    global new_size

    previous_size += old_block.bytes_required
    new_size += new_block.bytes_required


# Due to intra block optimization, we need to be wary of those cases in which the optimized outcome is determined
# from other blocks. In particular, when a sub block starts with a POP opcode, then it can be optimized iff the
# previous block has been optimized
def filter_optimized_blocks_by_intra_block_optimization(asm_sub_blocks, optimized_sub_blocks):
    final_sub_blocks = []

    current_pop_streak_blocks = []

    previous_block_starts_with_pop = False
    # Traverse from right to left
    for asm_sub_block, optimized_sub_block in zip(reversed(asm_sub_blocks), reversed(optimized_sub_blocks)):
        if asm_sub_block[0].disasm == "POP":
            current_pop_streak_blocks.append(deepcopy(optimized_sub_block))
            previous_block_starts_with_pop = True
        elif previous_block_starts_with_pop:
            current_pop_streak_blocks.append(deepcopy(optimized_sub_block))

            # All elements are not None, so the optimization can be applied
            if all(current_pop_streak_blocks):
                final_sub_blocks.extend(current_pop_streak_blocks)
            # Otherwise, all optimized blocks must be set to None

            else:
                none_pop_blocks = [None] * len(current_pop_streak_blocks)
                final_sub_blocks.extend(none_pop_blocks)

            previous_block_starts_with_pop = False
            current_pop_streak_blocks = []
        else:
            final_sub_blocks.append(deepcopy(optimized_sub_block))
            previous_block_starts_with_pop = False

    # Final check in case first block also starts with a POP instruction
    if previous_block_starts_with_pop:
        if all(current_pop_streak_blocks):
            final_sub_blocks.extend(current_pop_streak_blocks)
        else:
            none_pop_blocks = [None] * len(current_pop_streak_blocks)
            final_sub_blocks.extend(none_pop_blocks)

    # Finally, as we were working with reversed list, we reverse the solution to obtain the proper one
    return list(reversed(final_sub_blocks))

# Given an asm_block and its contract name, returns the asm block after the optimization
def optimize_asm_block_asm_format(block, timeout, storage, last_const, size_abs, partition,pop_flag, push_flag, revert_return):
    global statistics_rows
    global total_time

    stack_size = block.source_stack
    block_id = block.block_id
    block_name = block.block_name

    new_block = deepcopy(block)

    # Optimized blocks. When a block is not optimized, None is pushed to the list.
    optimized_blocks = {}

    log_dicts = {}

    instructions =  block.instructions_to_optimize_plain()

    # No instructions to optimize
    if instructions == []:
        return new_block, {}

    contracts_dict, sub_block_list = compute_original_sfs_with_simplifications(instructions,stack_size,block_id,
                                                                               block_name,storage, last_const,size_abs,
                                                                               partition,pop_flag, push_flag, revert_return)

    sfs_dict = contracts_dict["syrup_contract"]

    if not args.backend:
        optimize_block(sfs_dict, timeout, size_abs)
        return new_block, {}

    for solver_output, sub_block_name, original_instr, current_cost, current_length, user_instr, solver_time \
            in optimize_block(sfs_dict, timeout, size_abs):

        # We weren't able to find a solution using the solver, so we just update
        if not check_solver_output_is_correct(solver_output):
            optimized_blocks[sub_block_name] = None
            statistics_row = {"block_id": sub_block_name, "model_found": False, "shown_optimal": False,
                              "previous_solution": original_instr, "solver_time_in_sec": round(solver_time, 3),
                              "saved_size": 0, "saved_gas": 0}

            statistics_rows.append(statistics_row)
            total_time += solver_time
            continue

        bs = sfs_dict[sub_block_name]['max_sk_sz']

        _, instruction_theta_dict, opcodes_theta_dict, gas_theta_dict, values_dict = generate_theta_dict_from_sequence(bs, user_instr)

        
        instruction_output, _, pushed_output, optimized_cost = \
            generate_info_from_solution(solver_output, opcodes_theta_dict, instruction_theta_dict,
                                        gas_theta_dict, values_dict)

        new_sub_block = generate_sub_block_asm_representation_from_output(solver_output, opcodes_theta_dict,
                                                                          instruction_theta_dict,
                                                                          gas_theta_dict, values_dict)
        _, shown_optimal = analyze_file(solver_output, "oms")
        optimized_length = sum([instr.bytes_required for instr in new_sub_block])

        statistics_row = {"block_id": sub_block_name, "solver_time_in_sec": round(solver_time, 3), "saved_size": current_length - optimized_length,
                          "saved_gas": current_cost - optimized_cost, "model_found": True, "shown_optimal": shown_optimal,
                          "previous_solution": original_instr, "solution_found": ' '.join([instr.to_plain() for instr in new_sub_block])}

        statistics_rows.append(statistics_row)
        total_time += solver_time

        if (not size_abs and current_cost > optimized_cost) or (size_abs and current_length > optimized_length) :
            optimized_blocks[sub_block_name] = new_sub_block
            log_dicts[sub_block_name] = generate_solution_dict(solver_output)
        else:
            optimized_blocks[sub_block_name] = None

    new_block = rebuild_optimized_asm_block(block, sub_block_list, optimized_blocks)

    return new_block, log_dicts


def compare_asm_block_asm_format(old_block : AsmBlock, new_block : AsmBlock,storage = False, last_const = False, size_abs = False, partition = False, pop = False, push = False, revert = False):

    old_instructions =  old_block.instructions_to_optimize_plain()

    old_sfs_information, _ = compute_original_sfs_with_simplifications(old_instructions, old_block.source_stack,
                                                                       old_block.block_id, old_block.block_name,
                                                                       False, last_const, size_abs, False, pop, push, revert)

    old_sfs_dict = old_sfs_information["syrup_contract"]

    new_instructions =  new_block.instructions_to_optimize_plain()

    new_sfs_information, _ = compute_original_sfs_with_simplifications(new_instructions, new_block.source_stack,
                                                                       new_block.block_id, new_block.block_name,
                                                                       False, last_const, size_abs, False, pop, push, revert)

    new_sfs_dict = new_sfs_information["syrup_contract"]

    final_comparison = verify_block_from_list_of_sfs(old_sfs_dict, new_sfs_dict)

    # We also must check intermediate instructions match i.e those that are not sub blocks
    initial_instructions_old = old_block.instructions_initial_bytecode()
    initial_instructions_new = new_block.instructions_initial_bytecode()

    final_instructions_old = old_block.instructions_final_bytecode()
    final_instructions_new = new_block.instructions_final_bytecode()

    return final_comparison and (initial_instructions_new == initial_instructions_old) and \
           final_instructions_new == final_instructions_old


def optimize_asm_in_asm_format(file_name, output_file, csv_file, log_file, timeout=10, log=False, storage= False, last_const = False, size_abs = False, partition = False, pop = False, push = False, revert = False):
    global statistics_rows

    asm = parse_asm(file_name)
    log_dicts = {}
    contracts = []

    for c in asm.contracts:

        new_contract = deepcopy(c)

        # If it does not have the asm field, then we skip it, as there are no instructions to optimize
        if not c.has_asm_field:
            contracts.append(new_contract)
            continue

        contract_name = (c.contract_name.split("/")[-1]).split(":")[-1]
        init_code = c.init_code

        print("\nAnalyzing Init Code of: " + contract_name)
        print("-----------------------------------------\n")

        init_code_blocks = []

        for old_block in init_code:
            optimized_block, log_element = optimize_asm_block_asm_format(old_block, timeout, storage, last_const,size_abs,partition, pop, push, revert)

            if not compare_asm_block_asm_format(old_block, optimized_block):
                print("Comparison failed, so initial block is kept")
                print(old_block.to_plain())
                print(optimized_block.to_plain())
                print("")
                optimized_block = old_block
                log_element = {}

            log_dicts.update(log_element)
            init_code_blocks.append(optimized_block)

            # Deployment size is not considered when measuring it
            update_gas_count(old_block, optimized_block)

        new_contract.init_code = init_code_blocks

        print("\nAnalyzing Runtime Code of: " + contract_name)
        print("-----------------------------------------\n")
        for identifier in c.get_data_ids_with_code():
            blocks = c.get_run_code(identifier)

            run_code_blocks = []
            for old_block in blocks:
                optimized_block, log_element = optimize_asm_block_asm_format(old_block, timeout, storage, last_const,size_abs,partition, pop, push, revert)
                
                if not compare_asm_block_asm_format(old_block, optimized_block):
                    print("Comparison failed, so initial block is kept")
                    print(old_block.to_plain())
                    print(optimized_block.to_plain())
                    print("")
                    optimized_block = old_block
                    log_element = {}

                log_dicts.update(log_element)
                run_code_blocks.append(optimized_block)

                update_gas_count(old_block, optimized_block)
                update_size_count(old_block, optimized_block)

            new_contract.set_run_code(identifier, run_code_blocks)

        contracts.append(new_contract)

    new_asm = deepcopy(asm)
    new_asm.contracts = contracts

    if log:
        with open(log_file, "w") as log_f:
            json.dump(log_dicts, log_f)

    if args.backend:

        with open(output_file, 'w') as f:
            f.write(json.dumps(rebuild_asm(new_asm)))

        df = pd.DataFrame(statistics_rows)
        df.to_csv(csv_file)


def final_file_names(args : argparse.Namespace) -> Tuple[str, str, str]:
    input_file_name = args.input_path.split("/")[-1].split(".")[0]

    if args.output_path is None:
        if args.block:
            output_file = input_file_name + "_optimized.txt"
        elif args.log_path is not None:
            output_file = input_file_name + "_optimized_from_log.json_solc"
        else:
            output_file = input_file_name + "_optimized.json_solc"
    else:
        output_file = args.output_path

    if args.csv_path is None:
        csv_file = input_file_name + "_statistics.csv"
    else:
        csv_file = args.csv_path

    if args.log_stored_final is None:
        log_file = input_file_name + ".log"
    else:
        log_file = args.log_stored_final

    return output_file, csv_file, log_file


if __name__ == '__main__':
    global previous_gas
    global new_gas
    global previous_size
    global new_size
    global total_time

    init()
    clean_dir()
    ap = argparse.ArgumentParser(description='GASOL tool')
    ap.add_argument('input_path', help='Path to input file that contains the asm')
    ap.add_argument("-bl", "--block", help ="Enable analysis of a single asm block", action = "store_true")
    ap.add_argument("-tout", metavar='timeout', action='store', type=int,
                    help="Timeout in seconds. By default, set to 10s per block.", default=10)
    ap.add_argument("-optimize-from-log", dest='log_path', action='store', metavar="log_file",
                        help="Generates the same optimized bytecode than the one associated to the log file")
    ap.add_argument("-log", "--generate-log", help ="Enable log file for Etherscan verification",
                    action = "store_true", dest='log_flag')
    ap.add_argument("-dest-log", help ="Log output path", action = "store", dest='log_stored_final')
    ap.add_argument("-o", help="ASM output path", dest='output_path', action='store')
    ap.add_argument("-csv", help="CSV file path", dest='csv_path', action='store')
    ap.add_argument("-storage", "--storage", help="Split using SSTORE, MSTORE and MSTORE8", action="store_true")
    # ap.add_argument("-last-constants", "--last-constants", help="It removes the last instructions of a block when they generate a constant value", dest="last_constants", action = "store_true")
    # ap.add_argument("-mem40", "--mem40", help="It assumes that pos 64 in memory is not dependant with variables", action = "store_true")
    ap.add_argument("-size","--size",help="It enables size cost model. The simplification rules are applied only if they reduce the size",action="store_true")
    ap.add_argument("-partition","--partition",help="It enables the partition in blocks of 24 instructions",action="store_true")
    # ap.add_argument("-pop","--pop",help="It considers the necessary pops as uninterpreted functions",action="store_true")
    # ap.add_argument("-push","--push",help="It considers the push instructions as uninterpreted functions",action="store_true")
    # ap.add_argument("-terminal","--terminal",help="It takes into account if the last instruction is a revert or a return",action="store_true")
    ap.add_argument("-backend","--backend",help="Disables backend generation, so that only intermediate files are generated", action="store_false")
    ap.add_argument("-intermediate", "--intermediate", help="Keeps temporary intermediate files. These files contain the sfs representation, smt encoding...", action="store_true")

    args = ap.parse_args()


    # If storage or partition flag are activated, the blocks are split using store instructions
    if args.storage or args.partition:
        constants.append_store_instructions_to_split()

    output_file, csv_file, log_file = final_file_names(args)

    x = dtimer()
    if args.log_path is not None:
        with open(args.log_path) as path:
            log_dict = json.load(path)
            optimize_asm_from_log(args.input_path, log_dict, output_file,  args.storage, False,
                                  args.size,args.partition)
            if not args.intermediate:
                shutil.rmtree(paths.gasol_path, ignore_errors=True)
            exit(0)

    if not args.block:
        optimize_asm_in_asm_format(args.input_path, output_file, csv_file, log_file, args.tout, args.log_flag, args.storage,
                                   False,args.size,args.partition)

    else:
        optimize_isolated_asm_block(args.input_path, output_file, csv_file, args.tout, args.storage, False,
                                    args.size,args.partition)


    y = dtimer()

    print("")
    print("Total time: "+ str(round(y-x, 2)) + " s")

    if args.intermediate or not args.backend:
        print("")
        print("Intermediate files stored at " + paths.gasol_path)
    else:
        shutil.rmtree(paths.gasol_path, ignore_errors=True)


    if args.backend:
        print("")
        print("Optimized code stored in " + output_file)
        print("Optimality results stored in " + csv_file)
        print("")
        print("Estimated initial gas: "+str(previous_gas))
        print("Estimated gas optimized: " + str(new_gas))
        print("")
        print("Estimated initial size in bytes: " + str(previous_size))
        print("Estimated size optimized in bytes: " + str(new_size))

    else:
        print("")
        print("Estimated initial gas: "+str(previous_gas))
        print("")
        print("Estimated initial size in bytes: " + str(previous_size))
