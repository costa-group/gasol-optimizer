#!/usr/bin/python3
import argparse
import json
import os
import pathlib
import shutil
import sys
from typing import Tuple, Optional, List
from copy import deepcopy
from timeit import default_timer as dtimer
from argparse import ArgumentParser, Namespace

import pandas as pd

import global_params.constants as constants
import global_params.paths as paths
import sfs_generator.ir_block as ir_block
from sfs_generator.gasol_optimization import get_sfs_dict
from sfs_generator.parser_asm import (parse_asm,
                                      generate_block_from_plain_instructions,
                                      parse_blocks_from_plain_instructions)
from sfs_generator.utils import (compute_stack_size, get_ins_size_seq,
                                 is_constant_instruction, isYulInstruction,
                                 isYulKeyword)
from smt_encoding.gasol_encoder import (execute_syrup_backend,
                                        execute_syrup_backend_combined,
                                        generate_theta_dict_from_sequence)
from solution_generation.disasm_generation import (
    generate_sub_block_asm_representation_from_log)
from solution_generation.solver_output_generation import obtain_solver_output
from verification.sfs_verify import verify_block_from_list_of_sfs
from verification.solver_solution_verify import (
    check_solver_output_is_correct)
from solution_generation.optimize_from_sub_blocks import rebuild_optimized_asm_block
from sfs_generator.asm_block import AsmBlock, AsmBytecode
from smt_encoding.block_optimizer import BlockOptimizer, OptimizeOutcome

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


def clean_dir():
    ext = ["rbr", "csv", "sol", "bl", "disasm", "json"]
    pathlib.Path("unsat.txt").unlink(missing_ok=True)
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


def compute_original_sfs_with_simplifications(block: AsmBlock, parsed_args: Namespace):


    stack_size = block.source_stack
    block_name = block.block_name
    block_id = block.block_id
    instructions = block.to_plain()

    instructions_to_optimize = block.instructions_to_optimize_plain()

    if ("REVERT" in instructions or "RETURN" in instructions) and parsed_args.terminal:
        revert_flag = True
    else:
        revert_flag = False
        
    # if last_const:
    #     new_stack_size, rest_instructions = remove_last_constant_instructions(instructions_to_optimize)
    # else:
    #     new_stack_size = stack_size
    
    block_data = {"instructions": instructions_to_optimize, "input": stack_size}

    fname = parsed_args.input_path.split("/")[-1].split(".")[0]
    
    exit_code, subblocks_list = \
        ir_block.evm2rbr_compiler(file_name = fname, block=block_data, block_name=block_name, block_id=block_id,
                                  simplification=not parsed_args.no_simp, storage=parsed_args.storage, size = parsed_args.size, part = parsed_args.partition,
                                  pop= not parsed_args.pop_basic, push =not parsed_args.push_basic, revert=revert_flag, debug_info = parsed_args.debug_flag)

    sfs_dict = get_sfs_dict()

    return sfs_dict, subblocks_list


# Given the sequence of bytecodes, the initial stack size, the contract name and the
# block id, returns the output given by the solver, the name given to that block and current gas associated
# to that sequence.
def optimize_block(sfs_dict, timeout, parsed_args: Namespace) -> List[Tuple[AsmBlock, OptimizeOutcome, float,
                                                                            List[AsmBytecode], int, int]]:

    block_solutions = []
    # SFS dict of syrup contract contains all sub-blocks derived from a block after splitting
    for block_name in sfs_dict:
        sfs_block = sfs_dict[block_name]
        initial_solver_bound = sfs_block['init_progr_len']
        original_instr = sfs_block['original_instrs']
        original_block = generate_block_from_plain_instructions(original_instr, block_name)

        # To match previous results, multiply timeout by number of storage instructions
        # TODO devise better heuristics to deal with timeouts
        tout = parsed_args.tout * (1+len([True for instr in sfs_block['user_instrs'] if instr["storage"]]))

        optimizer = BlockOptimizer(block_name, sfs_block, parsed_args, tout)
        print(f"Optimizing {block_name}... Timeout:{str(tout)}")

        if parsed_args.backend:
            if initial_solver_bound > 40:
                optimization_outcome, optimized_asm = OptimizeOutcome.no_model, []
                solver_time = 0
            else:
                optimization_outcome, solver_time, optimized_asm = optimizer.optimize_block()
            block_solutions.append((original_block, optimization_outcome, solver_time,
                                    optimized_asm, tout, initial_solver_bound))
        else:
            optimizer.generate_intermediate_files()

    return block_solutions


# Given the log file loaded in json format, current block and the contract name, generates three dicts: one that
# contains the sfs from each block, the second one contains the sequence of instructions and
# the third one is a set that contains all block ids.
def generate_sfs_dicts_from_log(block, json_log, parsed_args: Namespace):

    contracts_dict, sub_block_list = compute_original_sfs_with_simplifications(block, parsed_args)
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


def optimize_asm_from_log(file_name, json_log, output_file, parsed_args: Namespace):
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
                generate_sfs_dicts_from_log(block, json_log, parsed_args)

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
                    generate_sfs_dicts_from_log(block, json_log, parsed_args)

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
                f.write(json.dumps(new_asm.to_json()))

            print("")
            print("Optimized code stored at " + output_file)
        else:
            print("Log file does not contain a valid solution")


def optimize_isolated_asm_block(block_name,output_file, csv_file, parsed_args: Namespace, timeout=10):
    global statistics_rows

    with open(block_name,"r") as f:        
        instructions = f.read()

    blocks = parse_blocks_from_plain_instructions(instructions)
    asm_blocks = []

    for old_block in blocks:
        asm_block, _ = optimize_asm_block_asm_format(old_block, timeout, parsed_args)
        
        if not compare_asm_block_asm_format(old_block, asm_block, parsed_args):
            print("Comparison failed, so initial block is kept")
            print(old_block.to_plain())
            print(asm_block.to_plain())
            print("")
            asm_block = old_block

        update_gas_count(old_block, asm_block)
        update_size_count(old_block, asm_block)
        asm_blocks.append(asm_block)

    if parsed_args.backend:
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


def generate_statistics_info(original_block: AsmBlock, outcome: Optional[OptimizeOutcome], solver_time: float,
                             optimized_asm: List[AsmBytecode], initial_bound: Optional[int], tout: Optional[int]):
    global statistics_row

    block_name = original_block.block_name
    original_instr = ' '.join(original_block.instructions_to_optimize_plain())

    statistics_row = {"block_id": block_name, "previous_solution": original_instr}

    # The outcome of the solver is unsat
    if outcome == OptimizeOutcome.unsat:
        statistics_row.update({"model_found": False, "shown_optimal": False, "solver_time_in_sec": round(solver_time, 3),
                               "saved_size": 0, "saved_gas": 0, "initial_n_instrs": initial_bound, "timeout": tout,
                               'outcome': 'unsat'})

    # The solver has returned no model
    elif outcome == OptimizeOutcome.no_model:
        statistics_row.update(
            {"model_found": False, "shown_optimal": False, "solver_time_in_sec": round(solver_time, 3),
             "saved_size": 0, "saved_gas": 0, "initial_n_instrs": initial_bound, "timeout": tout, 'outcome': 'no_model'})

    # The solver has returned a valid model
    else:
        shown_optimal = outcome == OptimizeOutcome.optimal
        optimized_length = sum([instr.bytes_required for instr in optimized_asm])
        optimized_gas = sum([instr.gas_spent for instr in optimized_asm])
        initial_length = original_block.bytes_required
        initial_gas = original_block.gas_spent

        statistics_row.update({"solver_time_in_sec": round(solver_time, 3), "saved_size": initial_length - optimized_length,
                               "saved_gas": initial_gas - optimized_gas, "model_found": True, "shown_optimal": shown_optimal,
                               "solution_found": ' '.join([instr.to_plain() for instr in optimized_asm]),
                               "initial_n_instrs": initial_bound, "optimized_n_instrs": len(optimized_asm),
                               "timeout": tout, 'outcome': 'model'})

    statistics_rows.append(statistics_row)


def block_has_been_optimized(original_block: AsmBlock, optimized_asm: List[AsmBytecode], size_criterion: bool) -> bool:
    saved_size = original_block.bytes_required - sum([instr.bytes_required for instr in optimized_asm])
    saved_gas = original_block.gas_spent - sum([instr.gas_spent for instr in optimized_asm])

    return (not size_criterion and (saved_gas > 0 or (saved_gas == 0 and saved_size > 0))) or \
           (size_criterion and (saved_size > 0 or (saved_size == 0 and saved_gas > 0)))


# Given an asm_block and its contract name, returns the asm block after the optimization
def optimize_asm_block_asm_format(block: AsmBlock, timeout: int, parsed_args: Namespace):
    new_block = deepcopy(block)

    # Optimized blocks. When a block is not optimized, None is pushed to the list.
    optimized_blocks = {}

    log_dicts = {}

    instructions = block.instructions_to_optimize_plain()

    # No instructions to optimize
    if instructions == []:
        return new_block, {}

    contracts_dict, sub_block_list = compute_original_sfs_with_simplifications(block, parsed_args)

    sfs_dict = contracts_dict["syrup_contract"]

    if not parsed_args.backend:
        optimize_block(sfs_dict, timeout, parsed_args)
        return new_block, {}

    for sub_block, optimization_outcome, solver_time, optimized_asm, tout, initial_solver_bound in optimize_block(sfs_dict, timeout, parsed_args):

        generate_statistics_info(sub_block, optimization_outcome, solver_time, optimized_asm, initial_solver_bound, tout)

        # Only check if the new block is considered if the solver has generated a new one
        if optimization_outcome == OptimizeOutcome.non_optimal or optimization_outcome == OptimizeOutcome.optimal:
            sub_block_name = sub_block.block_name
            if block_has_been_optimized(sub_block, optimized_asm, parsed_args.size):
                optimized_blocks[sub_block_name] = optimized_asm
                # log_dicts[sub_block_name] = generate_solution_dict(solver_output)
            else:
                optimized_blocks[sub_block_name] = None

    new_block = rebuild_optimized_asm_block(block, sub_block_list, optimized_blocks)

    return new_block, log_dicts


def compare_asm_block_asm_format(old_block: AsmBlock, new_block: AsmBlock, parsed_args: Namespace) -> bool:

    new_sfs_information, _ = compute_original_sfs_with_simplifications(new_block, parsed_args)

    new_sfs_dict = new_sfs_information["syrup_contract"]

    old_sfs_information, _ = compute_original_sfs_with_simplifications(old_block, parsed_args)

    old_sfs_dict = old_sfs_information["syrup_contract"]

    final_comparison = verify_block_from_list_of_sfs(old_sfs_dict, new_sfs_dict)

    # We also must check intermediate instructions match i.e those that are not sub blocks
    initial_instructions_old = old_block.instructions_initial_bytecode()
    initial_instructions_new = new_block.instructions_initial_bytecode()

    final_instructions_old = old_block.instructions_final_bytecode()
    final_instructions_new = new_block.instructions_final_bytecode()

    return final_comparison and (initial_instructions_new == initial_instructions_old) and \
           final_instructions_new == final_instructions_old


def optimize_asm_in_asm_format(file_name, output_file, csv_file, log_file, parsed_args: Namespace, timeout=10):
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
            optimized_block, log_element = optimize_asm_block_asm_format(old_block, timeout, parsed_args)

            if not compare_asm_block_asm_format(old_block, optimized_block, parsed_args):
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
                optimized_block, log_element = optimize_asm_block_asm_format(old_block, timeout, parsed_args)
                
                if not compare_asm_block_asm_format(old_block, optimized_block, parsed_args):
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

    if parsed_args.log:
        with open(log_file, "w") as log_f:
            json.dump(log_dicts, log_f)

    if parsed_args.backend:

        with open(output_file, 'w') as f:
            f.write(json.dumps(new_asm.to_json()))

        df = pd.DataFrame(statistics_rows)
        df.to_csv(csv_file)


def final_file_names(parsed_args: argparse.Namespace) -> Tuple[str, str, str]:
    input_file_name = parsed_args.input_path.split("/")[-1].split(".")[0]

    if parsed_args.output_path is None:
        if parsed_args.block:
            output_file = input_file_name + "_optimized.txt"
        elif parsed_args.log_path is not None:
            output_file = input_file_name + "_optimized_from_log.json_solc"
        else:
            output_file = input_file_name + "_optimized.json_solc"
    else:
        output_file = parsed_args.output_path

    if parsed_args.csv_path is None:
        csv_file = input_file_name + "_statistics.csv"
    else:
        csv_file = parsed_args.csv_path

    if parsed_args.log_stored_final is None:
        log_file = input_file_name + ".log"
    else:
        log_file = parsed_args.log_stored_final

    return output_file, csv_file, log_file


def parse_encoding_args() -> Namespace:
    # Unused options
    # ap.add_argument("-last-constants", "--last-constants", help="It removes the last instructions of a block when they generate a constant value", dest="last_constants", action = "store_true")
    # ap.add_argument("-mem40", "--mem40", help="It assumes that pos 64 in memory is not dependant with variables", action = "store_true")

    ap = ArgumentParser(description='GASOL, the EVM super-optimizer')

    input = ap.add_argument_group('Input options')

    input.add_argument('input_path', help='Path to input file that contains the code to optimize. Can be either asm or'
                                          'plain instructions, with the bl flag enabled')
    input.add_argument("-bl", "--block", help="Enable analysis of a single asm block", action = "store_true")

    output = ap.add_argument_group('Output options')

    output.add_argument("-o", help="Path for storing the optimized code", dest='output_path', action='store')
    output.add_argument("-csv", help="CSV file path", dest='csv_path', action='store')
    output.add_argument("-backend","--backend", action="store_false",
                        help="Disables backend generation, so that only intermediate files are generated")
    output.add_argument("-intermediate", "--intermediate", action="store_true",
                        help="Keeps temporary intermediate files. "
                             "These files contain the sfs representation, smt encoding...")
    output.add_argument("-d", "--debug", help="It prints debugging information", dest='debug_flag', action="store_true")

    log_generation = ap.add_argument_group('Log generation options', 'Options for managing the log generation')

    log_generation.add_argument("-log", "--generate-log", help ="Enable log file for Etherscan verification",
                                action = "store_true", dest='log')
    log_generation.add_argument("-dest-log", help ="Log output path", action = "store", dest='log_stored_final')
    log_generation.add_argument("-optimize-from-log", dest='log_path', action='store', metavar="log_file",
                                help="Generates the same optimized bytecode than the one associated to the log file")

    basic = ap.add_argument_group('Max-SMT solver general options',
                                  'Basic options for solving the corresponding Max-SMT problem')

    basic.add_argument("-solver", "--solver", help="Choose the solver", choices=["z3", "barcelogic", "oms"],
                       default="z3")
    basic.add_argument("-tout", metavar='timeout', action='store', type=int,
                       help="Timeout in seconds. By default, set to 10s per block.", default=10)

    blocks = ap.add_argument_group('Split block options', 'Options for deciding how to split blocks when optimizing')

    blocks.add_argument("-storage", "--storage", help="Split using SSTORE, MSTORE and MSTORE8", action="store_true")
    blocks.add_argument("-partition","--partition",help="It enables the partition in blocks of 24 instructions",action="store_true")

    hard = ap.add_argument_group('Hard constraints', 'Options for modifying the hard constraint generation')

    hard.add_argument("-memory-encoding", help="Choose the memory encoding model", choices=["l_vars", "direct"],
                      default="l_vars", dest='memory_encoding')
    hard.add_argument('-no-simplification',"--no-simplification", action='store_true', dest='no_simp',
                      help='Disables the application of simplification rules')
    hard.add_argument('-push-uninterpreted', action='store_false', dest='push_basic',
                      help='Encodes push instruction as uninterpreted functions')
    hard.add_argument('-pop-uninterpreted', action='store_false', dest='pop_basic',
                      help='Encodes pop instruction as uninterpreted functions')
    hard.add_argument('-order-bounds', action='store_true', dest='order_bounds',
                      help='Consider bounds on the position instructions can appear in the encoding')
    hard.add_argument('-empty', action='store_true', dest='empty',
                      help='Consider "empty" value as part of the encoding to reflect some stack position is empty,'
                           'instead of using a boolean term')
    hard.add_argument('-term-encoding', action='store', dest='encode_terms',
                      choices=['int', 'stack_vars', 'uninterpreted_uf', 'uninterpreted_int'],
                      help='Decides how terms are encoded in the SMT encoding: directly as numbers, using stack'
                           'variables or introducing uninterpreted functions',default = 'uninterpreted_uf')
    hard.add_argument('-terminal', action='store_true', dest='terminal',
                      help='(UNSUPPORTED) Encoding for terminal blocks that end with REVERT or RETURN. '
                           'Instead of considering the full stack order, just considers the two top elements')
    hard.add_argument('-ac', action='store_true', dest='ac_solver',
                      help='(UNSUPPORTED) Commutativity in operations is considered as an extension inside the solver. '
                           'Can only be combined with Z3')

    soft = ap.add_argument_group('Soft constraints', 'Options for modifying the soft constraint generation')
    soft.add_argument("-size", "--size", action="store_true",
                      help="It enables size cost model for optimization and disables rules that increase the size"
                           "The simplification rules are applied only if they reduce the size")

    soft.add_argument("-direct-inequalities", dest='direct', action='store_true',
                      help="Soft constraints with inequalities instead of equalities and without grouping")

    additional = ap.add_argument_group('Additional constraints',
                                       'Constraints that can help to speed up the optimization process, but are not '
                                       'necessary')
    additional.add_argument('-at-most', action='store_true', dest='at_most',
                            help='add a constraint for each uninterpreted function so that they are used at most once')
    additional.add_argument('-pushed-once', action='store_true', dest='pushed_once',
                            help='add a constraint to indicate that each pushed value is pushed at least once')
    additional.add_argument("-no-output-before-pop", action='store_true', dest='no_output_before_pop',
                            help='Add a constraint representing the fact that the previous instruction'
                                 'of a pop can only be a instruction that does not produce an element')
    additional.add_argument('-order-conflicts', action='store_true', dest='order_conflicts',
                            help='Consider the order among the uninterpreted opcodes in the encoding')

    parsed_args = ap.parse_args()

    # Additional check: if ufs are used, push instructions must be represented as uninterpreted too
    if parsed_args.encode_terms == "uninterpreted_uf":
        parsed_args.push_basic = False

    return parsed_args

if __name__ == '__main__':
    global previous_gas
    global new_gas
    global previous_size
    global new_size

    init()
    clean_dir()
    parsed_args = parse_encoding_args()

    # If storage or partition flag are activated, the blocks are split using store instructions
    if parsed_args.storage or parsed_args.partition:
        constants.append_store_instructions_to_split()

    output_file, csv_file, log_file = final_file_names(parsed_args)

    x = dtimer()
    if parsed_args.log_path is not None:
        with open(parsed_args.log_path) as path:
            log_dict = json.load(path)
            optimize_asm_from_log(parsed_args.input_path, log_dict, output_file,  parsed_args)
            if not parsed_args.intermediate:
                shutil.rmtree(paths.gasol_path, ignore_errors=True)
            exit(0)

    if not parsed_args.block:
        optimize_asm_in_asm_format(parsed_args.input_path, output_file, csv_file, log_file, parsed_args, parsed_args.tout)

    else:
        optimize_isolated_asm_block(parsed_args.input_path, output_file, csv_file, parsed_args, parsed_args.tout)


    y = dtimer()

    print("")
    print("Total time: "+ str(round(y-x, 2)) + " s")

    if parsed_args.intermediate or not parsed_args.backend:
        print("")
        print("Intermediate files stored at " + paths.gasol_path)
    else:
        shutil.rmtree(paths.gasol_path, ignore_errors=True)


    if parsed_args.backend:
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
