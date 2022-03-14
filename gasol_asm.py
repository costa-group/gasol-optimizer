#!/usr/bin/python3
import argparse
import collections
import json
import os
import shutil
import sys
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


def compute_original_sfs_with_simplifications(instructions, stack_size, cname, block_id, is_initial_block,storage, last_const, size_abs, partition, pop_flag, push_flag,revert_return):

    block_ins = list(filter(lambda x: x not in ["JUMP","JUMPI","JUMPDEST","tag", "STOP","RETURN","INVALID","REVERT"], instructions))

    if ("REVERT" in instructions or "RETURN" in instructions) and revert_return:
        revert_flag = True
    else:
        revert_flag = False
        
    if last_const:
        new_stack_size , rest_instructions = remove_last_constant_instructions(block_ins)
        
    else:
        new_stack_size = stack_size
    
    block_data = {"instructions": block_ins, "input": new_stack_size}

    if is_initial_block:
        prefix = "initial_"
    else:
        prefix = ""

    fname = args.input_path.split("/")[-1].split(".")[0]
    exit_code, subblocks_list = ir_block.evm2rbr_compiler(file_name = fname, contract_name=cname, block=block_data, block_id=block_id,
                                                                        preffix=prefix, simplification=True, storage=storage, size = size_abs, part = partition,pop = pop_flag, push = push_flag, revert = revert_flag)

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
        original_instrs = sfs_block['original_instrs']
        current_size = get_ins_size_seq(original_instrs)
        user_instr = sfs_block['user_instrs']
        initial_program_length = sfs_block['init_progr_len']

        args_i = argparse.Namespace()
        args_i.solver = "oms"
        args_i.instruction_order = True
        args_i.bytecode_size_soft_constraints = size

        if args.backend:
            execute_syrup_backend(args_i, sfs_block, block_name=block_name, timeout=timeout)

            if initial_program_length > 40:
                solver_output = "unsat"
                solver_time = 0
            # At this point, solution is a string that contains the output directly
            # from the solver
            else:
                solver_output, solver_time = obtain_solver_output(block_name, "oms", timeout)
            block_solutions.append((solver_output, block_name, current_cost, current_size, user_instr, solver_time))

    return block_solutions


# Given the log file loaded in json format, current block and the contract name, generates three dicts: one that
# contains the sfs from each block, the second one contains the sequence of instructions and
# the third one is a set that contains all block ids.
def generate_sfs_dicts_from_log(block, contract_name, json_log,storage, last_const):
    bytecodes = block.instructions
    stack_size = block.source_stack
    block_id = block.block_id
    is_init_block = block.is_init_block

    instructions = preprocess_instructions(bytecodes)

    sfs_dict = compute_original_sfs_with_simplifications(instructions, stack_size,
                                                         contract_name, block_id, is_init_block,storage, last_const)['syrup_contract']

    # Contains sfs blocks considered to check the SMT problem. Therefore, a block is added from
    # sfs_original iff solver could not find an optimized solution, and from sfs_dict otherwise.
    sfs_final = {}

    # Dict that contains all instr sequences
    instr_sequence_dict = {}

    # Set that contains all ids
    ids = set()

    # We need to inspect all sub-blocks in the sfs dict.
    for block_id in sfs_dict:

        log_json_id = contract_name + "_" + block_id

        ids.add(log_json_id)

        # If the id is not at json log, this means it has not been optimized
        if log_json_id not in json_log:
            continue

        instr_sequence = json_log[log_json_id]

        sfs_block = sfs_dict[block_id]


        sfs_final[log_json_id] = sfs_block
        instr_sequence_dict[log_json_id] = instr_sequence

    return sfs_final, instr_sequence_dict, ids


# Verify information derived from log file is correct
def check_log_file_is_correct(sfs_dict, instr_sequence_dict):
    execute_syrup_backend_combined(sfs_dict, instr_sequence_dict, "verify", "oms")

    solver_output = obtain_solver_output("verify", "oms", 0)

    return check_solver_output_is_correct(solver_output)



# Given a dict with the sfs from each block and another dict that contains whether previous block was optimized or not,
# generates the corresponding solution. All checks are assumed to have been done previously
def optimize_asm_block_from_log(block, sfs_dict, instr_sequence_dict):
    new_block = deepcopy(block)
    optimized_blocks = {}
    is_init_block = block.is_init_block
    block_id = block.block_id

    if is_init_block:
        block_name = "initial_block" + str(block_id)
    else:
        block_name = "block" + str(block_id)

    for block_id in sfs_dict:

        # We obtain the subindex from the block (if any)
        block_sub_index_str = block_id.split(block_name)[-1]

        # No subindex. By default, assigned to 0
        if block_sub_index_str == '':
            block_sub_index = 0
        else:
            # we must ignore the point . (first chatr in block_sub_index_str)
            block_sub_index = int(block_sub_index_str[1:])

        sfs_block = sfs_dict[block_id]

        user_instr = sfs_block['user_instrs']

        bs = sfs_block['max_sk_sz']
        instr_sequence = instr_sequence_dict[block_id]
        _, instruction_theta_dict, opcodes_theta_dict, gas_theta_dict, values_dict = \
            generate_theta_dict_from_sequence(bs, user_instr)

        asm_sub_block = generate_sub_block_asm_representation_from_log(instr_sequence, opcodes_theta_dict,
                                                                       instruction_theta_dict, gas_theta_dict, values_dict)
        optimized_blocks[block_sub_index] = asm_sub_block

    asm_sub_blocks = list(filter(lambda x: isinstance(x, list), block.split_in_sub_blocks()))
    optimized_blocks_list = [None if i not in optimized_blocks else optimized_blocks[i] for i in range(len(asm_sub_blocks))]

    new_block.set_instructions_from_sub_blocks(optimized_blocks_list)

    return new_block


def optimize_asm_from_log(file_name, json_log, output_file):
    asm = parse_asm(file_name)

    # Blocks from all contracts are checked together. Thus, we first will obtain the needed
    # information from each block
    sfs_dict, instr_sequence_dict, file_ids = {}, {}, set()
    contracts = []

    file_name_str = file_name.split("/")[-1].split(".")[0]

    # If not output file provided, then we create a name by default.
    if output_file is None:
        output_file = file_name_str + "_optimized_from_log.json_solc"

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
            sfs_final_block, instr_sequence_dict_block, block_ids = generate_sfs_dicts_from_log(block, contract_name, json_log)
            new_block = optimize_asm_block_from_log(block, sfs_final_block, instr_sequence_dict_block)
            sfs_dict.update(sfs_final_block)
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
                sfs_final_block, instr_sequence_dict_block, block_ids = generate_sfs_dicts_from_log(block, contract_name, json_log)
                new_block = optimize_asm_block_from_log(block, sfs_final_block, instr_sequence_dict_block)
                sfs_dict.update(sfs_final_block)
                instr_sequence_dict.update(instr_sequence_dict_block)
                file_ids.update(block_ids)
                run_code_blocks.append(new_block)

            new_contract.set_run_code(identifier, run_code_blocks)

        contracts.append(new_contract)

    # We check ids in json log file matches the ones generated from the source file
    if not set(json_log.keys()).issubset(file_ids):
        print("Log file does not match source file")
    else:
        not_empty = {k : v for k,v in sfs_dict.items() if v != []}
        correct = check_log_file_is_correct(not_empty, instr_sequence_dict)
        if correct:
            print("Solution generated from log file has been verified correctly")
            new_asm = deepcopy(asm)
            new_asm.set_contracts(contracts)

            with open(output_file, 'w') as f:
                f.write(json.dumps(rebuild_asm(new_asm)))
        else:
            print("Log file does not contain a valid solution")


def optimize_isolated_asm_block(block_name,output_file, csv_file, timeout=10, storage= False, last_const = False,
                                size_abs = False, partition = False, pop = False, push = False, revert = False):
    global statistics_rows

    file_name_str = block_name.split("/")[-1].split(".")[0]

    # If not output file provided, then we create a name by default.
    if output_file is None:
        output_file = file_name_str + "_optimized.txt"

    if csv_file is None:
        csv_file = file_name_str + "_statistics.csv"

    with open(block_name,"r") as f:        
        instructions = f.read()

    blocks = parse_blocks_from_plain_instructions(instructions)
    asm_blocks = []

    for old_block in blocks:
        asm_block, _ = optimize_asm_block_asm_format(old_block, file_name_str, timeout, storage, last_const, size_abs, partition, pop, push, revert)
        asm_blocks.append(asm_block)

        update_gas_count(old_block, asm_block)
        update_size_count(old_block, asm_block)

        if not compare_asm_block_asm_format(old_block, asm_block):
            print("Optimized block " + str(block.block_id) + " from data id " + str(identifier)
                  + " at contract " + contract_name + " has not been verified correctly")
            print(block.instructions)
            print(asm_block.instructions)
            verifier_error = True
            raise Exception

            
        
    if args.backend:
        df = pd.DataFrame(statistics_rows)
        df.to_csv(csv_file)
        print("")
        print("Optimized code stored at " + output_file)
        with open(output_file, 'w') as f:
            f.write(parse_asm_representation_from_blocks(asm_blocks))


def update_gas_count(old_block, new_block):
    global previous_gas
    global new_gas

    old_instructions = preprocess_instructions(old_block.instructions)
    new_instructions = preprocess_instructions(new_block.instructions)

    for instr in old_instructions:
        if not isYulInstruction(instr):
            previous_gas += op.get_ins_cost(instr)

    for instr in new_instructions:
        if not isYulInstruction(instr):
            new_gas += op.get_ins_cost(instr)


def update_size_count(old_block, new_block):
    global previous_size
    global new_size

    previous_size += sum([bytes_required_asm(asm_bytecode) for asm_bytecode in old_block.instructions])
    new_size += sum([bytes_required_asm(asm_bytecode) for asm_bytecode in new_block.instructions])



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
def optimize_asm_block_asm_format(block, contract_name, timeout, storage, last_const, size_abs, partition,pop_flag, push_flag, revert_return):
    global statistics_rows
    global total_time

    bytecodes = block.instructions
    stack_size = block.source_stack
    block_id = block.block_id
    is_init_block = block.is_init_block
    new_block = deepcopy(block)

    # Optimized blocks. When a block is not optimized, None is pushed to the list.
    optimized_blocks = {}

    log_dicts = {}

    instructions = preprocess_instructions(bytecodes)

    # x = dtimer()
    
    contracts_dict, sub_block_list = compute_original_sfs_with_simplifications(instructions,stack_size,contract_name,
                                                                               block_id, is_init_block,storage,
                                                                               last_const,size_abs, partition,pop_flag, push_flag, revert_return)

    # y = dtimer()
    # print("*************************************************************")
    # print("SFS generation time: "+str(y-x)+"s")
    # print("*************************************************************")

    if not args.backend:
        return new_block, {}
    
    sfs_dict = contracts_dict["syrup_contract"]
    for solver_output, block_name, current_cost, current_length, user_instr, solver_time \
            in optimize_block(sfs_dict, timeout, size_abs):

        # We weren't able to find a solution using the solver, so we just update
        if not check_solver_output_is_correct(solver_output):
            optimized_blocks[block_name] = None
            statistics_row = {"block_id": block_name, "no_model_found": True, "shown_optimal": False,
                              "solver_time_in_sec": round(solver_time, 3)}
            statistics_rows.append(statistics_row)
            total_time += solver_time
            continue

        bs = sfs_dict[block_name]['max_sk_sz']

        _, instruction_theta_dict, opcodes_theta_dict, gas_theta_dict, values_dict = generate_theta_dict_from_sequence(bs, user_instr)

        
        instruction_output, _, pushed_output, optimized_cost = \
            generate_info_from_solution(solver_output, opcodes_theta_dict, instruction_theta_dict,
                                        gas_theta_dict, values_dict)

        new_sub_block = generate_sub_block_asm_representation_from_output(solver_output, opcodes_theta_dict,
                                                                          instruction_theta_dict,
                                                                          gas_theta_dict, values_dict)
        _, shown_optimal = analyze_file(solver_output, "oms")
        optimized_length = sum([bytes_required_asm(instr) for instr in new_sub_block])
        statistics_row = {"block_id": block_name, "solver_time_in_sec": round(solver_time, 3), "saved_size": current_length - optimized_length,
                          "saved_gas": current_cost - optimized_cost, "no_model_found": False, "shown_optimal": shown_optimal}
        statistics_rows.append(statistics_row)
        total_time += solver_time

        if (not size_abs and current_cost > optimized_cost) or (size_abs and current_length > optimized_length) :
            optimized_blocks[block_name] = new_sub_block
            log_dicts[contract_name + '_' + block_name] = generate_solution_dict(solver_output)
        else:
            optimized_blocks[block_name] = None

    if is_init_block:
        block_name = "initial_block" + str(block_id)
    else:
        block_name = "block" + str(block_id)

    if len(sub_block_list) > 1 and len(sub_block_list[-1]) == 1:
        sub_block_list = sub_block_list[0:-1]

    if partition:
        asm_sub_blocks = list(filter(lambda x: isinstance(x, list), block.split_in_sub_blocks_partition(sub_block_list)))
    else:
        asm_sub_blocks = list(filter(lambda x: isinstance(x, list), block.split_in_sub_blocks()))

    # return block, log_dicts

    # At this point, we must be wary: some blocks may have been simplified totally and are not contained in the
    # optimized blocks dict. Thus, we need to identify them and assign them to []
    # Three cases: zero sub-block present in the contract, one or more than one

    # Case zero: nothing has been optimized
    if len(asm_sub_blocks) == 0:
        return deepcopy(block), {}
    # Case one: block may have been skipped completely
    if len(asm_sub_blocks) == 1:
        if not sfs_dict:
            optimized_blocks[block_name] = []
            log_dicts[contract_name + '_' + block_name] = []

        optimized_blocks_list = list(optimized_blocks.values())

    # # Case more than one sub blocks: several intermediate sub blocks may have been skipped.
    # # They can be identified from those sub blocks numbers that are not present in the sfs dict
    else:

        # For each sub-block in the initial block, we check whether is matches the corresponding sfs dict. If not,
        # it means a block was reduced directly and hence, we need to record it in the list of sub blocks

        optimized_blocks_list = []
        for current_idx in range(len(sub_block_list)):
            current_block_name = block_name + "." + str(current_idx)

            # If the corresponding block name does not belong to the list of optimized blocks, it means it was
            # simplified completely. Therefore, it is set to empty []
            optimized_blocks_list.append(optimized_blocks.get(current_block_name, []))

    #     # We sort by block id and obtain the associated values in order
    #     optimized_blocks_list_with_intra_block_consideration = \
    #         filter_optimized_blocks_by_intra_block_optimization(asm_sub_blocks, optimized_blocks_list)

    #     # If a sub block was optimized but finally we have to skip that optimization, we have to remove the corresponding
    #     # sub block information from the log dict. These sub blocks correspond to those that appeared at the log dict
    #     # but its corresponding block optimized in the list is not None
    #     log_dicts = {k : v for k,v in log_dicts.items() if optimized_blocks_list_with_intra_block_consideration[int(k.split(".")[-1])] is not None}

    if partition:
        new_block.set_instructions_from_sub_blocks_partition(optimized_blocks_list, sub_block_list)
    else:
        new_block.set_instructions_from_sub_blocks(optimized_blocks_list)

    return new_block, log_dicts


def compare_asm_block_asm_format(old_block, new_block, contract_name="example",storage = False, last_const = False, size_abs = False, partition = False, pop = False, push = False, revert = False):

    old_instructions = preprocess_instructions(old_block.instructions)

    old_sfs_information, _ = compute_original_sfs_with_simplifications(old_instructions, old_block.source_stack,
                                                                       contract_name, old_block.block_id,
                                                                       old_block.is_init_block, storage, last_const, size_abs, partition, pop, push, revert)

    old_sfs_dict = old_sfs_information["syrup_contract"]

    new_instructions = preprocess_instructions(new_block.instructions)


    new_sfs_information, _ = compute_original_sfs_with_simplifications(new_instructions, new_block.source_stack,
                                                                       contract_name, new_block.block_id,
                                                                       new_block.is_init_block, storage, last_const, size_abs, partition, pop, push, revert)

    new_sfs_dict = new_sfs_information["syrup_contract"]

    final_comparison = verify_block_from_list_of_sfs(old_sfs_dict, new_sfs_dict)

    # We also must check intermediate instructions match i.e those that are not sub blocks
    intermediate_instructions_old = list(map(lambda x: None if isinstance(x, list) else x, old_block.split_in_sub_blocks()))

    intermediate_instructions_new = list(map(lambda x: None if isinstance(x, list) else x, new_block.split_in_sub_blocks()))

    return final_comparison and (intermediate_instructions_old == intermediate_instructions_new)


def optimize_asm_in_asm_format(file_name, output_file, csv_file, timeout=10, log=False, storage= False, last_const = False, size_abs = False, partition = False, pop = False, push = False, revert = False):
    global statistics_rows

    asm = parse_asm(file_name)
    log_dicts = {}
    contracts = []
    # verifier_error = False

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
            optimized_block, log_element = optimize_asm_block_asm_format(old_block, contract_name, timeout, storage, last_const,size_abs,partition, pop, push, revert)
            log_dicts.update(log_element)
            init_code_blocks.append(optimized_block)

            # Deployment size is not considered when measuring it
            update_gas_count(old_block, optimized_block)

            if not compare_asm_block_asm_format(block, optimized_block):
                print("Optimized block " + str(block.block_id) + " from init code at contract " + contract_name +
                      " has not been verified correctly")
                print(block.instructions)
                print(optimized_block.instructions)
                verifier_error = True

        new_contract.init_code = init_code_blocks

        print("\nAnalyzing Runtime Code of: " + contract_name)
        print("-----------------------------------------\n")
        for identifier in c.get_data_ids_with_code():
            blocks = c.get_run_code(identifier)

            run_code_blocks = []
            for old_block in blocks:
                optimized_block, log_element = optimize_asm_block_asm_format(old_block, contract_name, timeout, storage, last_const,size_abs,partition, pop, push, revert)
                log_dicts.update(log_element)
                run_code_blocks.append(optimized_block)

                update_gas_count(old_block, optimized_block)
                update_size_count(old_block, optimized_block)

                if not compare_asm_block_asm_format(block, optimized_block):
                    print("Optimized block " + str(block.block_id) + " from data id " + str(identifier)
                          + " at contract " + contract_name + " has not been verified correctly")
                    print(block.instructions)
                    print(optimized_block.instructions)
                    verifier_error = True

            new_contract.set_run_code(identifier, run_code_blocks)

        contracts.append(new_contract)

    # if not verifier_error:
    #     print("Optimized bytecode has been checked successfully")
    # else:
    #     print("The optimized bytecode could not be verified")

    new_asm = deepcopy(asm)
    new_asm.set_contracts(contracts)

    print("Previous number of instructions:", compute_number_of_instructions_in_asm_json_per_file(asm))
    print("New number of instructions:", compute_number_of_instructions_in_asm_json_per_file(new_asm))

    if log:
        input_file_name = args.input_path.split("/")[-1].split(".")[0]
        with open(paths.gasol_path + input_file_name + ".log" , "w") as log_f:
            json.dump(log_dicts, log_f)

    if args.backend:
        with open(output_file, 'w') as f:
            f.write(json.dumps(rebuild_asm(new_asm)))

        df = pd.DataFrame(statistics_rows)
        df.to_csv(csv_file)


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
    # ap.add_argument("-optimize-gasol-from-log-file", dest='log_path', action='store', metavar="log_file",
    #                     help="Generates the same optimized bytecode than the one associated to the log file")
    # ap.add_argument("-log", "--generate-log", help ="Generate log file for Etherscan verification",
    #                 action = "store_true", dest='log_flag')
    ap.add_argument("-o", help="ASM output path", dest='output_path', action='store')
    ap.add_argument("-csv", help="CSV file path", dest='csv_path', action='store')
    ap.add_argument("-storage", "--storage", help="Split using SSTORE, MSTORE and MSTORE8", action="store_true")
    ap.add_argument("-last-constants", "--last-constants", help="It removes the last instructions of a block when they generate a constant value", dest="last_constants", action = "store_true")
    ap.add_argument("-mem40", "--mem40", help="It assumes that pos 64 in memory is not dependant with variables", action = "store_true")
    ap.add_argument("-size","--size",help="It enables size cost model. The simplification rules are applied only if they improve the size",action="store_true")
    ap.add_argument("-partition","--partition",help="It enables the partition in blocks of 24 instructions",action="store_true")
    ap.add_argument("-pop","--pop",help="It considers the necessary pops as uninterpreted functions",action="store_true")
    ap.add_argument("-push","--push",help="It considers the push instructions as uninterpreted functions",action="store_true")
    ap.add_argument("-terminal","--terminal",help="It takes into account if the last instruction is a revert or a return",action="store_true")
    ap.add_argument("-backend","--backend",help="Enables backend",action="store_true")
    args = ap.parse_args()


    # If storage or partition flag are activated, the blocks are split using store instructions
    if args.storage or args.partition:
        constants.append_store_instructions_to_split()

    x = dtimer()
    # if args.log_path is not None:
    #     with open(args.log_path) as path:
    #         log_dict = json.load(path)
    #         optimize_asm_from_log(args.input_path, log_dict, args.output_path)

    input_file_name = args.input_path.split("/")[-1].split(".")[0]

    if args.output_path is None:
        output_file = input_file_name + "_optimized.json_solc"
    else:
        output_file = args.output_path

    if args.csv_path is None:
        csv_file = input_file_name + "_statistics.csv"
    else:
        csv_file = args.csv_path


    if not args.block:
        optimize_asm_in_asm_format(args.input_path, output_file, csv_file, args.tout, False, args.storage,args.last_constants,args.size,args.partition,args.pop,args.push, args.terminal)
    else:
        optimize_isolated_asm_block(args.input_path, output_file, csv_file, args.tout, args.storage,args.last_constants,args.size,args.partition,args.pop,args.push, args.terminal)


    y = dtimer()

    print("")
    print("Total time: "+str(y-x))
    print("")
    
    if args.backend:
        print("")
        print("Total time spent by the SMT solver in minutes: " + str(round(total_time / 60, 2)))
        print("")
        print("Previous gas executed: "+str(previous_gas))
        print("New gas executed: " + str(new_gas))
        print("")
        print("Previous size executed: " + str(previous_size))
        print("New size executed: " + str(new_size))
        print("")
        print("Json solc optimized stored at " + output_file)

    else:
        print("Previous gas executed: " + str(previous_gas))
        print("")
        print("Previous size executed: " + str(previous_size))

    print("")
    print("Intermediate files stored at " + paths.gasol_path)
