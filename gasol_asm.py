#!/usr/bin/python3

import argparse
import json
import os
import sys
import shutil

sys.path.append(os.path.dirname(os.path.realpath(__file__))+"/smt_encoding")
sys.path.append(os.path.dirname(os.path.realpath(__file__))+"/sfs_generator/")
sys.path.append(os.path.dirname(os.path.realpath(__file__))+"/solution_generation")
sys.path.append(os.path.dirname(os.path.realpath(__file__))+"/verification")

from parser_asm import parse_asm
import ir_block
from gasol_optimization import get_sfs_dict
from gasol_encoder import execute_syrup_backend, generate_theta_dict_from_sequence, execute_syrup_backend_combined
from solver_output_generation import obtain_solver_output
from disasm_generation import generate_info_from_solution, generate_disasm_sol_from_output, \
    read_initial_dicts_from_files, generate_disasm_sol_from_log_block, obtain_log_representation_from_solution
from solver_solution_verify import check_solver_output_is_correct, generate_solution_dict
from global_params.paths import *
from utils import isYulInstruction, compute_stack_size


def clean_dir():
    ext = ["rbr", "csv", "sol", "bl", "disasm", "json"]
    if gasol_folder in os.listdir(tmp_path):
        for elem in os.listdir(gasol_path):
            last = elem.split(".")[-1]
            if last in ext:
                os.remove(gasol_path+elem)

        if "jsons" in os.listdir(gasol_path):
            shutil.rmtree(gasol_path + "jsons")

        if "disasms" in os.listdir(gasol_path):
            shutil.rmtree(gasol_path + "disasms")

        if "smt_encoding" in os.listdir(gasol_path):
            shutil.rmtree(gasol_path + "smt_encoding")

        if "solutions" in os.listdir(gasol_path):
            shutil.rmtree(gasol_path + "solutions")


# It modifies the name of the push opcodes of yul to integrate them in a single string
def preprocess_instructions(bytecodes):
    instructions = []
    for b in bytecodes:
        op = b.getDisasm()

        if op.startswith("PUSH") and not isYulInstruction(op):
            op = op+" 0x"+b.getValue()

        else:
            if op.startswith("PUSH") and op.find("tag")!=-1:
                op = "PUSHTAG"+" 0x"+b.getValue()

            elif op.startswith("PUSH") and op.find("#[$]")!=-1:
                op = "PUSH#[$]"+" 0x"+b.getValue()

            elif op.startswith("PUSH") and op.find("[$]")!=-1:
                op = "PUSH[$]"+" 0x"+b.getValue()

            elif op.startswith("PUSH") and op.find("data")!=-1:
                op = "PUSHDATA"+" 0x"+b.getValue()

            elif op.startswith("PUSH") and op.find("IMMUTABLE")!=-1:
                op = "PUSHIMMUTABLE"+" 0x"+b.getValue()
                
            elif op.startswith("PUSH") and op.find("DEPLOYADDRESS") !=-1:
                # Fixme: add ALL PUSH variants: PUSH data, PUSH DEPLOYADDRESS
                op = "PUSHDEPLOYADDRESS"
            elif op.startswith("PUSH") and op.find("SIZE") !=-1:
                op = "PUSHSIZE"
            
        instructions.append(op)


    return instructions


def compute_original_sfs_with_simplifications(instructions, stack_size, cname, block_id, is_initial_block):
    block_ins = list(filter(lambda x: x not in ["JUMP", "JUMPI", "JUMPDEST", "tag", "INVALID"], instructions))

    block_data = {"instructions": block_ins, "input": stack_size}

    if is_initial_block:
        prefix = "initial_"
    else:
        prefix = ""

    exit_code = ir_block.evm2rbr_compiler(contract_name=cname, block=block_data, block_id=block_id,
                                          preffix=prefix, simplification=True)

    sfs_dict = get_sfs_dict()

    return sfs_dict


# Given the sequence of bytecodes, the initial stack size, the contract name and the
# block id, returns the output given by the solver, the name given to that block and current gas associated
# to that sequence.
def optimize_block(instructions,stack_size,cname,block_id, timeout, is_initial_block= False):

    sfs_dict = compute_original_sfs_with_simplifications(instructions, stack_size, cname, block_id, is_initial_block)

    # No optimization is made if sfs_dict['syrup_contract'] == {}
    if sfs_dict['syrup_contract'] == {}:
        return []

    block_solutions = []

    # SFS dict of syrup contract contains all sub-blocks derived from a block after splitting
    for block_name in sfs_dict['syrup_contract']:
        sfs_block = sfs_dict['syrup_contract'][block_name]

        current_cost = sfs_block['current_cost']
        current_size = sfs_block['max_progr_len']

        execute_syrup_backend(None, sfs_block, block_name=block_name, timeout=timeout)

        # At this point, solution is a string that contains the output directly
        # from the solver
        solver_output = obtain_solver_output(block_name, "oms", timeout)
        block_solutions.append((solver_output, block_name, current_cost, current_size))

    return block_solutions    


def compute_original_sfs_without_simplifications(instructions,stack_size,cname,block_id,is_initial_block):
    block_ins = list(filter(lambda x: x not in ["JUMP","JUMPI","JUMPDEST","tag","INVALID"], instructions))

    block_data = {"instructions": block_ins, "input": stack_size}

    if is_initial_block:
        prefix = "initial_"
    else:
        prefix = ""
        
    exit_code = ir_block.evm2rbr_compiler(contract_name=cname, block=block_data, block_id=block_id,
                                          preffix = prefix,simplification = False)

    sfs_dict = get_sfs_dict()

    return sfs_dict


# Given an asm_block and its contract name, returns the asm block after the optimization
def optimize_asm_block(block, contract_name, timeout):
    bytecodes = block.getInstructions()
    stack_size = block.getSourceStack()
    block_id = block.getBlockId()
    is_init_block = block.get_is_init_block()

    total_current_cost, total_optimized_cost = 0, 0
    total_current_length, total_optimized_length = 0,0
    optimized_blocks = []

    log_dicts = {}

    
    instructions = preprocess_instructions(bytecodes)

    sfs_original = None
    
    for solver_output, block_name, current_cost, current_length \
            in optimize_block(instructions, stack_size, contract_name, block_id, timeout, is_init_block):

        # We weren't able to find a solution using the solver, so we just update the gas consumption
        if not check_solver_output_is_correct(solver_output):

            if sfs_original is None:
                # Dict that contains a SFS per sub-block without applying rule simplifications. Useful for rebuilding
                # solutions when no solution has been found.
                sfs_original = compute_original_sfs_without_simplifications(instructions, stack_size, contract_name,
                                                                            block_id, is_init_block)

            sfs_block = sfs_original['syrup_contract'][block_name]
            opcodes = sfs_block['init_info']['opcodes_seq']
            push_values = sfs_block['init_info']['push_vals']

            bs = sfs_block['max_sk_sz']
            user_instr = sfs_block['init_info']['non_inter']
            theta_dict, instruction_theta_dict, opcodes_theta_dict, gas_theta_dict = generate_theta_dict_from_sequence(bs, user_instr)

            instr_sequence = obtain_log_representation_from_solution(opcodes, push_values, theta_dict)
            generate_disasm_sol_from_log_block(contract_name, block_name, instr_sequence,
                                               opcodes_theta_dict, instruction_theta_dict, gas_theta_dict)
            total_current_cost += current_cost
            total_optimized_cost += current_cost
            total_current_length += current_length
            total_optimized_length += current_length

            # log_dicts[contract_name + '_' + block_name] = [1, *instr_sequence]

            continue

        # If it is a block in the initial code, then we add prefix "initial_"
        # if block.get_is_init_block():
        #    block_name = "initial_" + block_name

        opcodes_theta_dict, instruction_theta_dict, gas_theta_dict = read_initial_dicts_from_files(contract_name, block_name)
        instruction_output, _, pushed_output, total_gas = \
            generate_info_from_solution(solver_output, opcodes_theta_dict, instruction_theta_dict, gas_theta_dict)

        generate_disasm_sol_from_output(contract_name, solver_output,
                                        opcodes_theta_dict, instruction_theta_dict, gas_theta_dict)

        total_current_cost += current_cost
        total_optimized_cost += min(current_cost, total_gas)

        total_current_length += current_length
        total_optimized_length += len(instruction_output)

        if current_cost > total_gas:
            optimized_blocks.append(block_name)

        # Add 0 as first element to indicate block found has been optimized
        log_dicts[contract_name + '_' + block_name] = generate_solution_dict(solver_output)

    return total_current_cost, total_optimized_cost, optimized_blocks, total_current_length, total_optimized_length, log_dicts

# Given the log file loaded in json format, current block and the contract name, generates three dicts: one that
# contains the sfs from each block, the second one contains the sequence of instructions and
# the third one is a set that contains all block ids.
def generate_sfs_dicts_from_log(block, contract_name, json_log):
    bytecodes = block.getInstructions()
    stack_size = block.getSourceStack()
    block_id = block.getBlockId()
    is_init_block = block.get_is_init_block()

    instructions = preprocess_instructions(bytecodes)

    sfs_dict = compute_original_sfs_with_simplifications(instructions, stack_size,
                                                         contract_name, block_id, is_init_block)['syrup_contract']

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
# generates the corresponding solution. All comprobations are assumed to have been done previously
def optimize_asm_block_from_log(sfs_dict, instr_sequence_dict):
    for block_id in sfs_dict:

        # By naming convention, contract name always correspond to first string concatenated with "_"
        contract_name = block_id.split("_")[0]

        sfs_block = sfs_dict[block_id]

        user_instr = sfs_block['user_instrs']

        bs = sfs_block['max_sk_sz']
        instr_sequence = instr_sequence_dict[block_id]
        _, instruction_theta_dict, opcodes_theta_dict, gas_theta_dict = generate_theta_dict_from_sequence(bs, user_instr)
        generate_disasm_sol_from_log_block(contract_name, block_id, instr_sequence,
                                        opcodes_theta_dict, instruction_theta_dict, gas_theta_dict)


def optimize_asm(file_name, timeout=10, log_generation_enabled=False):
    asm = parse_asm(file_name)
    # csv_statistics = []

    csv_out = ["contract_name, saved_gas, old_cost, optimized_cost,old_length, optimized_length, saved_length, optimized_blocks"]
    log_dicts = {}

    for c in asm.getContracts():

        # current_dict = {}
        current_cost = 0
        optimized_cost = 0
        optimized_blocks = []
        current_length = 0
        optimized_length = 0

        contract_name = (c.getContractName().split("/")[-1]).split(":")[-1]
        init_code = c.getInitCode()

        print("\nAnalyzing Init Code of: "+contract_name)
        print("-----------------------------------------\n")
        for block in init_code:
            tuple_cost = optimize_asm_block(block, contract_name, timeout)
            current_cost += tuple_cost[0]
            optimized_cost += tuple_cost[1]
            optimized_blocks.extend(tuple_cost[2])
            current_length += tuple_cost[3]
            optimized_length += tuple_cost[4]
            log_dicts.update(tuple_cost[5])

        print("\nAnalyzing Runtime Code of: "+contract_name)
        print("-----------------------------------------\n")
        for identifier in c.getDataIds():
            blocks = c.getRunCodeOf(identifier)
            for block in blocks:
                tuple_cost = optimize_asm_block(block, contract_name, timeout)
                current_cost += tuple_cost[0]
                optimized_cost += tuple_cost[1]
                optimized_blocks.extend(tuple_cost[2])
                current_length += tuple_cost[3]
                optimized_length += tuple_cost[4]
                log_dicts.update(tuple_cost[5])

        saved_gas = current_cost - optimized_cost
        saved_length = current_length - optimized_length
                
        new_line = [contract_name,str(saved_gas),str(current_cost),str(optimized_cost),str(current_length),
                    str(optimized_length),str(saved_length),str(optimized_blocks)]
        csv_out.append(",".join(new_line))
        # current_dict['old_cost'] = current_cost
        # current_dict['optimized_cost'] = optimized_cost
        # current_dict['contract_name'] = contract_name
        # current_dict['optimized_blocks'] = optimized_blocks
        # current_dict['saved_gas'] = current_cost - optimized_cost
        # current_dict['old_length'] = current_length
        # current_dict['optimized_length'] = optimized_length
        # current_dict['saved_length'] = current_length - optimized_length
        # csv_statistics.append(current_dict)

    if "solutions" not in os.listdir(gasol_path):
        os.mkdir(gasol_path+"solutions")

    with open(csv_file,'w') as f:
        f.write("\n".join(csv_out))

    if log_generation_enabled:
        log_file = gasol_path + (file_name.split("/")[-1]).split(".")[-2] + ".log"
        with open(log_file, "w") as log_f:
            json.dump(log_dicts, log_f)


def optimize_asm_from_log(file_name, json_log):
    asm = parse_asm(file_name)

    # Blocks from all contracts are checked together. Thus, we first will obtain the needed
    # information from each block
    sfs_dict, instr_sequence_dict, file_ids = {}, {}, set()

    for c in asm.getContracts():

        contract_name = (c.getContractName().split("/")[-1]).split(":")[-1]
        init_code = c.getInitCode()

        print("\nAnalyzing Init Code of: " + contract_name)
        print("-----------------------------------------\n")
        for block in init_code:
            sfs_final_block, instr_sequence_dict_block, block_ids = generate_sfs_dicts_from_log(block, contract_name, json_log)
            sfs_dict.update(sfs_final_block)
            instr_sequence_dict.update(instr_sequence_dict_block)
            file_ids.update(block_ids)

        print("\nAnalyzing Runtime Code of: " + contract_name)
        print("-----------------------------------------\n")
        for identifier in c.getDataIds():
            blocks = c.getRunCodeOf(identifier)
            for block in blocks:
                sfs_final_block, instr_sequence_dict_block, block_ids = generate_sfs_dicts_from_log(block, contract_name, json_log)
                sfs_dict.update(sfs_final_block)
                instr_sequence_dict.update(instr_sequence_dict_block)
                file_ids.update(block_ids)
                
    # We check ids in json log file matches the ones generated from the source file
    if not set(json_log.keys()).issubset(file_ids):
        print("Log file does not match source file")
    else:
        correct = check_log_file_is_correct(sfs_dict, instr_sequence_dict)
        if correct:
            optimize_asm_block_from_log(sfs_dict, instr_sequence_dict)
            print("Solution generated from log file has been verified correctly")
        else:
            print("Log file does not contain a valid solution")


def optimize_isolated_asm_block(block_name, timeout=10):

    with open(block_name,"r") as f:        
        instructions = f.readline().strip()
    f.close()
    
    opcodes = []

    ops = instructions.split(" ")
    i = 0
    #it builds the list of opcodes
  
    while i<len(ops):
        op = ops[i]
        if not op.startswith("PUSH"):
            opcodes.append(op.strip())
        else:
           
            if  not isYulInstruction(op):
                val = ops[i+1]
                op = op+" 0x"+val if not val.startswith("0x") else op+" "+val
                i=i+1
            elif op.startswith("PUSH") and op.find("DEPLOYADDRESS") !=-1:
                op = "PUSHDEPLOYADDRESS"
            elif op.startswith("PUSH") and op.find("SIZE") !=-1:
                op = "PUSHSIZE"
            elif op.startswith("PUSH") and op.find("IMMUTABLE") !=-1:
                val = ops[i+1]
                op = "PUSHIMMUTABLE"+" 0x"+ val if not val.startswith("0x") else "PUSHIMMUTABLE "+val
                i=i+1
            else:
                t = ops[i+1]
                val = ops[i+2]
                
                if op.startswith("PUSH") and t.find("tag")!=-1:
                    op = "PUSHTAG"+" 0x"+val if not val.startswith("0x") else "PUSHTAG "+val

                elif op.startswith("PUSH") and t.find("#[$]")!=-1:
                    op = "PUSH#[$]"+" 0x"+val if not val.startswith("0x") else "PUSH#[$] "+val
                    
                elif op.startswith("PUSH") and t.find("[$]")!=-1:
                    op = "PUSH[$]"+" 0x"+val if not val.startswith("0x") else "PUSH[$] "+val

                elif op.startswith("PUSH") and t.find("data")!=-1:
                    op = "PUSHDATA"+" 0x"+val if not val.startswith("0x") else "PUSHDATA "+val

                i+=2
            opcodes.append(op)

        i+=1

    stack_size = compute_stack_size(opcodes)
    contract_name = block_name.split('/')[-1]
    for solver_output, block_name, current_cost, current_length \
        in optimize_block(opcodes,stack_size,contract_name,0, timeout, False):

        # We weren't able to find a solution using the solver, so we just update the gas consumption
        if check_solver_output_is_correct(solver_output):
            opcodes_theta_dict, instruction_theta_dict, gas_theta_dict = read_initial_dicts_from_files(contract_name,
                                                                                                       "block0")
            instruction_output, _, pushed_output, total_gas = \
                generate_info_from_solution(solver_output, opcodes_theta_dict, instruction_theta_dict, gas_theta_dict)

            sol = generate_disasm_sol_from_output(contract_name, solver_output,
                                                  opcodes_theta_dict, instruction_theta_dict, gas_theta_dict)
            print("OPTIMIZED BLOCK: "+str(sol))

        else:
            print("The solver has not been able to find a better solution")



    
if __name__ == '__main__':
    clean_dir()
    ap = argparse.ArgumentParser(description='Backend of GASOL tool')
    ap.add_argument('input_path', help='Path to input file that contains the asm')
    ap.add_argument("-bl", "--block", help ="Enable analysis of a single asm block", action = "store_true")
    ap.add_argument("-tout", metavar='timeout', action='store', type=int,
                    help="Timeout in seconds. By default, set to 10s per block.", default=10)
    ap.add_argument("-optimize-gasol-from-log-file", dest='log_path', action='store', metavar="log_file",
                        help="Generates the same optimized bytecode than the one associated to the log file")
    ap.add_argument("--generate-log", help ="Enables the generation of a log file that records the "
                                            "output from the optimization process", action = "store_true")


    args = ap.parse_args()

    if args.log_path is not None:
        with open(args.log_path) as path:
            log_dict = json.load(path)
            optimize_asm_from_log(args.input_path, log_dict)
    elif not args.block:
        optimize_asm(args.input_path, args.tout, args.generate_log)
    else:
        optimize_isolated_asm_block(args.input_path, args.tout)

