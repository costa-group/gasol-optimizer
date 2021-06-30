#!/usr/bin/python3

import argparse
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
from python_syrup import execute_syrup_backend
from solver_output_generation import obtain_solver_output
from disasm_generation import generate_info_from_solution, generate_disasm_sol_from_output, read_initial_dicts_from_files
from solver_solution_verify import check_solver_output_is_correct
from global_params import gasol_path, tmp_path, gasol_folder
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


# Given the sequence of bytecodes, the initial stack size, the contract name and the
# block id, returns the output given by the solver, the name given to that block and current gas associated
# to that sequence.
def optimize_block(bytecodes, stack_size, cname, block_id, timeout=10, is_initial_block=False):

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
                
            elif op.startswith("PUSH") and op.find("DEPLOYADDRESS") !=-1:
                # Fixme: add ALL PUSH variants: PUSH data, PUSH DEPLOYADDRESS
                op = "PUSHDEPLOYADDRESS"

        instructions.append(op)

    return optimize_instructions(instructions,stack_size,cname,block_id, timeout, is_initial_block)

def optimize_instructions(instructions,stack_size,cname,block_id, timeout, is_initial_block):
    block_ins = list(filter(lambda x: x not in ["JUMP","JUMPI","JUMPDEST","tag","INVALID"], instructions))

    block_data = {"instructions": block_ins, "input": stack_size}

    #TODO: añadir nuevas instrucciones
    exit_code = ir_block.evm2rbr_compiler(contract_name=cname,
                                                   block=block_data, block_id=block_id,preffix = preffix)

    sfs_dict = get_sfs_dict()

    # No optimization is made if sfs_dict['syrup_contract'] == {}
    if sfs_dict['syrup_contract'] == {}:
        return []

    block_solutions = []

    # SFS dict of syrup contract contains all sub-blocks derived from a block after splitting
    for block_name in sfs_dict['syrup_contract']:
        sfs_block = sfs_dict['syrup_contract'][block_name]

        current_cost = sfs_block['current_cost']
        current_size = sfs_block['max_progr_len']

        block_name = block_name
        # If it belongs to the initial code, then we add prefix initial so no confusion can be derive

        execute_syrup_backend(None, sfs_block, block_name=block_name, timeout=timeout)

        # At this point, solution is a string that contains the output directly
        # from the solver
        solver_output = obtain_solver_output(block_name, "oms", timeout)
        block_solutions.append((solver_output, block_name, current_cost, current_size))

    return block_solutions    

# Given an asm_block and its contract name, returns the asm block after the optimization
def optimize_asm_block(block, contract_name, timeout):
    bytecodes = block.getInstructions()
    stack_size = block.getSourceStack()
    block_id = block.getBlockId()
    is_init_block = block.get_is_init_block()

    total_current_cost, total_optimized_cost = 0, 0
    total_current_length, total_optimized_length = 0,0
    optimized_blocks = []

    for solver_output, block_name, current_cost, current_length \
            in optimize_block(bytecodes, stack_size, contract_name, block_id, timeout, is_init_block):

        # We weren't able to find a solution using the solver, so we just update the gas consumption
        if not check_solver_output_is_correct(solver_output):
            total_current_cost += current_cost
            total_optimized_cost += current_cost
            total_current_length += current_length
            total_optimized_length += current_length
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

    return total_current_cost, total_optimized_cost, optimized_blocks, total_current_length, total_optimized_length


def optimize_asm(file_name, timeout=10):
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

    csv_file = "/tmp/gasol/solutions/statistics.csv"
    with open(csv_file,'w') as f:
        f.write("\n".join(csv_out))




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
        in optimize_instructions(opcodes,stack_size,contract_name,0, timeout, False):

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

    args = ap.parse_args()

    if not args.block:
        optimize_asm(args.input_path, args.tout)
    else:
        optimize_isolated_asm_block(args.input_path, args.tout)

