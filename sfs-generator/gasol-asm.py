#!/usr/bin/python3
import argparse
import os
import sys
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/backend")
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/ethir")
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/solution_generation")
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/verification")

from parser_asm import parse_asm
import rbr_isolate_block
from syrup_optimization import get_sfs_dict
from python_syrup import execute_syrup_backend
sys.path.append(os.path.dirname(os.path.realpath(__file__))+"/../syrup_full_execution.py")
from solver_output_generation import obtain_solver_output
from disasm_generation import generate_info_from_solution, generate_disasm_sol
from solver_solution_verify import check_solver_output_is_correct
from oyente_ethir import clean_dir
import pandas as pd

def isYulInstruction(opcode):
    if opcode.find("tag") ==-1 and opcode.find("#") ==-1 and opcode.find("$") ==-1 \
            and opcode.find("data") ==-1 and opcode.find("DEPLOY") ==-1:
        return False
    else:
        return True


# Given the sequence of bytecodes, the initial stack size, the contract name and the
# block id, returns the output given by the solver, the name given to that block and current gas associated
# to that sequence.
def optimize_block(bytecodes, stack_size, cname, block_id, preffix=""):

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

            elif op.startswith("PUSH"):
                # Fixme: add ALL PUSH variants: PUSH data, PUSH DEPLOYADDRESS
                op = "PUSHTAG" + " 0x" + b.getValue()

        instructions.append(op)
        
    block_ins = list(filter(lambda x: x not in ["JUMP","JUMPI","JUMPDEST","tag","INVALID"], instructions))

    block_data = {"instructions": block_ins, "input": stack_size}

    #TODO: añadir nuevas instrucciones
    exit_code = rbr_isolate_block.evm2rbr_compiler(contract_name=cname, syrup=True,
                                                   block=block_data, sto=True, block_id=block_id)
    #TODO llamar a optimización

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
        block_name = preffix + block_name
        execute_syrup_backend(None, sfs_block, block_name=block_name)

        # At this point, solution is a string that contains the output directly
        # from the solver
        solver_output = obtain_solver_output(block_name, "oms", 10)
        block_solutions.append((solver_output, block_name, current_cost, current_size))

    return block_solutions


# Given an asm_block and its contract name, returns the asm block after the optimization
def optimize_asm_block(block, contract_name, init=False):
    bytecodes = block.getInstructions()
    stack_size = block.getSourceStack()
    block_id = block.getBlockId()

    if init:
        preffix = "initial_"
    else:
        preffix = ""

    total_current_cost, total_optimized_cost = 0, 0
    total_current_length, total_optimized_length = 0,0
    optimized_blocks = []

    for solver_output, block_name, current_cost, current_length \
            in optimize_block(bytecodes, stack_size, contract_name, block_id, preffix):

        # We weren't able to find a solution using the solver, so we just update the gas consumption
        if not check_solver_output_is_correct(solver_output):
            total_current_cost += current_cost
            total_optimized_cost += current_cost
            total_current_length += current_length
            total_optimized_length += current_length
            continue

        instruction_output, _, pushed_output, total_gas = generate_info_from_solution(contract_name, block_name, solver_output)

        generate_disasm_sol(contract_name, block_name, solver_output)

        total_current_cost += current_cost
        total_optimized_cost += min(current_cost, total_gas)

        total_current_length += current_length
        total_optimized_length += len(instruction_output)

        if current_cost > total_gas:
            optimized_blocks.append(block_name)

    return total_current_cost, total_optimized_cost, optimized_blocks, total_current_length, total_optimized_length

        # Found solution does not improve the previous one, so we return the same block
        # print(total_gas, current_cost)
        #if total_gas >= current_cost:
        #    return block
        # TODO: generate new block from instruction output + pushed_output
        #else:
        #    print("LLEGUE!")
        #    return block


def optimize_asm(file_name):
    asm = parse_asm(file_name)
    csv_statistics = []
    for c in asm.getContracts():

        current_dict = {}
        current_cost = 0
        optimized_cost = 0
        optimized_blocks = []
        current_length = 0
        optimized_length = 0

        contract_name = (c.getContractName().split("/")[-1]).split(":")[-1]
        init_code = c.getInitCode()

        for block in init_code:
            tuple_cost = optimize_asm_block(block, contract_name, True)
            current_cost += tuple_cost[0]
            optimized_cost += tuple_cost[1]
            optimized_blocks.extend(tuple_cost[2])
            current_length += tuple_cost[3]
            optimized_length += tuple_cost[4]

        for identifier in c.getDataIds():
            blocks = c.getRunCodeOf(identifier)
            for block in blocks:
                tuple_cost = optimize_asm_block(block, contract_name)
                current_cost += tuple_cost[0]
                optimized_cost += tuple_cost[1]
                optimized_blocks.extend(tuple_cost[2])
                current_length += tuple_cost[3]
                optimized_length += tuple_cost[4]

        current_dict['old_cost'] = current_cost
        current_dict['optimized_cost'] = optimized_cost
        current_dict['contract_name'] = contract_name
        current_dict['optimized_blocks'] = optimized_blocks
        current_dict['saved_gas'] = current_cost - optimized_cost
        current_dict['old_length'] = current_length
        current_dict['optimized_length'] = optimized_length
        current_dict['saved_length'] = current_length - optimized_length
        csv_statistics.append(current_dict)

    df = pd.DataFrame(csv_statistics, columns=['contract_name', 'saved_gas', 'old_cost', 'optimized_cost',
                                               'old_length', 'optimized_length', 'saved_length', 'optimized_blocks'])
    csv_file = "/tmp/gasol/solutions/statistics.csv"
    df.to_csv(csv_file)


if __name__ == '__main__':
    clean_dir()
    ap = argparse.ArgumentParser(description='Backend of gasol tool')
    ap.add_argument('json_path', help='Path to json file that contains the asm')
    args = ap.parse_args()
    optimize_asm(args.json_path)
