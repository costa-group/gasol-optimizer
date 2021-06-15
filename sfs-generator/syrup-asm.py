#!/usr/bin/python3

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
from disasm_generation import generate_info_from_solution
from solver_solution_verify import check_solver_output_is_correct

def isYulInstruction(opcode):
    if opcode.find("tag") ==-1 and opcode.find("#") ==-1 and opcode.find("$")==-1:
        return False
    else:
        return True


# Given the sequence of bytecodes, the initial stack size, the contract name and the
# block id, returns the output given by the solver, the name given to that block and current gas associated
# to that sequence.
def optimize_block(bytecodes, stack_size, cname, block_id):

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
        return "", "", 0

    # In order to obtain the dict in the format for syrup, we have
    # to access the values of the values, as first key corresponds to the
    # contract and the second to current block.
    block_name = list(sfs_dict['syrup_contract'].keys())[0]
    sfs_block = sfs_dict['syrup_contract'][block_name]

    current_cost = sfs_block['current_cost']
    execute_syrup_backend(None, sfs_block, block_name=block_name)

    # At this point, solution is a string that contains the output directly
    # from the solver
    solver_output = obtain_solver_output(block_name, "oms", 10)
    return solver_output, block_name, current_cost


# Given an asm_block and its contract name, returns the asm block after the optimization
def optimize_asm_block(block, contract_name):
    bytecodes = block.getInstructions()
    stack_size = block.getSourceStack()
    block_id = block.getBlockId()

    solver_output, block_name, current_cost = optimize_block(bytecodes, stack_size, contract_name, block_id)

    # We weren't able to find a solution using the solver, so we return the same block
    if not check_solver_output_is_correct(solver_output):
        return block

    instruction_output, _, pushed_output, total_gas = generate_info_from_solution(block_name, solver_output)

    # Found solution does not improve the previous one, so we return the same block
    if total_gas >= current_cost:
        return block
    # TODO: generate new block from instruction output + pushed_output
    else:
        pass


def optimize_asm(file_name):
    asm = parse_asm(file_name)

    for c in asm.getContracts():

        contract_name = c.getContractName().split("/")[-1]
        init_code = c.getInitCode()

        init_blocks = []

        for block in init_code:
            init_blocks.append(optimize_asm_block(block, contract_name))

        data_blocks = []

        for identifier in c.getDataIds():
            blocks = c.getRunCodeOf(identifier)
            for block in blocks:
                data_blocks.append(optimize_asm_block(block, contract_name))

        print(init_blocks, data_blocks)


if __name__ == '__main__':
    file_name = "salida"
    optimize_asm(file_name)
