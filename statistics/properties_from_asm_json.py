# Module that contains methods for determining different properties from an AsmJSON object

import re
from sfs_generator.utils import get_ins_size, isYulInstruction
import sfs_generator.opcodes as opcodes

def asm_instruction_to_plain(asm_bytecode):
    op = asm_bytecode.getDisasm()

    if op.startswith("PUSH") and not isYulInstruction(op):
        op = op + " 0x" + asm_bytecode.getValue()

    else:
        if op.startswith("PUSH") and op.find("tag") != -1:
            op = "PUSHTAG" + " 0x" + asm_bytecode.getValue()

        elif op.startswith("PUSH") and op.find("#[$]") != -1:
            op = "PUSH#[$]" + " 0x" + asm_bytecode.getValue()

        elif op.startswith("PUSH") and op.find("[$]") != -1:
            op = "PUSH[$]" + " 0x" + asm_bytecode.getValue()

        elif op.startswith("PUSH") and op.find("data") != -1:
            op = "PUSHDATA" + " 0x" + asm_bytecode.getValue()

        elif op.startswith("PUSH") and op.find("IMMUTABLE") != -1:
            op = "PUSHIMMUTABLE" + " 0x" + asm_bytecode.getValue()

        elif op.startswith("PUSH") and op.find("LIB") != -1:
            op = "PUSHLIB" + " 0x" + asm_bytecode.getValue()

        elif op.startswith("PUSH") and op.find("DEPLOYADDRESS") != -1:
            # Fixme: add ALL PUSH variants: PUSH data, PUSH DEPLOYADDRESS
            op = "PUSHDEPLOYADDRESS"
        elif op.startswith("PUSH") and op.find("SIZE") != -1:
            op = "PUSHSIZE"

    return op


# It modifies the name of the push opcodes of yul to integrate them in a single string
def preprocess_instructions(bytecodes):
    instructions = []
    for asm_bytecode in bytecodes:
        instructions.append(asm_instruction_to_plain(asm_bytecode))
    return instructions


# Computes the number of bytecodes given an ASM json object
def compute_number_of_instructions_in_asm_json_per_contract(asm_json):
    contract_counter_dict = {}
    for c in asm_json.getContracts():
        number_instrs = 0
        contract_name = (c.getContractName().split("/")[-1]).split(":")[-1]

        for identifier in c.getDataIds():
            blocks = c.getRunCodeOf(identifier)
            for block in blocks:
                number_instrs += len(list(filter(lambda x: x.getDisasm() != "tag", block.getInstructions())))

        contract_counter_dict[contract_name] = number_instrs
    return contract_counter_dict


# Computes the number of bytecodes given an ASM json object
def compute_number_of_instructions_in_asm_json_per_file(asm_json):
    contract_counter_dict = compute_number_of_instructions_in_asm_json_per_contract(asm_json)
    return sum(contract_counter_dict.values())


def bytes_required_asm(asm_bytecode, address_length = 4):
    plain_representation = asm_instruction_to_plain(asm_bytecode)
    operands = list(filter(lambda x: x != '', plain_representation.split(' ')))
    if len(operands) == 1:
        return get_ins_size(operands[0], None, address_length)
    elif len(operands) == 2:
        return get_ins_size(operands[0], int(operands[1], 16), address_length)
    else:
        raise ValueError("Opcodes have only 1 or 2 operands")


def compute_bytecode_size_in_asm_json_per_block(asm_block):
    return sum([bytes_required_asm(asm_bytecode) for asm_bytecode in asm_block.getInstructions()])


# Computes the size of the bytecode given an ASM json object
def compute_bytecode_size_in_asm_json_per_contract(asm_json):
    contract_counter_dict = {}
    for c in asm_json.getContracts():
        bytecode_size = 0
        contract_name = (c.getContractName().split("/")[-1]).split(":")[-1]

        for identifier in c.getDataIds():
            blocks = c.getRunCodeOf(identifier)
            for block in blocks:
                bytecode_size += compute_bytecode_size_in_asm_json_per_block(block)
        contract_counter_dict[contract_name] = bytecode_size
    return contract_counter_dict


# Computes the number of bytecodes given an ASM json object
def compute_bytecode_size_in_asm_json_per_file(asm_json):
    contract_counter_dict = compute_bytecode_size_in_asm_json_per_contract(asm_json)
    return sum(contract_counter_dict.values())