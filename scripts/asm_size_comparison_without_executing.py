#!/usr/bin/env python3
import os
import sys
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))) + global_params)
import glob
from paths import project_path
from parser_asm import parse_asm

parent_directory = project_path + "/experiments/jsons-solc"

def number_encoding_size(number):
    i = 0
    while number != 0:
        i += 1
        number = number >> 8
    return i

def bytes_required(asm_bytecode, address_length = 4):
    op_name = asm_bytecode.getDisasm()
    if not op_name.startswith("PUSH") or op_name == "tag":
        return 1
    elif op_name == "PUSH":
        return 1 + max(1, number_encoding_size(int(asm_bytecode.getValue(), 16)))
    elif op_name == "PUSH #[$]" or op_name == "PUSHSIZE":
        return 1 + 4
    elif op_name == "PUSH [tag]" or op_name == "PUSH data" or op_name == "PUSH [$]":
        return 1 + address_length
    elif op_name == "PUSHLIB" or op_name == "PUSHDEPLOYADDRESS":
        return 1 + 20
    elif op_name == "PUSHIMMUTABLE":
        return 1 + 32
    elif op_name == "ASSIGNIMMUTABLE":
        # Number of PushImmutable's with the same hash. Assume 1 (?)
        m_immutableOccurrences = 1
        return 1 + (3 + 32) * m_immutableOccurrences
    else:
        raise ValueError("Opcode not recognized")


def compute_bytecode_size_in_asm_json_per_block(asm_block):
    return sum([bytes_required(asm_bytecode) for asm_bytecode in asm_block.getInstructions()])


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

if __name__ == "__main__":
    sol = 0
    for asm_json in glob.glob(parent_directory + "/*.json_solc"):
        contract_name = asm_json.split("/")[-1].rstrip(".json_solc")
        old_asm = parse_asm(asm_json)
        sol += compute_bytecode_size_in_asm_json_per_contract(old_asm)
    print(sol)