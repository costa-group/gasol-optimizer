# Module that contains methods for determining different properties from an AsmJSON object

from statistics_utils import number_encoding_size
import re

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


# Taken directly from https://github.com/ethereum/solidity/blob/develop/libevmasm/AssemblyItem.cpp
# Address length: maximum address a tag can appear. By default 4 (as worst case for PushSubSize is 16 MB)
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


def bytes_required_initial_plain(op_name, address_length = 4):
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