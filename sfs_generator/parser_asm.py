
import itertools
import json
import re
from typing import Union, Dict, Any

from sfs_generator.asm_block import AsmBlock
from sfs_generator.asm_bytecode import AsmBytecode, ASM_Json_T
from sfs_generator.asm_contract import AsmContract
from sfs_generator.asm_json import AsmJSON
from sfs_generator.utils import isYulKeyword
import global_params.constants as constants


def build_asm_bytecode(instruction : ASM_Json_T, pushlib_values: dict) -> AsmBytecode:
    if instruction['name'] == 'PUSHLIB':
        value = instruction['value']
        if value not in pushlib_values:
            pushlib_values[value] = len(pushlib_values)
        value = pushlib_values[value]
    else:
        value = instruction.get("value", None)

    begin = instruction.get("begin", -1)
    end = instruction.get("end", -1)
    name = instruction.get("name", -1)
    source = instruction.get("source", -1)
    jump_type = instruction.get("jumpType", None)

    # At this point, we identify PUSH0 instructions, and we create an AsmBytecode as such
    if constants.push0_enabled and name == 'PUSH' and value == "0":
        asm_bytecode = AsmBytecode(begin, end, source, "PUSH0", None, jump_type)
    else:
        asm_bytecode = AsmBytecode(begin, end, source, name, value, jump_type)

    return asm_bytecode


def _generate_block_name_from_id(block_name_prefix : str, block_id : Union[str, int]) -> str:
    return '_'.join([block_name_prefix, "block", str(block_id)])


def build_blocks_from_asm_representation(cname : str, block_name_prefix : str, instr_list : [ASM_Json_T],
                                         is_init_code : bool) -> [AsmBlock]:
    bytecodes = []

    block_id = 0
    block = AsmBlock(cname, block_id, _generate_block_name_from_id(block_name_prefix, block_id), is_init_code)
    block_id += 1
    pushlib_values = dict()

    i = 0
    while i < len(instr_list):
        instr_name = instr_list[i]["name"]
        asm_bytecode = build_asm_bytecode(instr_list[i], pushlib_values)

        # Final instructions of a block
        if instr_name in ["JUMP","JUMPI","STOP","RETURN","REVERT","INVALID"]:
            block.add_instruction(asm_bytecode)
            bytecodes.append(block)
            block = AsmBlock(cname, block_id, _generate_block_name_from_id(block_name_prefix, block_id), is_init_code)
            pushlib_values = dict()
            block_id+=1

        # Tag always correspond to the beginning of a new block. JUMPDEST is always preceded by a tag instruction
        elif instr_name == "tag":
            # There must be at least one instruction to add current block
            if block.instructions:
                bytecodes.append(block)
                block = AsmBlock(cname, block_id, _generate_block_name_from_id(block_name_prefix, block_id), is_init_code)
                pushlib_values = dict()
                block_id += 1
                
            block.tag = instr_list[i]["value"]
            block.add_instruction(asm_bytecode)
        else:
            block.add_instruction(asm_bytecode)
        i+=1

    # If last block has any instructions left, it must be added to the bytecode
    if block.instructions:
        bytecodes.append(block)
        
    return bytecodes


def build_asm_contract(cname : str, cinfo : Dict[str, Any]) -> AsmContract:
    asm_c = AsmContract(cname)

    initCode = cinfo[".code"]

    # For blocks, we are not interested in the complete path
    simplified_cname = (cname.split("/")[-1]).split(":")[-1]

    init_bytecode = build_blocks_from_asm_representation(simplified_cname, '_'.join([simplified_cname, "initial"]), initCode, True)

    asm_c.init_code = init_bytecode

    # Only available from solc v 0.8.14
    source_list = cinfo.get("sourceList", None)
    asm_c.source_list = source_list

    data = cinfo[".data"]

    for elem in data:

        if not isinstance(data[elem],str):
            aux_data = data[elem].get(".auxdata", None)
            if aux_data is not None:
                asm_c.set_auxdata(elem, aux_data)

            code = data[elem][".code"]
            run_bytecode = build_blocks_from_asm_representation(simplified_cname, '_'.join([simplified_cname, "run_code_of", str(elem)]), code, False)
            asm_c.set_run_code(elem, run_bytecode)

            data1 = data[elem].get(".data", None)
            if data1 is not None:
                asm_c.set_data_field(elem, data1)
            
        else:
            asm_c.set_data_field_with_address(elem, data[elem])

    # asm_c.build_static_edges_init()
    # asm_c.build_static_edges_runtime()
    return asm_c


def parse_json_asm(file_name: str) -> AsmContract:
    with open(file_name) as f:
        data = json.load(f)
    return build_asm_contract("contract", data)


def parse_asm(file_name : str) -> AsmJSON:
    with open(file_name) as f:
        data = json.load(f)

    solc_v = data["version"]
    asm_json = AsmJSON(solc_v)
    
    contracts = data["contracts"]


    for c in contracts:
        if contracts[c].get("asm",None) is None:
            asm_json.add_contract(AsmContract(c, False))
            continue

        asm_c = build_asm_contract(c,contracts[c]["asm"])
        asm_json.add_contract(asm_c)

    return asm_json


# Given a string containing a sequence of instructions, returns a list of dicts representing each of them.
# These dicts contain the key "name", that corresponds to the name of the instruction of Assembly format and
# the key "value" if the opcode has any hexadecimal value associated.
# See https://github.com/ethereum/solidity/blob/develop/libevmasm/Assembly.cpp on how different assembly
# items are represented
def plain_instructions_to_asm_representation(raw_instruction_str : str) -> [ASM_Json_T]:
    # We chain all strings contained in the raw string, splitting whenever a line is found or a whitespace
    split_str = list(itertools.chain.from_iterable([[elem for elem in line.split(" ")] for line in raw_instruction_str.splitlines()]))

    # We remove empty elements, as they obviously do not add any info on the sequence of opcodes
    ops = list(filter(lambda x: x != '', split_str))
    opcodes = []
    i = 0
    pushlib_values = dict()

    while i < len(ops):
        op = ops[i]
        if op.startswith("ASSIGNIMMUTABLE") or op.startswith("tag"):
            opcodes.append({"name": op, "value": ops[i + 1]})
            i += 1
        elif op.startswith('PUSHLIB'):
            value = ops[i+1]
            if value not in pushlib_values:
                pushlib_values[value] = len(pushlib_values)
            opcodes.append({"name": op, "value": pushlib_values[ops[i+1]]})
            i += 1
        elif not op.startswith("PUSH"):
            opcodes.append({"name": op})
        else:
            if op.startswith("PUSH") and op.find("DEPLOYADDRESS") != -1:
                # Fixme: add ALL PUSH variants: PUSH data, PUSH DEPLOYADDRESS
                final_op = {"name": op}
            elif op.startswith("PUSH") and op.find("SIZE") != -1:
                final_op = {"name": op}
            # PUSH0 is parsed similarly to PUSH 0, and is interpreted as one form or the other depending on the
            # flag --push0
            elif op.startswith("PUSH0"):
                val_representation = "0"
                final_op = {"name": "PUSH", "value": val_representation}
            # This case refers to PUSHx opcodes, that are allowed in the plain representation
            elif re.fullmatch("PUSH([0-9]+)", op) is not None:
                val = ops[i + 1]
                # The hex representation omits
                if val.startswith("0x"):
                    val_representation = val[2:]
                else:
                    val_representation = hex(int(val))[2:]
                final_op = {"name": "PUSH", "value": val_representation}
                i = i + 1

            # If position t+1 is a Yul Keyword, then we need to analyze them separately
            elif not isYulKeyword(ops[i + 1]):
                val = ops[i + 1]
                # The hex representation omits
                val_representation = hex(int(val, 16))[2:]
                final_op = {"name": op, "value": val_representation}
                i = i + 1
            else:
                name_keyword = ops[i + 1]
                val = ops[i + 2]
                name = op + " " + name_keyword
                val_representation = hex(int(val, 16))[2:]
                final_op = {"name": name, "value": val_representation}
                i += 2

            opcodes.append(final_op)

        i += 1
    return opcodes


# Conversion from a string containing all different instructions in Assembly format to ASMBlocks representation.
# See https://github.com/ethereum/solidity/blob/develop/libevmasm/Assembly.cpp on how different assembly
# items are represented
def parse_blocks_from_plain_instructions(raw_instructions_str, cname = "", block_name_prefix = ""):
    instr_list = plain_instructions_to_asm_representation(raw_instructions_str)
    if cname == "" and block_name_prefix == "":
        blocks = build_blocks_from_asm_representation("isolated", "isolated", instr_list, False)
    else:
        blocks = build_blocks_from_asm_representation(cname, block_name_prefix, instr_list, False)
    return blocks


# Similar to the previous function, but assuming the raw_instructions correspond to a simple block
def generate_block_from_plain_instructions(raw_instructions_str: str, block_name: str, is_init_block: bool = False) -> AsmBlock:
    instr_list = plain_instructions_to_asm_representation(raw_instructions_str)
    block = AsmBlock('optimized', -1, block_name, is_init_block)
    pushlib_value = dict()
    block.instructions = [build_asm_bytecode(instr, pushlib_value) for instr in instr_list]
    return block

# Conversion from an ASMBlock to a plain sequence of instructions
def parse_asm_representation_from_block(asm_block : AsmBlock):
    return '\n'.join([asm_instruction.disasm + ' ' + asm_instruction.value
                     if asm_instruction.value is not None else asm_instruction.disasm
                     for asm_instruction in asm_block.instructions])


# Conversion from a list of ASMBlocks to a plain sequence of instructions
def parse_asm_representation_from_blocks(asm_blocks):
    return '\n'.join([parse_asm_representation_from_block(asm_block) for asm_block in asm_blocks])
