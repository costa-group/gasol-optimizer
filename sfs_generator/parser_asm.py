#!/usr/bin/env python3

import json
from sfs_generator.asm_bytecode import AsmBytecode
from sfs_generator.asm_json import AsmJSON
from sfs_generator.asm_block import AsmBlock
from sfs_generator.asm_contract import AsmContract
from sfs_generator.utils import isYulKeyword
import itertools

def build_asm_bytecode(instruction):
    begin = instruction.get("begin", -1)
    end = instruction.get("end", -1)
    name = instruction.get("name", -1)
    source = instruction.get("source", -1)
    value = instruction.get("value", None)

    asm_bytecode = AsmBytecode(begin,end,source,name,value)
    return asm_bytecode


def build_blocks_from_asm_representation(cname, instr_list, is_init_code):
    bytecodes = []

    block = AsmBlock(cname,0, is_init_code)
    blockId = 1
    i = 0
    while i < len(instr_list):
        instr_name = instr_list[i]["name"]
        asm_bytecode = build_asm_bytecode(instr_list[i])

        # Final instructions of a block
        if instr_name in ["JUMP","JUMPI","STOP","RETURN","REVERT","INVALID"]:
            block.addInstructions(asm_bytecode)
            block.compute_stack_size()
            bytecodes.append(block)
            block = AsmBlock(cname,blockId, is_init_code)
            blockId+=1

        # Tag always correspond to the beginning of a new block. JUMPDEST is always preceded by a tag instruction
        elif instr_name == "tag":
            # There must be at least one instruction to add current block
            if block.getInstructions():
                block.compute_stack_size()
                bytecodes.append(block)
                block = AsmBlock(cname, blockId, is_init_code)
                blockId += 1
            block.addInstructions(asm_bytecode)
        else:
            block.addInstructions(asm_bytecode)
        i+=1

    # If last block has any instructions left, it must be added to the bytecode
    if block.getInstructions():
        block.compute_stack_size()
        bytecodes.append(block)

    return bytecodes

        
def build_asm_contract(cname,cinfo):
    asm_c = AsmContract(cname)

    if len(cinfo) > 2:
        raise Exception("ERROR. Check")

    initCode = cinfo[".code"]

    init_bytecode = build_blocks_from_asm_representation(cname, initCode, True)
    
    asm_c.setInitCode(init_bytecode)
        
    data = cinfo[".data"]

    
    for elem in data:

        if not isinstance(data[elem],str):
            aux_data = data[elem][".auxdata"]
            asm_c.setAux(elem,aux_data)

            code = data[elem][".code"]
            run_bytecode = build_blocks_from_asm_representation(cname, code, False)
            asm_c.setRunCode(elem,run_bytecode)

            data1 = data[elem].get(".data",None)
            if data1 is not None:
                asm_c.setAuxData(elem,data1)
            
        else:
            asm_c.setData(elem, data[elem])
    return asm_c

def parse_asm(file_name):
    with open(file_name) as f:
        data = json.load(f)

        
    asm_json = AsmJSON() 

    solc_v = data["version"]
    asm_json.setVersion(solc_v)
    
    contracts = data["contracts"]


    for c in contracts:
        if contracts[c].get("asm",None) is None:
            asm_json.addContracts(AsmContract(c, False))
            continue

        asm_c = build_asm_contract(c,contracts[c]["asm"])
        asm_json.addContracts(asm_c)


    return asm_json


# Given a string containing a sequence of instructions, returns a list of dicts representing each of them.
# These dicts contain the key "name", that corresponds to the name of the instruction of Assembly format and
# the key "value" if the opcode has any hexadecimal value associated.
# See https://github.com/ethereum/solidity/blob/develop/libevmasm/Assembly.cpp on how different assembly
# items are represented
def plain_instructions_to_asm_representation(raw_instruction_str):
    # We chain all strings contained in the raw string, splitting whenever a line is found or a whitespace
    split_str = list(itertools.chain.from_iterable([[elem for elem in line.split(" ")] for line in raw_instruction_str.splitlines()]))

    # We remove empty elements, as they obviously do not add any info on the sequence of opcodes
    ops = list(filter(lambda x: x != '', split_str))
    opcodes = []
    i = 0

    while i < len(ops):
        op = ops[i]
        if not op.startswith("PUSH"):
            opcodes.append({"name": op})
        else:
            if op.startswith("PUSH") and op.find("DEPLOYADDRESS") != -1:
                # Fixme: add ALL PUSH variants: PUSH data, PUSH DEPLOYADDRESS
                final_op = {"name": op}
            elif op.startswith("PUSH") and op.find("SIZE") != -1:
                final_op = {"name": op}
            # If position t+1 is a Yul Keyword, then we need to analyze them separately
            elif not isYulKeyword(ops[i + 1]):
                val = ops[i + 1]
                # The hex representation omits
                val_representation = val[2:] if val.startswith("0x") else val
                final_op = {"name": op, "value": val_representation}
                i = i + 1
            else:
                name_keyword = ops[i + 1]
                val = ops[i + 2]
                name = op + " " + name_keyword
                val_representation = val[2:] if val.startswith("0x") else val
                final_op = {"name": name, "value": val_representation}
                i += 2

            opcodes.append(final_op)

        i += 1
    return opcodes


# Conversion from a string containing all different instructions in Assembly format to ASMBlocks representation.
# See https://github.com/ethereum/solidity/blob/develop/libevmasm/Assembly.cpp on how different assembly
# items are represented
def parse_blocks_from_plain_instructions(raw_instructions_str):
    instr_list = plain_instructions_to_asm_representation(raw_instructions_str)
    blocks = build_blocks_from_asm_representation("isolated", instr_list, False)
    return blocks


# Conversion from an ASMBlock to a plain sequence of instructions
def parse_asm_representation_from_block(asm_block):
    return '\n'.join([asm_instruction.getDisasm() + ' ' + asm_instruction.getValue()
                     if asm_instruction.getValue() is not None else asm_instruction.getDisasm()
                     for asm_instruction in asm_block.getInstructions()])


# Conversion from a list of ASMBlocks to a plain sequence of instructions
def parse_asm_representation_from_blocks(asm_blocks):
    return '\n'.join([parse_asm_representation_from_block(asm_block) for asm_block in asm_blocks])