#!/usr/bin/env python3

import json
from sfs_generator.asm_bytecode import AsmBytecode
from sfs_generator.asm_json import AsmJSON
from sfs_generator.asm_block import AsmBlock
from sfs_generator.asm_contract import AsmContract

def buildAsmBytecode(instruction):
    begin = instruction["begin"]
    end = instruction["end"]
    name = instruction["name"]
    source = instruction["source"]
    value = instruction.get("value", None)

    asm_bytecode = AsmBytecode(begin,end,source,name,value)
    return asm_bytecode


def buildBlocks(cname,instr_list, is_init_code):
    bytecodes = []

    block = AsmBlock(cname,0, is_init_code)
    blockId = 1

    i = 0
    last = ""
    while i < len(instr_list):
        instr_name = instr_list[i]["name"]
        asm_bytecode = buildAsmBytecode(instr_list[i])
        if instr_name in ["JUMP","JUMPI","STOP","RETURN","REVERT","INVALID","JUMPDEST"]:
            block.addInstructions(asm_bytecode)
            block.compute_stack_size()
            bytecodes.append(block)
            last = instr_name
            block = AsmBlock(cname,blockId, is_init_code)
            blockId+=1
        elif instr_name == "tag":
            if last not in ["JUMP","JUMPI","STOP","RETURN","REVERT","INVALID","JUMPDEST"]:
                block.compute_stack_size()
                bytecodes.append(block)
                last = ""
                block = AsmBlock(cname,blockId, is_init_code)
                blockId+=1
            block.addInstructions(asm_bytecode)
        else:
            block.addInstructions(asm_bytecode)
        i+=1

    if last not in ["JUMP","JUMPI","STOP","RETURN","REVERT","INVALID","JUMPDEST"] and block not in bytecodes:
        bytecodes.append(block)
        block.compute_stack_size()
        
    # for i in bytecodes:
    #     print(i)

    return bytecodes

        
def build_asm_contract(cname,cinfo):
    asm_c = AsmContract(cname)

    if len(cinfo) > 2:
        raise Exception("ERROR. Check")

    initCode = cinfo[".code"]

    init_bytecode = buildBlocks(cname, initCode, True)
    
    asm_c.setInitCode(init_bytecode)
        
    data = cinfo[".data"]

    
    for elem in data:

        if not isinstance(data[elem],str):
            aux_data = data[elem][".auxdata"]
            asm_c.setAux(elem,aux_data)

            code = data[elem][".code"]
            run_bytecode = buildBlocks(cname,code, False)
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
        
