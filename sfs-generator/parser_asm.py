#!/usr/bin/env python3

import json
from asm_bytecode import AsmBytecode
from asm_json import AsmJSON
from asm_block import AsmBlock
from asm_contract import AsmContract

def buildAsmBytecode(instruction):
    begin = instruction["begin"]
    end = instruction["end"]
    name = instruction["name"]
    source = instruction.get("source", -1)
    value = instruction.get("value", "0000000000000000000000000000000000000000000000000000000000000000")

    asm_bytecode = AsmBytecode(begin,end,source,name,value)
    return asm_bytecode


def buildBlocks(cname,instr_list):
    bytecodes = []

    block = AsmBlock(cname,0)
    blockId = 1

    i = 0
    last = ""
    while i < len(instr_list):
        instr_name = instr_list[i]["name"]
        asm_bytecode = buildAsmBytecode(instr_list[i])
        if instr_name in ["JUMP","JUMPI","STOP","RETURN","REVERT","INVALID"]:
            block.addInstructions(asm_bytecode)
            block.compute_stack_size()
            bytecodes.append(block)
            last = instr_name
            block = AsmBlock(cname,blockId)
            blockId+=1
        elif instr_name == "tag":
            if last not in ["JUMP","JUMPI","STOP","RETURN","REVERT","INVALID"]:
                block.compute_stack_size()
                bytecodes.append(block)
                last = ""
                block = AsmBlock(cname,blockId)
                blockId+=1
            block.addInstructions(asm_bytecode)
        else:
            block.addInstructions(asm_bytecode)
        i+=1

    if last not in ["JUMP","JUMPI","STOP","RETURN","REVERT","INVALID"] and block not in bytecodes:
        bytecodes.append(block)
        block.compute_stack_size()
        
    for i in bytecodes:
        print(i)

    return bytecodes

        
def build_asm_contract(cname,cinfo):
    asm_c = AsmContract(cname)

    if len(cinfo) > 2:
        raise Exception("ERROR. Check")

    initCode = cinfo[".code"]

    init_bytecode = buildBlocks(cname, initCode)
    
    asm_c.setInitCode(init_bytecode)
        
    data = cinfo[".data"]

    print("*****************")
    
    for elem in data:
        aux_data = data[elem][".auxdata"]
        asm_c.setAux(elem,aux_data)

        code = data[elem][".code"]
        run_bytecode = buildBlocks(cname,code)
        asm_c.setRunCode(elem,run_bytecode)
        
    return asm_c

def parse_asm(file_name):
    with open(file_name) as f:
        data = json.load(f)

        
    asm_json = AsmJSON() 

    solc_v = data["version"]
    asm_json.setVersion(solc_v)
    
    contracts = data["contracts"]

    
    for c in contracts:
        if contracts[c]["asm"] is None:
            continue
        asm_c = build_asm_contract(c,contracts[c]["asm"])
        asm_json.addContracts(asm_c)


    return asm_json
        
if __name__ == '__main__':

    file_name = "salida"
    parse_asm(file_name)
