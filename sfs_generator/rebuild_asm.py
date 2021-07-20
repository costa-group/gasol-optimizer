#!/usr/bin/env python3
import argparse
import json
import sys
sys.path.append("../")
import sfs_generator.parser_asm
from deepdiff import DeepDiff

def rebuild_asm_bytecode(asm_bytecode):
    json_bytecode = {"begin": asm_bytecode.getBegin(), "end": asm_bytecode.getEnd(), "name": asm_bytecode.getDisasm(),
                     "source": asm_bytecode.getSource()}

    if asm_bytecode.getValue() is not None :
        json_bytecode["value"] = asm_bytecode.getValue()

    return json_bytecode

# Given a list of blocks of instructions, the initial code is rebuilt
def rebuild_asm_block(asm_blocks):

    json_code = []

    for block in asm_blocks:
        for instr in block.getInstructions():
            json_code.append(rebuild_asm_bytecode(instr))

    return json_code


def rebuild_asm_contract(asm_contract):

    json_contract = {".code": rebuild_asm_block(asm_contract.getInitCode())}

    data_ids = asm_contract.getDataIds()

    json_data = {}

    for data_id in data_ids:


        if not asm_contract.is_data_address(data_id):

            json_data_fields = {}

            aux_data = asm_contract.get_aux(data_id)
            json_data_fields[".auxdata"] = aux_data

            run_bytecode = rebuild_asm_block(asm_contract.getRunCodeOf(data_id))
            json_data_fields[".code"] = run_bytecode

            data = asm_contract.get_data_aux(data_id)
            if data is not None:
                json_data_fields[".data"] = data

            json_data[data_id] = json_data_fields

        else:
            json_data[data_id] = asm_contract.getDataField(data_id)

    json_contract[".data"] = json_data

    return {asm_contract.getContractName() : {"asm" : json_contract}}


def rebuild_asm(asm_json):

    final_asm = {"version": asm_json.getVersion()}

    contracts = {}

    for c in asm_json.getContracts():

        # If it has no asm field, then we just add the contract name to the json dict
        if not c.has_asm_field():
            contracts.update({c.getContractName() : {}})
            continue

        contract = rebuild_asm_contract(c)
        contracts.update(contract)

    final_asm["contracts"] = contracts

    return final_asm

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description='Backend of GASOL tool')
    ap.add_argument('input_path', help='Path to input file that contains the asm')

    args = ap.parse_args()
    asm = sfs_generator.parser_asm.parse_asm(args.input_path)
    final_json = rebuild_asm(asm)

    with open(args.input_path) as f:
        data = json.load(f)

    diff = DeepDiff(data, final_json)
    print(diff)

    #with open("prueba.json", 'w') as f:
    #    f.write(json.dumps(final_json))
