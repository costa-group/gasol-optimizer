#!/usr/bin/env python3

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

        json_data_fields = {}

        aux_data = asm_contract.get_aux(data_id)
        json_data_fields[".auxdata"] = aux_data

        run_bytecode = rebuild_asm_block(asm_contract.getRunCodeOf(data_id))
        json_data_fields[".code"] = run_bytecode

        data = asm_contract.get_data_aux(data_id)
        if data is not None:
            json_data_fields[".data"] = data

        json_data[data_id] = json_data_fields

    data_addresses = asm_contract.getDataFieldIds()

    for address in data_addresses:
        json_data[address] = asm_contract.getDataField(address)

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
