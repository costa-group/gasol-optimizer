from sfs_generator.asm_block import AsmBlock
from sfs_generator.asm_bytecode import AsmBytecode, ASM_Json_T
from typing import List

def rebuild_asm_bytecode(asm_bytecode : AsmBytecode) -> ASM_Json_T:
    json_bytecode = {"begin": asm_bytecode.begin, "end": asm_bytecode.end, "name": asm_bytecode.disasm,
                     "source": asm_bytecode.source}

    if asm_bytecode.value is not None :
        json_bytecode["value"] = asm_bytecode.value

    return json_bytecode

# Given a list of blocks of instructions, the initial code is rebuilt
def rebuild_asm_block(asm_blocks : List[AsmBlock]):

    json_code = []

    for block in asm_blocks:
        for instr in block.instructions:
            json_code.append(rebuild_asm_bytecode(instr))

    return json_code


def rebuild_asm_contract(asm_contract):

    json_contract = {".code": rebuild_asm_block(asm_contract.init_code)}

    data_ids = asm_contract.get_data_ids_with_code()

    json_data = {}

    for data_id in data_ids:

        json_data_fields = {}

        aux_data = asm_contract.get_auxdata(data_id)
        json_data_fields[".auxdata"] = aux_data

        run_bytecode = rebuild_asm_block(asm_contract.get_run_code(data_id))
        json_data_fields[".code"] = run_bytecode

        data = asm_contract.get_data_field(data_id)
        if data is not None:
            json_data_fields[".data"] = data

        json_data[data_id] = json_data_fields

    data_addresses = asm_contract.get_data_ids_with_data_address()

    for address in data_addresses:
        json_data[address] = asm_contract.get_data_address(address)

    json_contract[".data"] = json_data

    return {asm_contract.contract_name : {"asm" : json_contract}}


def rebuild_asm(asm_json):

    final_asm = {"version": asm_json.version}

    contracts = {}

    for c in asm_json.contracts:

        # If it has no asm field, then we just add the contract name to the json dict
        if not c.has_asm_field:
            contracts.update({c.contract_name : {}})
            continue

        contract = rebuild_asm_contract(c)
        contracts.update(contract)

    final_asm["contracts"] = contracts

    return final_asm
