from smt_encoding.complete_encoding.synthesis_full_encoding import SMS_T
from sfs_generator.asm_bytecode import AsmBytecode
from typing import List, Dict, Any


def id_to_asm_bytecode(uf_instrs: Dict[str, Dict[str, Any]], instr_id: str) -> AsmBytecode:
    # AsmBytecode(-1, -1, -1, , )
    if instr_id in uf_instrs:
        associated_instr = uf_instrs[instr_id]

        # Special case: reconstructing PUSH0 (see sfs_generator/parser_asm.py)
        if associated_instr["disasm"] == "PUSH0":
            return AsmBytecode(-1, -1, -1, "PUSH", "0")
        # Special PUSH cases that were transformed to decimal are analyzed separately
        elif associated_instr['disasm'] == "PUSH" or associated_instr['disasm'] == "PUSH data" \
                or associated_instr['disasm'] == "PUSHIMMUTABLE":
            value = hex(int(associated_instr['value'][0]))[2:]
            return AsmBytecode(-1, -1, -1, associated_instr['disasm'], value)
        else:
            return AsmBytecode(-1, -1, -1, associated_instr['disasm'],
                               None if 'value' not in associated_instr else str(associated_instr['value'][0]))

    else:
        # The id is the instruction itself
        return AsmBytecode(-1, -1, -1, instr_id, None)


def id_seq_to_asm_bytecode(uf_instrs: Dict[str, Dict[str, Any]], id_seq: List[str]) -> List[AsmBytecode]:
    return [id_to_asm_bytecode(uf_instrs, instr_id) for instr_id in id_seq if instr_id != 'NOP']


def asm_from_ids(sms: SMS_T, id_seq: List[str]) -> List[AsmBytecode]:
    instr_id_to_instr = {instr['id']: instr for instr in sms['user_instrs']}
    return id_seq_to_asm_bytecode(instr_id_to_instr, id_seq)
