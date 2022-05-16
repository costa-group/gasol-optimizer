import re

from smt_encoding.instructions.comm_uninterpreted import \
    CommutativeUninterpreted
from smt_encoding.instructions.dupk_basic import DupKBasic
from smt_encoding.instructions.non_comm_uninterpreted import \
    NonCommutativeUninterpreted
from smt_encoding.instructions.nop_basic import NopBasic
from smt_encoding.instructions.pop_basic import PopBasic
from smt_encoding.instructions.pop_uninterpreted import PopUninterpreted
from smt_encoding.instructions.push_basic import PushBasic
from smt_encoding.instructions.store_uninterpreted import StoreUninterpreted
from smt_encoding.instructions.swapk_basic import SwapKBasic
from smt_encoding.instructions.uninterpreted_instruction import UninterpretedInstruction, Instruction_JSON_T
from smt_encoding.instructions.basic_instruction import BasicInstruction


class InstructionFactory:

    def __init__(self):
        self._next_theta_value = 0
        self._instructions_ids = {}

    def create_instruction_json_format(self, json_instr: Instruction_JSON_T) -> UninterpretedInstruction:
        instr_id = json_instr["id"]

        # If it was already created, then we return the previous instance, as two instructions
        # cannot share the same name in our encoding
        if instr_id in self._instructions_ids:
            return self._instructions_ids[instr_id]

        if json_instr["storage"]:
            instance = StoreUninterpreted(json_instr, self._next_theta_value)
        elif json_instr["id"].startswith("POP"):
            instance = PopUninterpreted(json_instr, self._next_theta_value)
        elif json_instr["commutative"]:
            instance = CommutativeUninterpreted(json_instr, self._next_theta_value)
        else:
            instance = NonCommutativeUninterpreted(json_instr, self._next_theta_value)

        # The instruction was recognized, thus, we need to update theta and store the corresponding instance
        self._instructions_ids[instr_id] = instance
        self._next_theta_value += 1
        return instance

    # Given a name that identifies a basic stack operation, returns the corresponding EncodingInstruction object.
    def create_instruction_name(self, name : str) -> BasicInstruction:

        # If it was already created, then we return the previous instance, as two instructions
        # cannot share the same name in our encoding
        if name in self._instructions_ids:
            return self._instructions_ids[name]

        if name == "PUSH":
            instance = PushBasic(self._next_theta_value)
        elif name == "POP":
            instance = PopBasic(self._next_theta_value)
        elif name == "NOP":
            instance = NopBasic(self._next_theta_value)
        else:
            swap_match = re.fullmatch("SWAP([0-9]+)", name)
            dup_match = re.fullmatch("DUP([0-9]+)", name)

            if swap_match is not None:
                k = int(swap_match.group(1))
                instance = SwapKBasic(self._next_theta_value, k)
            elif dup_match is not None:
                k = int(dup_match.group(1))
                instance = DupKBasic(self._next_theta_value, k)
            else:
                raise ValueError(name + " instruction not recognized")

        # The instruction was recognized, thus, we need to update theta and store the corresponding instance
        self._instructions_ids[name] = instance
        self._next_theta_value += 1
        return instance

