from abc import ABC

from smt_encoding.instructions.encoding_instruction import EncodingInstruction, ThetaValue, Id_T, Stack_Var_T
from typing import Dict, Any, Optional, List, Union

Instruction_JSON_T = Dict[str, Any]


class UninterpretedInstruction(EncodingInstruction, ABC):

    def __init__(self, instr: Instruction_JSON_T, theta_value: ThetaValue):
        self._output_stack = instr['outpt_sk']
        self._input_stack = instr['inpt_sk']
        self._gas = instr["gas"]
        self._name = instr["disasm"]
        self._hex = instr["opcode"]
        self._id = instr["id"]
        self._size = instr["size"]
        # Value field may not appear in the instruction representation
        self._value = instr.get('value', None)
        self._theta_value = theta_value

    # An uninterpreted function is assumed to appear once in the sequence iff it does not consume
    # any other element
    @property
    def unique_ui(self) -> bool:
        return len(self._input_stack) > 0

    @property
    def theta_value(self) -> ThetaValue:
        return self._theta_value

    @property
    def id(self) -> Id_T:
        return self._id

    @property
    def opcode_name(self) -> str:
        return self._name

    # If an instruction only appears once in the code, then we do not need to take into account in the soft constraints
    # Thus, none gas cost is returned.
    @property
    def gas_cost(self) -> int:
        return self._gas

    @property
    def size_cost(self) -> int:
        return self._size

    @property
    def input_stack(self) -> List[Stack_Var_T]:
        return self._input_stack

    @property
    def output_stack(self) -> Optional[str]:
        if not self._output_stack:
            return None
        return self._output_stack[0]

    @property
    def value(self) -> Optional[int]:
        if self._value is not None:
            return self._value[0]
        return self._value
