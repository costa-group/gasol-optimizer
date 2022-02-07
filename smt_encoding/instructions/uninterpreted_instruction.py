from abc import ABC

from smt_encoding.instructions.encoding_instruction import EncodingInstruction
from smt_encoding.utils_bckend import add_bars_and_index_to_string
from typing import Dict, Any, Optional

SMS_T = Dict[str, Any]

class UninterpretedFunction(EncodingInstruction, ABC):


    def __init__(self, instr : SMS_T, theta_value : int, var_initial_idx : int = 0):
        self._output_stack = instr['outpt_sk']
        self._input_stack = instr['inpt_sk']
        self._gas = instr["inpt_sk"]
        self._name = instr["disasm"]
        self._hex = instr["opcode"]
        self._id = instr["id"]
        self._theta_value = theta_value
        self._initial_idx = var_initial_idx


    # An uninterpreted function is assumed to appear once in the sequence iff it does not consume
    # any other element
    @property
    def unique_ui(self) -> bool:
        return len(self.input_stack) > 0

    @property
    def theta_value(self) -> int:
        return self._theta_value

    @property
    def id(self) -> str:
        return self._id

    @property
    def opcode_name(self) -> str:
        return self.name

    # If an instruction only appears once in the code, then we do not need to take into account in the soft constraints
    # Thus, none gas cost is returned.
    @property
    def gas_cost(self) -> Optional[int]:
        if self.unique_ui:
            return None
        else:
            return self.gas

    @property
    def size_cost(self) -> Optional[int]:
        if self.unique_ui:
            return None
        elif self.name.startswith("PUSH"):
            return 5
        else:
            return 1
