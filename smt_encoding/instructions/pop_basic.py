from smt_encoding.encoding_stack_instructions import pop_encoding
from smt_encoding.instructions.basic_instruction import BasicInstruction


class PopBasic(BasicInstruction):

    def __init__(self, theta_value):
        self._theta_value = theta_value

    @property
    def theta_value(self):
        return self._theta_value

    @property
    def id(self):
        return "POP"

    @property
    def opcode_name(self):
        return "POP"

    @property
    def size_cost(self):
        return 1

    @property
    def gas_cost(self):
        return 2
