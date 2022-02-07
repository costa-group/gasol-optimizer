from smt_encoding.instructions.basic_instruction import BasicInstruction

class NopBasic(BasicInstruction):

    def __init__(self, theta_value, initial_idx=0):
        self._theta_value = theta_value
        self.initial_idx = initial_idx

    @property
    def theta_value(self):
        return self._theta_value

    @property
    def id(self):
        return "NOP"

    @property
    def opcode_name(self):
        return "NOP"

    @property
    def size_cost(self):
        return 0

    @property
    def gas_cost(self):
        return 0
