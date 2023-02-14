from smt_encoding.instructions.basic_instruction import BasicInstruction


class PushBasic(BasicInstruction):

    def __init__(self, theta_value):
        self._theta_value = theta_value

    @property
    def theta_value(self):
        return self._theta_value

    @property
    def id(self):
        return "PUSH"

    @property
    def opcode_name(self):
        return "PUSH"

    @property
    def size_cost(self):
        return 5

    @property
    def gas_cost(self):
        return 3
