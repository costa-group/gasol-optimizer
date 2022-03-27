import global_params.constants as constants
from smt_encoding.instructions.basic_instruction import BasicInstruction


class DupKBasic(BasicInstruction):

    def __init__(self, theta_value : int, k : int):
        assert 1 <= k <= constants.max_k_dup
        self._k = k
        self._theta_value = theta_value


    @property
    def theta_value(self) -> int:
        return self._theta_value

    @property
    def id(self) -> str:
        return "DUP" + str(self._k)

    @property
    def opcode_name(self) -> str:
        return "DUP" + str(self._k)

    @property
    def size_cost(self) -> int:
        return 1

    @property
    def gas_cost(self) -> int:
        return 3
