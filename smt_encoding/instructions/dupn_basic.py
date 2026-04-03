import global_params.constants as constants
from smt_encoding.instructions.basic_instruction import BasicInstruction


class DupNBasic(BasicInstruction):

    def __init__(self, theta_value : int, n : int):
        assert constants.max_k_dup <= n <= 235
        self._n = n
        self._theta_value = theta_value


    @property
    def theta_value(self) -> int:
        return self._theta_value

    @property
    def id(self) -> str:
        return "DUPN" + str(self._n)

    @property
    def opcode_name(self) -> str:
        return "DUPN" + str(self._n)

    @property
    def size_cost(self) -> int:
        return 2

    @property
    def gas_cost(self) -> int:
        return 3

    @property
    def k(self) -> int:
        return self._n
