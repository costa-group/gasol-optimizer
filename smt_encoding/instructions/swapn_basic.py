import global_params.constants as constants
from smt_encoding.instructions.basic_instruction import BasicInstruction
from smt_encoding.instructions.encoding_instruction import ThetaValue


class SwapNBasic(BasicInstruction):

    def __init__(self, theta_value : ThetaValue, n: int):
        assert constants.max_k_swap <= n <= 235
        self._n = n
        self._theta_value = theta_value

    @property
    def theta_value(self):
        return self._theta_value


    @property
    def id(self):
        return "SWAPN" + str(self._n)


    @property
    def opcode_name(self):
        return "SWAPN" + str(self._n)


    @property
    def size_cost(self):
        return 2


    @property
    def gas_cost(self):
        return 3

    @property
    def k(self) -> int:
        return self._n
