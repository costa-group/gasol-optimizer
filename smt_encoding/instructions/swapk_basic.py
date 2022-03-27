import global_params.constants as constants
from smt_encoding.instructions.basic_instruction import BasicInstruction
from smt_encoding.instructions.encoding_instruction import ThetaValue


class SwapKBasic(BasicInstruction):

    def __init__(self, theta_value : ThetaValue, k: int):
        assert 1 <= k <= constants.max_k_swap
        self._k = k
        self._theta_value = theta_value

    @property
    def theta_value(self):
        return self._theta_value


    @property
    def id(self):
        return "SWAP" + str(self._k)


    @property
    def opcode_name(self):
        return "SWAP" + str(self._k)


    @property
    def size_cost(self):
        return 1


    @property
    def gas_cost(self):
        return 3
