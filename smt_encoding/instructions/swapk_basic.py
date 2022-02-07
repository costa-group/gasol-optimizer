import global_params.constants as constants
from smt_encoding.encoding_stack_instructions import swapk_encoding
from smt_encoding.instructions.basic_instruction import BasicInstruction


class SwapKBasic(BasicInstruction):

    def __init__(self, theta_value, k, initial_idx = 0):
        assert 0 <= k <= constants.max_k_swap
        self._k = k
        self._theta_value = theta_value
        self.initial_idx = initial_idx


    def encoding_instruction(self, **kwargs):
        bs = kwargs["bs"]
        j = kwargs['j']

        return swapk_encoding(self._k, j, bs, self.theta_value)


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
