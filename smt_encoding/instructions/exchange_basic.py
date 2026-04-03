import global_params.constants as constants
from smt_encoding.instructions.basic_instruction import BasicInstruction
from smt_encoding.instructions.encoding_instruction import ThetaValue


class ExchangeBasic(BasicInstruction):

    def __init__(self, theta_value : ThetaValue, n: int, m: int):
        assert 1 <= n <= 13
        assert n < m <= 29
        assert n + m <= 30
        self._n = n
        self._m = m
        self._theta_value = theta_value

    @property
    def theta_value(self):
        return self._theta_value


    @property
    def id(self):
        return "EXCHANGE " + str(self._n) + ' ' + str(self._m)


    @property
    def opcode_name(self):
        return "EXCHANGE " + str(self._n) + ' ' + str(self._m)


    @property
    def size_cost(self):
        return 2


    @property
    def gas_cost(self):
        return 3

    @property
    def n(self) -> int:
        return self._n
    
    @property
    def m(self) -> int:
        return self._m
