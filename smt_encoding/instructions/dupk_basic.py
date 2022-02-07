import global_params.constants as constants
from smt_encoding.instructions.basic_instruction import BasicInstruction
from smt_encoding.constraints.assertions import Assert
from smt_encoding.constraints.connector_factory import add_eq, add_and, add_implies, add_not
from smt_encoding.complete_encoding.synthesis_variables import u, x, t
from smt_encoding.complete_encoding.synthesis_predicates import move

def dupk_encoding(k : int, j : int, bs : int, theta_dupk : int) -> Assert:
    left_term = add_eq(t(j), theta_dupk)
    right_term = add_and(add_not(u(bs-1, j)), u(k-1, j), u(0, j+1),
                          add_eq(x(0, j+1), x(k-1, j)), move(j, 0, bs-2, 1))
    return Assert(add_implies(left_term, right_term))


class DupKBasic(BasicInstruction):

    def __init__(self, theta_value : int, k : int, initial_idx : int = 0):
        assert 0 <= k <= constants.max_k_dup
        self._k = k
        self._theta_value = theta_value
        self.initial_idx = initial_idx

    def encoding_instruction(self, **kwargs) -> Assert:
        bs = kwargs["bs"]
        j = kwargs["j"]

        return dupk_encoding(self._k, j, bs, self.theta_value)

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
