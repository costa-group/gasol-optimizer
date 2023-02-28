from smt_encoding.instructions.encoding_instruction import ThetaValue
from smt_encoding.instructions.instruction_bounds import InstructionBounds

class DumbInstructionBounds(InstructionBounds):
    """
    Instruction bounds in which all instructions share the same bounds
    """

    def __init__(self, lb : int, ub : int):
        self._lb = lb
        self._ub = ub

    def upper_bound_theta_value(self, theta_value: ThetaValue) -> int:
        return self._ub

    def lower_bound_theta_value(self, theta_value: ThetaValue) -> int:
        return self._lb

    @property
    def first_position_sequence(self) -> int:
        return self._lb

    @property
    def last_position_sequence(self) -> int:
        return self._ub
