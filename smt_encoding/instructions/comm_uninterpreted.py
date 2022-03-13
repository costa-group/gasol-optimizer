from smt_encoding.instructions.uninterpreted_instruction import UninterpretedFunction, SMS_T
from smt_encoding.instructions.encoding_instruction import InstructionSubset

class CommutativeUninterpreted(UninterpretedFunction):

    def __init__(self, sfs_instr : SMS_T, theta_value : int, var_initial_idx : int = 0):
        super().__init__(sfs_instr, theta_value, var_initial_idx)
        self.commutative = True

    # Statement it belongs to basic instructions
    @property
    def instruction_subset(self) -> InstructionSubset:
        return InstructionSubset.comm
