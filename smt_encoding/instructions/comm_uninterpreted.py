from smt_encoding.instructions.uninterpreted_instruction import UninterpretedFunction, SMS_T
from smt_encoding.constraints.assertions import Assert
from smt_encoding.constraints.connector_factory import add_eq, add_and, add_implies, add_not, add_or
from smt_encoding.complete_encoding.synthesis_predicates import move
from smt_encoding.instructions.encoding_instruction import InstructionSubset

class CommutativeUninterpreted(UninterpretedFunction):

    def __init__(self, sfs_instr : SMS_T, theta_value : int, var_initial_idx : int = 0):
        super().__init__(sfs_instr, theta_value, var_initial_idx)
        self.commutative = True

    # Statement it belongs to basic instructions
    @property
    def instruction_subset(self) -> InstructionSubset:
        return InstructionSubset.comm
