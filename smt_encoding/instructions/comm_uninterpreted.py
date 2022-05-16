from smt_encoding.instructions.uninterpreted_instruction import UninterpretedInstruction, Instruction_JSON_T
from smt_encoding.instructions.encoding_instruction import InstructionSubset

class CommutativeUninterpreted(UninterpretedInstruction):

    def __init__(self, sfs_instr : Instruction_JSON_T, theta_value : int):
        super().__init__(sfs_instr, theta_value)
        self.commutative = True

    # Statement it belongs to basic instructions
    @property
    def instruction_subset(self) -> InstructionSubset:
        return InstructionSubset.comm
