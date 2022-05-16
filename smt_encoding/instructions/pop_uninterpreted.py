from smt_encoding.instructions.encoding_instruction import InstructionSubset
from smt_encoding.instructions.uninterpreted_instruction import UninterpretedInstruction, Instruction_JSON_T, ThetaValue


class PopUninterpreted(UninterpretedInstruction):

    def __init__(self, sfs_instr: Instruction_JSON_T, theta_value: ThetaValue):
        super().__init__(sfs_instr, theta_value)
        self.commutative = False

    @property
    def instruction_subset(self) -> InstructionSubset:
        return InstructionSubset.pop
