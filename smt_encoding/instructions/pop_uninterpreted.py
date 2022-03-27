from smt_encoding.encoding_stack_instructions import pop_uninterpreted_encoding
from smt_encoding.instructions.encoding_instruction import InstructionSubset
from smt_encoding.instructions.uninterpreted_instruction import UninterpretedInstruction


class PopUninterpreted(UninterpretedInstruction):

    def __init__(self, sfs_instr, theta_value):
        super().__init__(sfs_instr, theta_value)
        self.commutative = False

    @property
    def instruction_subset(self) -> InstructionSubset:
        return InstructionSubset.basic