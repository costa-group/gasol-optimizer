from smt_encoding.instructions.encoding_instruction import InstructionSubset
from smt_encoding.instructions.uninterpreted_instruction import UninterpretedInstruction


class StoreUninterpreted(UninterpretedInstruction):

    def __init__(self, sfs_instr, theta_value):
        super().__init__(sfs_instr, theta_value)

    @property
    def instruction_subset(self) -> InstructionSubset:
        return InstructionSubset.store
