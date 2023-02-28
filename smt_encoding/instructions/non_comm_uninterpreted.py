from smt_encoding.instructions.uninterpreted_instruction import UninterpretedInstruction
from smt_encoding.instructions.encoding_instruction import InstructionSubset

class NonCommutativeUninterpreted(UninterpretedInstruction):

    def __init__(self, sfs_instr, theta_value):
        super().__init__(sfs_instr, theta_value)


    # Statement it belongs to basic instructions
    @property
    def instruction_subset(self):
        return InstructionSubset.non_comm
