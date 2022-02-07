from abc import ABC

from smt_encoding.instructions.encoding_instruction import EncodingInstruction
from encoding_instruction import InstructionSubset

class BasicInstruction(EncodingInstruction, ABC):

    # A basic instruction can always happen multiple times
    @property
    def unique_ui(self) -> bool:
        return False

    # Statement it belongs to basic instructions
    @property
    def instruction_subset(self) -> InstructionSubset:
        return InstructionSubset.basic
