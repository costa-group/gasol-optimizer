from typing import Dict, Optional, Union
import sfs_generator.opcodes as opcodes

# Assuming the value of asm is hexadecimal base. This way, we ensure the same format is respected
ASM_Value_T = Optional[str]

# Type for the json representation of the assembly item
ASM_Json_T = Dict[str, Union[int, str, ASM_Value_T]]

class AsmBytecode:
    """
    Class that represents the assembly format of the bytecode, following the same convention as the Solidity compiler
    """

    def __init__(self, begin: int, end: int, source : int, disasm: str, value: ASM_Value_T):
        self.begin = begin
        self.end = end
        self.source = source
        self.disasm = disasm
        self.value = value

    def to_json(self)-> ASM_Json_T :
        """
        Assembly item conversion to json form
        :return: a dictionary with the different fields as keys and their corresponding values
        """

        json_bytecode = {"begin": self.begin, "end": self.end, "name": self.disasm, "source": self.source}

        if self.value is not None:
            json_bytecode["value"] = self.value

        return json_bytecode

    def to_plain(self) -> str:
        """
        Assembly item conversion to human-readable format. This format consists of the opcode name followed
        by the corresponding value in hexadecimal if any
        :return: a string containing the representation
        """
        return self.disasm if self.value is None else ' '.join([self.disasm, self.value])


    def __str__(self):
        content = "{begin:"+str(self.begin)+", end:"+str(self.end)+", source:"+str(self.source)+", name:"+str(self.disasm)+", value:"+str(self.value)+"}"
        return content


    def __repr__(self):
        content = "{begin:"+str(self.begin)+", end:"+str(self.end)+", source:"+str(self.source)+", name:"+str(self.disasm)+", value:"+str(self.value)+"}"
        return content


    def __eq__(self, other):
        return self.begin == other.begin and self.end == other.end and self.source == other.source and \
               self.disasm == other.disasm and self.value == other.value
