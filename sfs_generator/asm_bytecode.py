from typing import Dict, Optional, Union
import sfs_generator.opcodes as opcodes
from sfs_generator.utils import get_ins_size, get_push_number_hex

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
        return self.disasm if self.value is None else ' '.join([self.disasm, str(self.value)])

    def to_plain_with_byte_number(self) -> str:
        op_name = ''.join([self.disasm, str(get_push_number_hex(self.value))]) if self.disasm == "PUSH" else self.disasm
        op_value = ''.join(['0x', self.value]) if self.disasm == "PUSH" else str(self.value) if self.value is not None else ''
        return ' '.join([op_name, op_value]) if self.value is not None else op_name

    @property
    def bytes_required(self) -> int:
        if self.disasm == "PUSH":
            decimal_value = int(self.value, 16)
        else:
            decimal_value = None
        return get_ins_size(self.disasm, decimal_value)

    @property
    def gas_spent(self) -> int:
        return opcodes.get_ins_cost(self.disasm, self.value)


    def __str__(self):
        content = "{begin:"+str(self.begin)+", end:"+str(self.end)+", source:"+str(self.source)+", name:"+str(self.disasm)+", value:"+str(self.value)+"}"
        return content


    def __repr__(self):
        content = "{begin:"+str(self.begin)+", end:"+str(self.end)+", source:"+str(self.source)+", name:"+str(self.disasm)+", value:"+str(self.value)+"}"
        return content


    def __eq__(self, other):
        return self.begin == other.begin and self.end == other.end and self.source == other.source and \
               self.disasm == other.disasm and self.value == other.value
