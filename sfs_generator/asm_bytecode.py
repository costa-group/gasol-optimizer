from typing import Dict, Optional, Union
import sfs_generator.opcodes as opcodes
from sfs_generator.utils import get_ins_size, get_push_number_hex

# Assuming the value of asm is hexadecimal base. This way, we ensure the same format is respected
ASM_Value_T = Optional[str]

# Type the jumpType field can contain. Expected to be the same as ASM_Value_T
ASM_Jump_T = Optional[str]

# Type for the json representation of the assembly item
ASM_Json_T = Dict[str, Union[int, str, ASM_Value_T]]

class AsmBytecode:
    """
    Class that represents the assembly format of the bytecode, following the same convention as the Solidity compiler
    """

    def __init__(self, begin: int, end: int, source: int, disasm: str, value: ASM_Value_T, jump_type: ASM_Jump_T = None):
        self.begin = begin
        self.end = end
        self.source = source
        self.disasm = disasm
        self.value = value
        self.jump_type = jump_type

    def to_json(self)-> ASM_Json_T :
        """
        Assembly item conversion to json form
        :return: a dictionary with the different fields as keys and their corresponding values
        """

        json_bytecode = {"begin": self.begin, "end": self.end, "name": self.disasm, "source": self.source}

        if self.value is not None:
            json_bytecode["value"] = self.value

        if self.jump_type is not None:
            json_bytecode["jumpType"] = self.jump_type

        return json_bytecode

    def to_plain(self) -> str:
        """
        Assembly item conversion to human-readable format. This format consists of the opcode name followed
        by the corresponding value or jump Type in hexadecimal if any
        :return: a string containing the representation
        """
        return f"{self.disasm} {str(self.value)}" if self.value is not None and self.disasm == "PUSH" else f"{self.disasm} {self.jump_type}" \
            if self.jump_type is not None else self.disasm

    def to_plain_with_byte_number(self) -> str:
        op_name = ''.join([self.disasm, str(get_push_number_hex(self.value))]) if self.disasm == "PUSH" else self.disasm
        op_value = ''.join(['0x', self.value]) if self.disasm == "PUSH" else str(self.value) if self.value is not None else ''
        return f"{op_name} {op_value}" if self.value is not None and self.disasm == "PUSH" else f"{self.disasm} {self.jump_type}" \
            if self.jump_type is not None else self.disasm

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

    def gas_spent_accesses(self, warm_access: bool, store_changed_original_value: bool) -> int:
        return opcodes.get_ins_cost(self.disasm, self.value, already=warm_access)

    def get_disasm(self) -> str:
        return self.disasm
    
    def get_value(self) -> int:
        return self.value
    
    
    def __str__(self):
        return f"{{begin:{str(self.begin)}, end:{str(self.end)}, source:{str(self.source)}, name:{self.disasm}, value:{str(self.value)}, jumpType:{self.jump_type}}}"


    def __repr__(self):
        return f"{{begin:{str(self.begin)}, end:{str(self.end)}, source:{str(self.source)}, name:{self.disasm}, value:{str(self.value)}, jumpType:{str(self.jump_type)}}}"


    def __eq__(self, other):
        return self.begin == other.begin and self.end == other.end and self.source == other.source and \
               self.disasm == other.disasm and self.value == other.value and self.jump_type == other.jump_type
