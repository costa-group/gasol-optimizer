from typing import Dict, Optional, Union
import sfs_generator.opcodes as opcodes
from sfs_generator.utils import get_ins_size, get_push_number_hex
import global_params.constants as constants

# Assuming the value of asm is hexadecimal base. This way, we ensure the same format is respected
ASM_Value_T = Optional[str]

# Type the jumpType field can contain. Expected to be the same as ASM_Value_T
ASM_Jump_T = Optional[str]

# Type for the json representation of the assembly item
ASM_Json_T = Dict[str, Union[int, str, ASM_Value_T]]


def is_push0(disasm: str, value: str) -> bool:
    """
    We need to check push0 separately because we need to consider it depending on constants.push0_enabled
    """
    return constants.push0_enabled and disasm == "PUSH" and value == "0"


class AsmBytecode:
    """
    Class that represents the assembly format of the bytecode, following the same convention as the Solidity compiler
    """

    def __init__(self, begin: int, end: int, source: int, disasm: str, value: ASM_Value_T,
                 jump_type: ASM_Jump_T = None, modifier_depth: Optional[int] = None, real_value: ASM_Value_T = None):
        self.begin = begin
        self.end = end
        self.source = source
        self.disasm = disasm
        self.value = value
        self.jump_type = jump_type
        self.modifier_depth = modifier_depth
        self.real_value = real_value if real_value is not None else value

    def to_json(self)-> ASM_Json_T :
        """
        Assembly item conversion to json form
        :return: a dictionary with the different fields as keys and their corresponding values
        """

        json_bytecode = {"begin": self.begin, "end": self.end, "name": self.disasm, "source": self.source}

        if self.value is not None:
            # Substitute by the real value (for push instructions with no numeric value)
            json_bytecode["value"] = self.real_value

        if self.jump_type is not None:
            json_bytecode["jumpType"] = self.jump_type

        if self.modifier_depth is not None:
            json_bytecode["modifierDepth"] = self.modifier_depth

        return json_bytecode

    def to_plain(self) -> str:
        """
        Assembly item conversion to human-readable format. This format consists of the opcode name followed
        by the corresponding value or jump Type in hexadecimal if any
        :return: a string containing the representation
        """
        if is_push0(self.disasm, self.value):
            return "PUSH0"
        return f"{self.disasm} {str(self.value)}" if self.value is not None and "JUMP" not in self.disasm else self.disasm

    def to_plain_with_byte_number(self) -> str:
        if is_push0(self.disasm, self.value):
            return "PUSH0"

        op_name = ''.join([self.disasm, str(get_push_number_hex(self.value))]) if self.disasm == "PUSH" else self.disasm
        op_value = ''.join(['0x', self.value]) if self.disasm == "PUSH" else str(self.value) if self.value is not None else ''
        return f"{op_name} {op_value}" if self.value is not None and self.disasm == "PUSH" else f"{self.disasm} {self.jump_type}" \
            if self.jump_type is not None else self.disasm

    def to_plain_abstracted(self, value_dict: Dict) -> str:
        if is_push0(self.disasm, self.real_value):
            return "PUSH0"

        op_name = ''.join([self.disasm, str(get_push_number_hex(self.real_value))]) if self.disasm == "PUSH" else self.disasm

        op_value = ''.join(['0x', self.real_value]) if self.disasm == "PUSH" \
            else value_dict.get(self.real_value, str(self.real_value)) if self.value is not None else ''

        return f"{op_name} {op_value}" if self.value is not None else f"{self.disasm}" \
            if self.jump_type is not None else self.disasm


    @property
    def bytes_required(self) -> int:
        if is_push0(self.disasm, self.value):
            return 1
        elif self.disasm == "PUSH":
            decimal_value = int(self.value, 16)
        else:
            decimal_value = None
        return get_ins_size(self.disasm, decimal_value)

    @property
    def gas_spent(self) -> int:
        # Special case: if PUSH0 opcode is allowed, we need to measure the gas spent for PUSH 0 as PUSH0
        if is_push0(self.disasm, self.value):
            return 2
        return opcodes.get_ins_cost(self.disasm, self.value)

    def gas_spent_accesses(self, warm_access: bool, store_changed_original_value: bool) -> int:
        if is_push0(self.disasm, self.value):
            return 2
        return opcodes.get_ins_cost(self.disasm, self.value, already=warm_access)

    def get_disasm(self) -> str:
        return self.disasm
    
    def get_value(self) -> int:
        return self.value
    
    
    def __str__(self):
        return f"{{begin:{str(self.begin)}, end:{str(self.end)}, source:{str(self.source)}, name:{self.disasm}, value:{str(self.value)}, real_value:{str(self.real_value)}, jumpType:{self.jump_type}}}"


    def __repr__(self):
        return f"{{begin:{str(self.begin)}, end:{str(self.end)}, source:{str(self.source)}, name:{self.disasm}, value:{str(self.value)}, real_value:{str(self.real_value)}, jumpType:{str(self.jump_type)}}}"


    def __eq__(self, other):
        return self.begin == other.begin and self.end == other.end and self.source == other.source and \
               self.disasm == other.disasm and self.value == other.value and self.jump_type == other.jump_type
