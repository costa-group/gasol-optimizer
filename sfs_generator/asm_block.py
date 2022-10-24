import global_params.constants as constants
import sfs_generator.opcodes as opcodes
import sfs_generator.utils as utils
from sfs_generator.asm_bytecode import AsmBytecode, ASM_Json_T
from typing import List, Union

# Blocks are identified using an int
Block_id_T = int

# Jump types identified as strings (maybe in the future use enum)
Jump_Type_T = str

class AsmBlock:
    """
    Class for representing an Assembly block
    """
    
    def __init__(self, cname : str, identifier : Block_id_T, name : str, is_init_block : bool):
        self.contract_name = cname
        self.block_id = identifier
        self.block_name = name
        self._instructions = []
        # minimum size of the source stack
        self.source_stack = 0
        self.is_init_block = is_init_block
        self._jump_type = None
        self._jump_to = None
        self._falls_to = None
        self._tag = -1

    @property
    def instructions(self) -> List[AsmBytecode]:
        return self._instructions

    @instructions.setter
    def instructions(self, new_instructions : List[AsmBytecode]) -> None:
        # First, we update the new set of instructions
        self._instructions = new_instructions

        # Then we update the source stack size
        self.source_stack = utils.compute_stack_size(map(lambda x: x.disasm, self.instructions_to_optimize_bytecode()))

    def add_instruction(self, bytecode : AsmBytecode) -> None:
        self._instructions.append(bytecode)

        # If an instruction is added, we need to update the source stack counter
        self.source_stack = utils.compute_stack_size(map(lambda x: x.disasm, self.instructions_to_optimize_bytecode()))

    @property
    def jump_type(self) -> Jump_Type_T:
        return self._jump_type

    @jump_type.setter
    def jump_type(self, t : Jump_Type_T) -> None:
        if t not in ["conditional","unconditional","terminal", "falls_to"]:
            raise Exception("Wrong jump type")
        else:
            self._jump_type = t

    @property
    def tag(self) -> int:
        '''
        It contains the value of the corresponding tag
        '''
        return self._tag

    @tag.setter
    def tag(self, t : int) -> None:
        self._tag = t

    @property
    def jump_to(self) -> int:
        return self._jump_to

    @jump_to.setter
    def jump_to(self, blockId : int) -> None:
        self._jump_to = blockId

    @property
    def falls_to(self) -> int:
        return self._falls_to

    @falls_to.setter
    def falls_to(self, blockId : int) -> None:
        self._falls_to = blockId

    def set_types(self) -> None:
        """
        Set the jump type matching the last instruction in the block
        :return: None
        """
        last_instruction = self.instructions[-1].disasm
        if last_instruction == "JUMP":
            self.jump_type = "unconditional"
        elif last_instruction == "JUMPI":
            self.jump_type = "conditional"
        elif last_instruction in ["INVALID","REVERT","STOP","RETURN","SUICIDE"]:
            self.jump_type = "terminal"
        else:
            self.jump_type = "falls_to"

    def to_json(self) -> [ASM_Json_T]:
        return list(map(lambda instr: instr.to_json(), self.instructions))


    def to_plain(self) -> str:
        return ' '.join(map(lambda instr: instr.to_plain(), self.instructions))

    def to_plain_with_byte_number(self) -> str:
        return ' '.join(map(lambda instr: instr.to_plain_with_byte_number(), self.instructions))

    def __str__(self):
        content = ""
        content += "Block Id:"+str(self.block_id)+"\n"
        for i in self.instructions:
            content += str(i)+"\n"

        content+=str(self.source_stack)
        return content

    def __repr__(self):
        content = ""
        content += "Block Id:"+str(self.block_id)+"\n"
        for i in self.instructions:
            content += str(i)+"\n"

        content+=str(self.source_stack)
        return content

    def instructions_to_optimize_plain(self) -> List[str]:
        return [instruction.to_plain() for instruction in self.instructions_to_optimize_bytecode()]

    def instructions_to_optimize_bytecode(self) -> List[AsmBytecode]:
        return [instruction for instruction in self.instructions
                if instruction.disasm not in constants.beginning_block and instruction.disasm not in constants.end_block]

    def instructions_initial_bytecode(self) -> List[AsmBytecode]:
        return [instruction for instruction in self.instructions if instruction.disasm in constants.beginning_block]

    def instructions_initial_plain(self) -> List[str]:
        return [instruction.to_plain() for instruction in self.instructions_initial_bytecode()]

    def instructions_final_bytecode(self) -> List[AsmBytecode]:
        return [instruction for instruction in self.instructions if instruction.disasm in constants.end_block]

    def instructions_final_plain(self) -> List[str]:
        return [instruction.to_plain() for instruction in self.instructions_final_bytecode()]


    @property
    def bytes_required(self) -> int:
        return sum([instruction.bytes_required for instruction in self.instructions])

    @property
    def gas_spent(self) -> int:
        return sum([instruction.gas_spent for instruction in self.instructions])

    def get_contract_name(self):
        return self.contract_name

    def get_block_id(self):
        return self.block_id

    def set_block_id(self, identifier):
        self.block_id = identifier
        
    def get_block_name(self):
        return self.block_name

    def set_block_name(self,block_name):
        self.block_name = block_name
