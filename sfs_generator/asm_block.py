import global_params.constants as constants
import sfs_generator.opcodes as opcodes
import sfs_generator.utils as utils
from sfs_generator.asm_bytecode import AsmBytecode, ASM_Json_T
from typing import List, Union

# Blocks are identified using an int
Block_id_T = int

# Jump types identified as strings (maybe in the future use enum)
Jump_Type_T = str


def execute_asm(current_stack: List[str], asm_bytecode: AsmBytecode) -> List[str]:
    instr_name = asm_bytecode.disasm
    if instr_name == "PUSH":
        current_stack.insert(0, str(int(asm_bytecode.value, 16)))
    elif instr_name.startswith("SWAP"):
        index = int(instr_name[4:])
        current_stack[0], current_stack[index] = current_stack[index], current_stack[0]
    elif instr_name.startswith("DUP"):
        index = int(instr_name[3:])
        current_stack.insert(0, current_stack[index - 1])
    elif instr_name == "POP":
        current_stack.pop(0)
    else:
        opcode_info = opcodes.get_opcode(instr_name)
        operands = []
        for _ in range(opcode_info[1]):
            operands.append(current_stack[0])
            current_stack.pop(0)
        joined_operands = ','.join(operands)
        if opcode_info[2] == 0:
            pass
        elif instr_name == "KECCAK256":
            pass
            current_stack.insert(0, f'{instr_name}({joined_operands})')
        elif operands == []:
            current_stack.insert(0, asm_bytecode.to_plain())
        else:
            joined_operands = ','.join(operands)
            current_stack.insert(0, f'{instr_name}({joined_operands})')
    return current_stack


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
        return ' '.join((instr.to_plain() for instr in self.instructions if instr.disasm != "tag"))

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
        stack_size = utils.compute_stack_size(map(lambda x: x.disasm, self.instructions))
        current_stack = [f's({i})' for i in range(stack_size)]
        total_gas = 0
        touched_addresses, touched_slots, touched_slots_store = set(), set(), set()
        for instruction in self.instructions:
            stack_top = current_stack[0] if len(current_stack) > 0 else None
            if instruction.disasm == "SLOAD":
                assert stack_top is not None
                # print(instruction.gas_spent_accesses(stack_top in touched_slots, stack_top in touched_slots_store))
                # print(instruction.disasm, stack_top)
                total_gas += instruction.gas_spent_accesses(stack_top in touched_slots, False)
                touched_slots.add(stack_top)
            elif instruction.disasm == "SSTORE":
                assert stack_top is not None
                total_gas += instruction.gas_spent_accesses(stack_top in touched_slots, stack_top in touched_slots_store)
                # print(instruction.gas_spent_accesses(stack_top in touched_slots, stack_top in touched_slots_store))
                # print(instruction.disasm, stack_top)
                touched_slots.add(stack_top)
                touched_slots_store.add(stack_top)
            elif instruction.disasm in ("BALANCE","EXTCODESIZE","EXTCODEHASH", "EXTCODECOPY"):
                assert stack_top is not None
                total_gas += instruction.gas_spent_accesses(stack_top in touched_addresses, False)
                # print(instruction.gas_spent_accesses(stack_top in touched_slots, stack_top in touched_slots_store))
                # print(instruction.disasm, stack_top)
                touched_addresses.add(stack_top)
            else:
                total_gas += instruction.gas_spent

            # Update stack
            current_stack = execute_asm(current_stack, instruction)
        # if len(touched_slots) > 0 or len(touched_addresses) > 0:
        #     print("Block", self.block_id)
        return total_gas

    def gas_spent_by_storage(self) -> int:
        stack_size = utils.compute_stack_size(map(lambda x: x.disasm, self.instructions))
        current_stack = [f's({i})' for i in range(stack_size)]
        total_gas = 0
        touched_addresses, touched_slots, touched_slots_store = set(), set(), set()
        for instruction in self.instructions:
            stack_top = current_stack[0] if len(current_stack) > 0 else None
            if instruction.disasm == "SLOAD":
                assert stack_top is not None
                # print(instruction.gas_spent_accesses(stack_top in touched_slots, stack_top in touched_slots_store))
                # print(instruction.disasm, stack_top)
                total_gas += instruction.gas_spent_accesses(stack_top in touched_slots, False)
                touched_slots.add(stack_top)
            elif instruction.disasm == "SSTORE":
                assert stack_top is not None
                total_gas += instruction.gas_spent_accesses(stack_top in touched_slots, stack_top in touched_slots_store)
                # print(instruction.gas_spent_accesses(stack_top in touched_slots, stack_top in touched_slots_store))
                # print(instruction.disasm, stack_top)
                touched_slots.add(stack_top)
                touched_slots_store.add(stack_top)
            # elif instruction.disasm in ("BALANCE","EXTCODESIZE","EXTCODEHASH", "EXTCODECOPY"):
            #     assert stack_top is not None
            #     #total_gas += instruction.gas_spent_accesses(stack_top in touched_addresses, False)
            #     # print(instruction.gas_spent_accesses(stack_top in touched_slots, stack_top in touched_slots_store))
            #     # print(instruction.disasm, stack_top)
            #     touched_addresses.add(stack_top)
            # else:
            #     total_gas += instruction.gas_spent

            # Update stack
            current_stack = execute_asm(current_stack, instruction)
        # if len(touched_slots) > 0 or len(touched_addresses) > 0:
        #     print("Block", self.block_id)
        return total_gas
    

    @property
    def length(self) -> int:
        return len([True for instruction in self.instructions if instruction.disasm != 'tag'])

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
