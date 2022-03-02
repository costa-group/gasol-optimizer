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
        self.jump_to = None
        self.falls_to = None

    @property
    def instructions(self) -> List[AsmBytecode]:
        return self._instructions

    @instructions.setter
    def instructions(self, new_instructions : List[AsmBytecode]) -> None:
        # First, we update the source stack size
        self.source_stack = utils.compute_stack_size(map(lambda x: x.disasm, new_instructions))

        # Then we update the new set of instructions
        self._instructions = new_instructions

    def add_instruction(self, bytecode : AsmBytecode) -> None:
        self._instructions.append(bytecode)

        # If an instruction is added, we need to update the source stack counter
        self.source_stack = utils.compute_stack_size(map(lambda x: x.disasm, self._instructions))

    @property
    def jump_type(self) -> Jump_Type_T:
        return self._jump_type

    @jump_type.setter
    def jump_type(self, t : Jump_Type_T) -> None:
        if t not in ["conditional","unconditional","terminal", "falls_to"]:
            raise Exception("Wrong jump type")
        else:
            self._jump_type = t

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


        
    def split_in_sub_blocks(self) -> [Union[List[AsmBytecode], AsmBytecode]]:
        """
        Split the block in a list of asm_bytecodes that contains either sub blocks or
        isolated instructions (JUMPs or split instructions).

        :return: a list with the split sub-blocks
        """
        sub_blocks = []
        current_sub_block = []
        for asm_bytecode in self.instructions:

            instruction = asm_bytecode.disasm

            # Three cases: either an instruction correspond to a jump/end or split instruction or neither of them.
            if instruction in ["JUMP","JUMPI","STOP","RETURN","REVERT","INVALID","JUMPDEST","tag"] \
                    or instruction in constants.split_block:
                if current_sub_block:
                    sub_blocks.append(current_sub_block)
                    current_sub_block = []

                # These instructions are isolated, so we introduce them directly in the list of sub blocks
                sub_blocks.append(asm_bytecode)
            else:
                current_sub_block.append(asm_bytecode)

        # If there is a sub block left, we need to add it to the list
        if current_sub_block:
            sub_blocks.append(current_sub_block)

        return sub_blocks

    def split_in_sub_blocks_partition(self, sub_block_list):
        sub_blocks = []
        current_sub_block = []
        current_sub_block_index = 0
        current_instruction_in_sub_block = 0
        initial_instructions = True
        pop_initial = True

        assembly_item_to_internal_representation = {v:k for k, v in opcodes.opcode_internal_representation_to_assembly_item.items()}
        for asm_bytecode in self.instructions:

            instruction = asm_bytecode.disasm
            # Representation that matches the one in the sub block list
            plain_representation = assembly_item_to_internal_representation.get(instruction, instruction)

            # Pops that appear at the beginning of a block that isn't the first one are simplified via
            # intra-block optimization (not always, for instance with LOG3 does not behave this way)
            if plain_representation == "POP" and pop_initial and not initial_instructions and \
                    len(sub_block_list[current_sub_block_index]) > current_instruction_in_sub_block and \
                    plain_representation != sub_block_list[current_sub_block_index][current_instruction_in_sub_block]:
                current_sub_block.append(asm_bytecode)
                continue

            # Three cases: either a instruction correspond to a jump/end or split instruction or neither of them.
            if instruction in ["JUMP","JUMPI","STOP","RETURN","REVERT","INVALID","JUMPDEST","tag"] \
                    or instruction in constants.split_block:

                # We append all instructions that do not conform a block
                if initial_instructions or current_sub_block_index >= len(sub_block_list):
                    sub_blocks.append(asm_bytecode)

                # We have already generated a complete block, so we update the values
                elif len(sub_block_list[current_sub_block_index]) - 1 == current_instruction_in_sub_block:
                    # assert (sub_block_list[current_sub_block_index][current_instruction_in_sub_block].startswith(
                    #     plain_representation))

                    # Last split instruction if any is considered into the block, instead of a split per se
                    if current_sub_block_index + 1 == len(sub_block_list):
                        current_sub_block.append(asm_bytecode)
                        sub_blocks.append(current_sub_block)
                        current_sub_block = []

                    else:
                        sub_blocks.append(current_sub_block)
                        current_sub_block = []
                        sub_blocks.append(asm_bytecode)

                    pop_initial = True
                    current_sub_block_index += 1
                    # First instruction always corresponds to the split instruction, so we do not consider it again
                    current_instruction_in_sub_block = 1

                else:
                    # assert (sub_block_list[current_sub_block_index][current_instruction_in_sub_block].startswith(
                    #     plain_representation))

                    current_sub_block.append(asm_bytecode)
                    current_instruction_in_sub_block += 1

            else:
                # assert (sub_block_list[current_sub_block_index][current_instruction_in_sub_block].startswith(
                #    plain_representation))
                initial_instructions = False
                current_sub_block.append(asm_bytecode)
                if len(sub_block_list[current_sub_block_index]) - 1 == current_instruction_in_sub_block:
                    current_sub_block_index += 1
                    current_instruction_in_sub_block = 0
                else:
                    current_instruction_in_sub_block += 1
                    pop_initial = False

        # If there is a sub block left, we need to add it to the list
        if current_sub_block:
            sub_blocks.append(current_sub_block)

        return sub_blocks

    # Given a set of optimized sub_blocks (possibly containing None when no optimized block has been generated),
    # rebuilds a block considering the "isolated" instructions which split the blocks
    def set_instructions_from_sub_blocks(self, optimized_sub_blocks):
        current_sub_block = 0
        previous_sub_blocks = self.split_in_sub_blocks()

        instructions = []
        for elem in previous_sub_blocks:
            if isinstance(elem, list):
                # If no optimized block is in the list, then we just consider instructions without optimizing
                if optimized_sub_blocks[current_sub_block] is None:
                    instructions.extend(elem)
                # Otherwise, instructions from current block are added
                else:
                    instructions.extend(optimized_sub_blocks[current_sub_block])
                current_sub_block += 1
            else:
                instructions.append(elem)

        # The number of sub blocks must match
        # assert (current_sub_block == len(optimized_sub_blocks))
        self.instructions = instructions


    # Given a set of optimized sub_blocks (possibly containing None when no optimized block has been generated),
    # rebuilds a block considering the "isolated" instructions which split the blocks
    def set_instructions_from_sub_blocks_partition(self, optimized_sub_blocks, sub_blocks_list):
        current_sub_block = 0
        previous_sub_blocks = self.split_in_sub_blocks_partition(sub_blocks_list)

        instructions = []
        for elem in previous_sub_blocks:
            if isinstance(elem, list):
                # If no optimized block is in the list, then we just consider instructions without optimizing
                if optimized_sub_blocks[current_sub_block] is None:
                    instructions.extend(elem)
                # Otherwise, instructions from current block are added
                else:
                    instructions.extend(optimized_sub_blocks[current_sub_block])
                current_sub_block += 1
            else:
                instructions.append(elem)

        # The number of sub blocks must match
        # assert (current_sub_block == len(optimized_sub_blocks))
        self.instructions = instructions
