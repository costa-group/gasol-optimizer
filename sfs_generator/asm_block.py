#!/usr/bin/env python3

import sfs_generator.utils as utils
from sfs_generator.gasol_optimization import split_block

class AsmBlock():
    
    def __init__(self, cname, identifier, is_init_block):
        self.contract_name = cname
        self.identifier = identifier
        self.instructions = []
        #minimum size of the source stack
        self.source_stack = 0
        self.is_init_block = is_init_block

    def getContractName(self):
        return self.contract_name

    def setContractName(self,name):
        self.contract_name = name

    def getBlockId(self):
        return self.identifier

    def setBlockId(self, identifier):
        self.identifier = identifier

    def addInstructions(self,bytecode):
        self.instructions.append(bytecode)
        
    def getInstructions(self):
        return self.instructions

    def setInstructions(self, instructions):
        self.instructions = instructions

    def getSourceStack(self):
        return self.source_stack

    def setSourceStack(self, val):
        self.source_stack = val

    def get_is_init_block(self):
        return self.is_init_block

    def set_is_init_block(self, val):
        self.is_init_block = val

    def compute_stack_size(self):
        evm_instructions = map(lambda x: x.getDisasm(),self.instructions)
        
        init_stack = utils.compute_stack_size(evm_instructions)

        self.source_stack = init_stack

    # Split the block in a list of asm_bytecodes that contains either sub blocks or
    # isolated instructions (JUMPs or split instructions).
    def split_in_sub_blocks(self):
        sub_blocks = []
        current_sub_block = []
        for asm_bytecode in self.instructions:

            instruction = asm_bytecode.getDisasm()

            # Three cases: either a instruction correspond to a jump/end or split instruction or neither of them.
            if instruction in ["JUMP","JUMPI","STOP","RETURN","REVERT","INVALID","JUMPDEST","tag"] \
                    or instruction in split_block:
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
        assert (current_sub_block == len(optimized_sub_blocks))
        self.instructions = instructions


    def __str__(self):
        content = ""
        content += "Block Id:"+str(self.identifier)+"\n"
        for i in self.instructions:
            content += str(i)+"\n"

        content+=str(self.source_stack)
        return content
