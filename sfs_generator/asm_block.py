#!/usr/bin/env python3

import utils

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
            
    def __str__(self):
        content = ""
        content += "Block Id:"+str(self.identifier)+"\n"
        for i in self.instructions:
            content += str(i)+"\n"

        content+=str(self.source_stack)
        return content
