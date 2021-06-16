#!/usr/bin/env python3

import sys
import os
sys.path.append(os.path.dirname(os.path.realpath(__file__))+"/../ethir")
import opcodes

class AsmBlock():
    
    def __init__(self, cname, identifier):
        self.contract_name = cname
        self.identifier = identifier
        self.instructions = []
        #minimum size of the source stack
        self.source_stack = 0

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

    def compute_stack_size(self):
        init_stack = self.source_stack
        current_stack = 0

        for i in self.instructions:
            op = i.getDisasm()
            opcode_info = opcodes.get_opcode(op)

            consumed_elements = opcode_info[1]
            produced_elements = opcode_info[2]
            
            if consumed_elements > current_stack:
                diff = consumed_elements - current_stack
                init_stack +=diff
                current_stack = current_stack+diff-consumed_elements+produced_elements
            else:
                current_stack = current_stack-consumed_elements+produced_elements

        self.source_stack = init_stack
            
    def __str__(self):
        content = ""
        content += "Block Id:"+str(self.identifier)+"\n"
        for i in self.instructions:
            content += str(i)+"\n"

        content+=str(self.source_stack)
        return content
