#!/usr/bin/env python3

class AsmBytecode():

    def __init__(self,begin,end,soruce,disasm,value):
        self.begin = begin
        self.end = end
        self.source = soruce
        self.disasm = disasm
        self.value = value


    def getBegin(self):
        return self.begin
    
    def setBegin(self, v):
        self.begin = v
        
    def getEnd(self):
        return self.end
    
    def setEnd(self, v):
        self.end = v
        
    def getSource(self):
        return self.source
    
    def setSource(self, v):
        self.source = v

    def getDisasm(self):
        return self.disasm
    
    def setDisasm(self, v):
        self.disasm = v

    def getValue(self):
        return self.value
    
    def setValue(self, v):
        self.value = v

    def __str__(self):
        content = "{begin:"+str(self.begin)+", end:"+str(self.end)+", source:"+str(self.source)+", name:"+str(self.disasm)+", value:"+str(self.value)+"}"
        return content
