#!/usr/bin/env python3

class AsmContract():

    def __init__(self,cname):
        self.cname = cname
        self.code = []
        self.data = {}
        
    def setAux(self,dataId,aux):
        if not self.data.get(dataId,False):
            self.data[dataId] = {}
            self.data[dataId]["aux"] = aux

        else:
            self.data[dataId]["aux"] = aux

    def setRunCode(self,dataId,blocks):
        if not self.data.get(dataId, False):
            self.data[dataId] = {}
            self.data[dataId]["code"] = blocks

        else:
            self.data[dataId]["code"] = blocks
            
    def getInitCode(self):
        return self.code

    def setInitCode(self,blocks):
        self.code = blocks

    def addCodeBlock(self,block):
        self.code.append(block)


    def getData(self):
        return self.data

    def getDataIds(self):
        return self.data.keys()
    
    def getDataOf(self,dataId):
        return self.data[dataId]

    def getRunCodeOf(self,dataId):
        return self.data[dataId]["code"]

    def getContractName(self):
        return self.cname
    
    def __str__(self):
        content = ""
        content+=self.cname+"\n"
        content+="Code: "
        for c in self.code:
            content+=str(c)+"\n"
            
        # content+=str(self.code)+"\n"
        content+=str(self.data)
        return content
