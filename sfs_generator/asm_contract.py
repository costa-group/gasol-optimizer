#!/usr/bin/env python3

class AsmContract:

    def __init__(self,cname, contains_asm_field = True):
        self.cname = cname
        self.code = []
        self.data = {}
        self.data_addresses = {}
        self.contains_asm_field = contains_asm_field

    def has_asm_field(self):
        return self.contains_asm_field

    def setAux(self,data_id,aux):
        if not self.data.get(data_id,False):
            self.data[data_id] = {}
            self.data[data_id]["aux"] = aux
            
        else:
            self.data[data_id]["aux"] = aux


    def setRunCode(self,data_id,blocks):
        if not self.data.get(data_id, False):
            self.data[data_id] = {}
            self.data[data_id]["code"] = blocks

        else:
            self.data[data_id]["code"] = blocks

    def setAuxData(self,data_id,data):
        if not self.data.get(data_id,False):
            self.data[data_id]["data"] = {}
            self.data[data_id]["data"] = data

        else:
            self.data[data_id]["data"] = data

    def setData(self,data_id,data):
        if not self.data_addresses.get(data_id,False):
            self.data_addresses[data_id] = data
            
    def getInitCode(self):
        return self.code

    def setInitCode(self,blocks):
        self.code = blocks

    def addCodeBlock(self,block):
        self.code.append(block)
        
    def is_data_address(self, data_id):
        return data_id in self.data_addresses


    def getDataField(self, data_id):
        return self.data_addresses[data_id]

    def getDataFieldIds(self):
        return self.data_addresses.keys()

    def getDataIds(self):
        return self.data.keys()
    
    def getDataOf(self,data_id):
        return self.data[data_id]

    def getRunCodeOf(self,data_id):
        return self.data[data_id]["code"]
    
    def get_aux(self,data_id):
        return self.data[data_id]["aux"]
    
    def get_data_aux(self,data_id):
        return self.data[data_id].get("data", None)

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
