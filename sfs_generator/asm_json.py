#!/usr/bin/env python3

from asm_contract import AsmContract

class AsmJSON():

    def __init__(self):
        self.solc_version = ""
        self.contracts = []
        
    def getVersion(self):
        return solc_version

    def setVersion(self,v):
        self.solc_version = v

    def getContracts(self):
        return self.contracts

    def addContracts(self,contract):
        if isinstance(contract,AsmContract):
            self.contracts.append(contract)

        else:
            raise TypeError("addContracts: contract is not an instance of AsmContract")


    def __str__(self):
        content = ""
        for c in self.contracts:
            content+=str(c)+"\n"

        content+=self.solc_version+"\n"
        return content
