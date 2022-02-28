
from sfs_generator.asm_contract import AsmContract
from typing import List, Any, Dict


class AsmJSON:
    """
    Class that represents the whole output from solc when enabling --combined-json asm.
    Contains multiple contracts and the solidity version in which it was compiled
    """

    def __init__(self, version : str):
        self._solc_version = version
        self._contracts = []

    @property
    def version(self) -> str:
        return self._solc_version

    @property
    def contracts(self) -> List[AsmContract]:
        return self._contracts

    @contracts.setter
    def contracts(self, contracts : List[AsmContract]) -> None:
        self._contracts = contracts

    def add_contract(self, contract : AsmContract) -> None:
        self._contracts.append(contract)

    def to_json(self) -> Dict[str, Any]:

        final_asm = {"version": self.version}

        contracts = {key : val for contract in self.contracts for key, val in contract.to_json().items()}

        final_asm["contracts"] = contracts

        return final_asm


    def __str__(self):
        content = ""
        for c in self.contracts:
            content+=str(c)+"\n"

        content+=self.version + "\n"
        return content
