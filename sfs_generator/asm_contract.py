from sfs_generator.asm_block import AsmBlock
from sfs_generator.utils import get_block
from typing import List, Dict, Optional, Union, Any


class AsmContract:
    """
    Class that represents an assembly contract
    """

    def __init__(self,cname : str, contains_asm_field : bool = True):
        self.contract_name = cname
        self._code = []
        self.data = {}
        self.data_addresses = {}
        self.has_asm_field = contains_asm_field
        self._source_list = None

    @property
    def init_code(self) -> List[AsmBlock]:
        return self._code

    @init_code.setter
    def init_code(self, new_value : List[AsmBlock]):
        self._code = new_value

    @property
    def source_list(self) -> Optional[List[str]]:
        """
        Returns the associated sourceList field for a data id. Included in solc 0.8.14
        """
        return self._source_list

    @source_list.setter
    def source_list(self, source_list: List[str]) -> None:

        self._source_list = source_list

    def set_auxdata(self, data_id : str, aux : str) -> None:
        """
        Set aux field from
        :param data_id: data id that identifies current assembly structure
        :param aux: value to set for param aux data
        :return: None
        """
        if not self.data.get(data_id,False):
            self.data[data_id] = {}
            self.data[data_id]["auxdata"] = aux
            
        else:
            self.data[data_id]["auxdata"] = aux


    def set_run_code(self, data_id : str, blocks : List[AsmBlock]) -> None:
        """
        Sets the associated run code for a data id
        :param data_id: data id that identifies current assembly structure
        :param blocks: list of AsmBlocks
        :return:
        """
        if not self.data.get(data_id, False):
            self.data[data_id] = {}
            self.data[data_id]["code"] = blocks

        else:
            self.data[data_id]["code"] = blocks


    def set_data_field(self, data_id : str, data : Dict[str, str]) -> None:
        """
        Sets the "data" field inside the assembly structure. This data field contains pairs value/key,
        where the associated value is an Event hash

        :param data_id: data id that identifies current assembly structure
        :param data: a dict containing key/value as strings
        :return: None
        """
        if not self.data.get(data_id,False):
            self.data[data_id]["data"] = {}
            self.data[data_id]["data"] = data

        else:
            self.data[data_id]["data"] = data


    def set_data_field_with_address(self, data_id : str, data: str) -> None:
        """
        Sets the data when a string is passed instead of a dict

        :param data_id: data id that identifies current assembly structure
        :param data: a string that represents an address
        :return: None
        """
        if not self.data_addresses.get(data_id,False):
            self.data_addresses[data_id] = data

        
    def is_data_address(self, data_id : str) -> bool:
        """
        Given a data id, determines whether it has an associated address or not
        :param data_id: data id that identifies current assembly structure
        :return: True if it has an associated address, False otherwise
        """
        return data_id in self.data_addresses


    def get_data_address(self, data_id : str) -> str:
        """
        Given a data id, returns the associated address
        :param data_id: data id that identifies current assembly structure
        :return: the associated address
        """
        return self.data_addresses[data_id]

    def get_data_ids_with_data_address(self) -> [str]:
        """
        Returns an iterator with all the data ids that have an associated address
        :return: iterator of strings
        """
        return self.data_addresses.keys()


    def get_data_ids_with_code(self) -> [str]:
        """
        Returns an iterator with all the data ids that have an associated code
        :return: iterator of strings
        """
        return self.data.keys()
    
    def get_data_structure_from_id(self, data_id : str) -> Dict[str, Union[List[AsmBlock], str, Dict[str, str]]]:
        """
        Returns a dict containing .auxdata, .code and (possibly) .data fields from the assembly.
        These corresponding keys are "auxdata", "code" and "data" respectively.
        :param data_id: data id that identifies current assembly structure
        :return: a dict with the described structure
        """
        return self.data[data_id]

    def get_run_code(self, data_id : str) -> List[AsmBlock]:
        """
        Returns the associated run code for a data id.
        :param data_id: data id that identifies current assembly structure
        :return: the list of blocks in which the run code is split
        """
        return self.data[data_id]["code"]
    
    def get_auxdata(self, data_id : str) -> str:
        """
        Returns the associated auxdata field for a data id.
        :param data_id: data id that identifies current assembly structure
        :return: a string containing the auxdata information
        """
        return self.data[data_id]["auxdata"]
    
    def get_data_field(self, data_id : str) -> Optional[Dict[str, str]]:
        """
        Sets the "data" field inside the assembly structure. This data field contains pairs value/key,
        where the associated value is an Event hash

        :param data_id: data id that identifies current assembly structure
        :return: a dict with event address as values
        """
        return self.data[data_id].get("data", None)


    def build_static_edges_init(self)->None:
        self.build_static_edges(self.init_code)


    def build_static_edges_runtime(self)->None:
        for data_id in self.data:
            self.build_static_edges(self.data[data_id]["code"])
            
    def build_static_edges(self,blocks:[AsmBlock])-> None:
        for block in blocks:
            instructions = block.instructions
            last_instruction = instructions[-1].get_disasm()

            if "JUMP" == last_instruction and len(instructions)>1:
                if "PUSH [tag]" == instructions[-2].get_disasm():
                    tag = instructions[-2].get_value()
                    block.jump_to = get_block(blocks, tag).get_block_id()

            elif "JUMPI" == last_instruction and len(instructions)>1:
                if "PUSH [tag]" == instructions[-2].get_disasm():
                    tag = instructions[-2].get_value()
                    block.jump_to = get_block(blocks, tag).get_block_id()
                    block.falls_to = block.get_block_id()+1
            elif block.jump_type == "falls_to":
                block.falls_to = block.get_block_id()+1
                
    def to_json(self) -> Dict[str, Any]:

        # If it has no asm field, we just return the contract name with an empty dict tied
        if not self.has_asm_field:
            return {self.contract_name : {}}

        json_contract = {".code": [instruction.to_json() for block in self.init_code for instruction in block.instructions]}

        source_list = self.source_list
        if source_list is not None:
            json_contract["sourceList"] = source_list

        data_ids = self.get_data_ids_with_code()

        json_data = {}

        for data_id in data_ids:

            json_data_fields = {}

            aux_data = self.get_auxdata(data_id)
            if aux_data is not None:
                json_data_fields[".auxdata"] = aux_data

            run_bytecode = [instruction.to_json() for block in self.get_run_code(data_id) for instruction in block.instructions]
            json_data_fields[".code"] = run_bytecode

            data = self.get_data_field(data_id)
            if data is not None:
                json_data_fields[".data"] = data

            json_data[data_id] = json_data_fields

        data_addresses = self.get_data_ids_with_data_address()

        for address in data_addresses:
            json_data[address] = self.get_data_address(address)

        json_contract[".data"] = json_data

        return {self.contract_name: {"asm": json_contract}}

    def to_plain(self) -> str:
        if not self.has_asm_field:
            return self.contract_name

        plain_representation_list = [self.contract_name, "Initial code"]

        plain_representation_list.extend([asm_block.to_plain() for asm_block in self.init_code])

        for data_id in self.get_data_ids_with_code():
            plain_representation_list.append(' '.join(["Run code of", str(data_id)]))

            plain_representation_list.extend([asm_block.to_plain() for asm_block in self.get_run_code(data_id)])

        return '\n'.join(plain_representation_list)
    
    def __str__(self):
        content = ""
        content+=self.contract_name + "\n"
        content+="Code: "
        for c in self.init_code:
            content+=str(c)+"\n"
            
        # content+=str(self.code)+"\n"
        content+=str(self.data)
        return content

    
