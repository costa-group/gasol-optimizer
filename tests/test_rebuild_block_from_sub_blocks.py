import os
import glob
import unittest
from copy import deepcopy
from sfs_generator.parser_asm import parse_asm


class TestRebuildBlockFromSubBlocks(unittest.TestCase):

    def test_copy_contract_leads_to_same_asm(self):
        project_path = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))
        for input_path in glob.glob(project_path + "/examples/jsons-solc/*.json_solc"):
            asm = parse_asm(input_path)
            for c in asm.contracts:
                new_contract = deepcopy(c)
                prev_contract_dict = c.to_json()
                new_contract_dict = new_contract.to_json()
                with self.subTest(msg="Failed at " + input_path):
                    self.assertDictEqual(prev_contract_dict, new_contract_dict)

    def test_copy_blocks_leads_to_same_asm(self):
        project_path = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))
        for input_path in glob.glob(project_path + "/examples/jsons-solc/*.json_solc"):
            asm = parse_asm(input_path)
            for c in asm.contracts:
                init_code = c.init_code
                new_contract = deepcopy(c)

                new_init_code = []
                for block in init_code:
                    new_block = deepcopy(block)
                    new_init_code.append(new_block)

                new_contract.init_code = new_init_code

                for identifier in c.get_data_ids_with_code():
                    blocks = c.get_run_code(identifier)
                    new_run_code = []
                    for block in blocks:
                        new_block = deepcopy(block)
                        new_run_code.append(new_block)

                    new_contract.set_run_code(identifier, new_run_code)

                prev_contract_dict = c.to_json()
                new_contract_dict = new_contract.to_json()
                with self.subTest(msg="Failed at " + input_path):
                    self.assertDictEqual(prev_contract_dict, new_contract_dict)


if __name__ == '__main__':
    unittest.main()
