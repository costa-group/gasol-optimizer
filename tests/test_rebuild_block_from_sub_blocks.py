import os
import sys

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))

import glob
import unittest
from copy import deepcopy

from sfs_generator.parser_asm import parse_asm
from sfs_generator.rebuild_asm import rebuild_asm_contract


class TestRebuildBlockFromSubBlocks(unittest.TestCase):

    def test_copy_contract_leads_to_same_asm(self):
        project_path = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))
        for input_path in glob.glob(project_path + "/examples/jsons-solc/*.json_solc"):
            asm = parse_asm(input_path)
            for c in asm.getContracts():
                new_contract = deepcopy(c)
                prev_contract_dict = rebuild_asm_contract(c)
                new_contract_dict = rebuild_asm_contract(new_contract)
                with self.subTest(msg="Failed at " + input_path):
                    self.assertDictEqual(prev_contract_dict, new_contract_dict)

    def test_copy_blocks_leads_to_same_asm(self):
        project_path = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))
        for input_path in glob.glob(project_path + "/examples/jsons-solc/*.json_solc"):
            asm = parse_asm(input_path)
            for c in asm.getContracts():
                init_code = c.getInitCode()
                new_contract = deepcopy(c)

                new_init_code = []
                for block in init_code:
                    new_block = deepcopy(block)
                    new_init_code.append(new_block)

                new_contract.setInitCode(new_init_code)

                for identifier in c.getDataIds():
                    blocks = c.getRunCodeOf(identifier)
                    new_run_code = []
                    for block in blocks:
                        new_block = deepcopy(block)
                        new_run_code.append(new_block)

                    new_contract.setRunCode(identifier, new_run_code)

                prev_contract_dict = rebuild_asm_contract(c)
                new_contract_dict = rebuild_asm_contract(new_contract)
                with self.subTest(msg="Failed at " + input_path):
                    self.assertDictEqual(prev_contract_dict, new_contract_dict)

    def test_rebuild_blocks_leads_to_same_asm(self):
        project_path = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))
        for input_path in glob.glob(project_path + "/examples/jsons-solc/*.json_solc"):
            asm = parse_asm(input_path)
            for c in asm.getContracts():
                init_code = c.getInitCode()
                new_contract = deepcopy(c)

                new_init_code = []
                for block in init_code:
                    new_block = deepcopy(block)
                    sub_blocks_size = len(list(filter(lambda x: isinstance(x, list), new_block.split_in_sub_blocks())))
                    non_optimized_list = [None] * sub_blocks_size
                    new_block.set_instructions_from_sub_blocks(non_optimized_list)
                    new_init_code.append(new_block)

                new_contract.setInitCode(new_init_code)

                for identifier in c.getDataIds():
                    blocks = c.getRunCodeOf(identifier)
                    new_run_code = []
                    for block in blocks:
                        new_block = deepcopy(block)
                        sub_blocks_size = len(list(filter(lambda x: isinstance(x, list), new_block.split_in_sub_blocks())))
                        non_optimized_list = [None] * sub_blocks_size
                        new_block.set_instructions_from_sub_blocks(non_optimized_list)
                        new_run_code.append(new_block)

                    new_contract.setRunCode(identifier, new_run_code)

                prev_contract_dict = rebuild_asm_contract(c)
                new_contract_dict = rebuild_asm_contract(new_contract)
                with self.subTest(msg="Failed at " + input_path):
                    self.assertDictEqual(prev_contract_dict, new_contract_dict)


if __name__ == '__main__':
    unittest.main()
