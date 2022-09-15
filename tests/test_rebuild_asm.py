import os
import glob
import json
import unittest
from sfs_generator.parser_asm import parse_asm

class TestRebuildASM(unittest.TestCase):

    def test_to_json_leads_to_same_asm_lt_v_0_8_14(self):
        project_path = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))
        for input_path in glob.glob(project_path + "/examples/jsons-solc/*.json_solc"):
            with open(input_path) as f:
                json_load = json.load(f)

            asm = parse_asm(input_path)
            json_generated = asm.to_json()
            with self.subTest(msg="Failed at " + input_path):
                self.assertDictEqual(json_load, json_generated)

    def test_to_json_leads_to_same_asm_ge_v_0_8_14(self):
        project_path = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))
        for input_path in glob.glob(project_path + "/tests/files/solc_v_0_8_15/*.json_solc"):
            with open(input_path) as f:
                json_load = json.load(f)

            asm = parse_asm(input_path)
            json_generated = asm.to_json()
            with self.subTest(msg="Failed at " + input_path):
                self.assertDictEqual(json_load, json_generated)


if __name__ == '__main__':
    unittest.main()
