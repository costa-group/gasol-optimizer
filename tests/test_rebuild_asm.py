import os
import sys

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))

import glob
import json
import unittest

from sfs_generator.parser_asm import parse_asm
from sfs_generator.rebuild_asm import rebuild_asm


class TestRebuildASM(unittest.TestCase):

    def test_rebuild_with_json_solc_examples(self):
        project_path = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))
        for input_path in glob.glob(project_path + "/examples/jsons-solc/*.json_solc"):
            asm = parse_asm(input_path)
            final_json = rebuild_asm(asm)

            with open(input_path) as f:
                data = json.load(f)
            with self.subTest(msg="Failed at " + input_path):
                self.assertDictEqual(data, final_json)

    def test_to_json_leads_to_same_asm(self):
        project_path = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))
        for input_path in glob.glob(project_path + "/examples/jsons-solc/*.json_solc"):
            with open(input_path) as f:
                json_load = json.load(f)

            asm = parse_asm(input_path)
            json_generated = asm.to_json()
            with self.subTest(msg="Failed at " + input_path):
                self.assertDictEqual(json_load, json_generated)

if __name__ == '__main__':
    unittest.main()
