import os
import sys

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))

import unittest

from sfs_generator.parser_asm import parse_asm
from sfs_generator.rebuild_asm import rebuild_asm
import json
import glob


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


if __name__ == '__main__':
    unittest.main()
