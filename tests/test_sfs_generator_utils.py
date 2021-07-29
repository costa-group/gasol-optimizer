import os
import sys

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))

import unittest

from sfs_generator.parser_asm import parse_asm
from sfs_generator.utils import compute_number_of_instructions_in_asm_json_per_file

class TestComputeNumberOfInstructions(unittest.TestCase):
    def test_compute_number_of_instructions_in_asm_json_per_file(self):
        project_path = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))
        input_path = project_path + "/examples/jsons-solc/0x7aa21657E549943089bfA6547465b910c6b89c98.json_solc"
        asm = parse_asm(input_path)
        number_of_instructions = compute_number_of_instructions_in_asm_json_per_file(asm)
        self.assertEqual(number_of_instructions, 9)


if __name__ == '__main__':
    unittest.main()
