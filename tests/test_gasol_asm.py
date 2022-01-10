import os
import sys

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))

import json
import unittest

from gasol_asm import filter_optimized_blocks_by_intra_block_optimization
from sfs_generator.asm_bytecode import AsmBytecode


class TestGasolASM(unittest.TestCase):
    def test_intra_block_optimization_1(self):
        asm_blocks = [ [AsmBytecode(-1,-1,-1,"POP", -1)], [AsmBytecode(-1,-1,-1,"POP", -1)], "Error",
                       [AsmBytecode(-1,-1,-1,"DUP", -1)], "Error", [AsmBytecode(-1,-1,-1,"POP", -1)],
                       [AsmBytecode(-1,-1,-1,"DUP", -1)], "Error", [AsmBytecode(-1,-1,-1,"POP", -1)],
                       [AsmBytecode(-1,-1,-1,"POP", -1)], "Error", [AsmBytecode(-1,-1,-1,"POP", -1)]]
        asm_sub_blocks = list(filter(lambda x: isinstance(x, list), asm_blocks))
        optimized_blocks = ['a', None, 'b', 'c', 1, 2, 3, None]
        expected_result =  [None, None, 'b', 'c', None, None, None, None]
        self.assertEqual(expected_result, filter_optimized_blocks_by_intra_block_optimization(asm_sub_blocks, optimized_blocks))

    def test_log_generation_1(self):
        asm_path1 = "tests/files/0x363c421901B7BDCa0f2a17dA03948D676bE350E4_optimized.json_solc"
        with open(asm_path1) as f:
            asm_json1 = json.load(f)
        asm_path2 = "tests/files/0x363c421901B7BDCa0f2a17dA03948D676bE350E4_optimized_from_log.json_solc"
        with open(asm_path2) as f:
            asm_json2 = json.load(f)

        self.assertDictEqual(asm_json1, asm_json2)

    def test_log_generation_2(self):
        asm_path1 = "tests/files/0x20e7Efc18f4D03670EDC2FD86b840AB2D01E030D_optimized.json_solc"
        with open(asm_path1) as f:
            asm_json1 = json.load(f)
        asm_path2 = "tests/files/0x20e7Efc18f4D03670EDC2FD86b840AB2D01E030D_optimized_from_log.json_solc"
        with open(asm_path2) as f:
            asm_json2 = json.load(f)

        self.assertDictEqual(asm_json1, asm_json2)


if __name__ == '__main__':
    unittest.main()
