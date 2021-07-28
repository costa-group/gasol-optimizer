import os
import sys

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))

import unittest

from sfs_generator.parser_asm import parse_asm
from gasol_asm import filter_optimized_blocks_by_intra_block_optimization
from sfs_generator.asm_bytecode import AsmBytecode

class TestIntraBlockOptimization(unittest.TestCase):
    def test_intra_block_optimization_1(self):
        asm_blocks = [ [AsmBytecode(-1,-1,-1,"POP", -1)], [AsmBytecode(-1,-1,-1,"POP", -1)], "Error",
                       [AsmBytecode(-1,-1,-1,"DUP", -1)], "Error", [AsmBytecode(-1,-1,-1,"POP", -1)],
                       [AsmBytecode(-1,-1,-1,"DUP", -1)], "Error", [AsmBytecode(-1,-1,-1,"POP", -1)],
                       [AsmBytecode(-1,-1,-1,"POP", -1)], "Error", [AsmBytecode(-1,-1,-1,"POP", -1)]]
        asm_sub_blocks = list(filter(lambda x: isinstance(x, list), asm_blocks))
        optimized_blocks = ['a', None, 'b', 'c', 1, 2, 3, None]
        expected_result =  [None, None, 'b', 'c', None, None, None, None]
        self.assertEqual(expected_result, filter_optimized_blocks_by_intra_block_optimization(asm_sub_blocks, optimized_blocks))



if __name__ == '__main__':
    unittest.main()
