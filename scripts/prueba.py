#!/usr/bin/env python3
import os
import sys
sys.path.append("../")
sys.path.append("../sfs_generator")
from sfs_generator import ir_block
from sfs_generator.gasol_optimization import get_sfs_dict

if __name__ == "__main__":

    block_data = {'instructions': ['PUSHTAG 0x52', 'DUP2', 'PUSH 0x40', 'MLOAD', 'DUP1', 'PUSH 0x20', 'ADD', 'PUSH 0x40', 'MSTORE',
                      'DUP1', 'PUSH 0x0', 'DUP2', 'MSTORE', 'POP', 'PUSH 0x0', 'PUSHTAG 0x53'], 'input': 1}
    block_id = 35
    print(block_data)
    exit_code = ir_block.evm2rbr_compiler(contract_name="aaa", block=block_data, block_id=block_id,
                                          preffix="", simplification=True)
    sfs_dict = get_sfs_dict()
    print(sfs_dict)