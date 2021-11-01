#!/usr/bin/env python3
import os
import sys
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))
import glob

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/global_params")
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/sfs_generator")
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/statistics")


from parser_asm import parse_asm
from properties_from_asm_json import compute_bytecode_size_in_asm_json_per_file
import argparse




if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("-path", metavar='path', action='store', type=str,
                        help="", required=True)

    args = parser.parse_args()
    parent_directory = args.path
    total_size = 0
    for asm_json in glob.glob(parent_directory + "/*.json_solc"):
        old_asm = parse_asm(asm_json)
        total_size += compute_bytecode_size_in_asm_json_per_file(old_asm)

    exit(total_size)
