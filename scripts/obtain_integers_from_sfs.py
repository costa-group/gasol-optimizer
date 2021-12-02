#!/usr/bin/python3
import argparse
import os
import glob
import pathlib
import shlex
import subprocess
import re
import json
import pandas as pd
import sys
from sympy.ntheory import factorint
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/global_params")
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/sfs_generator")
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/smt_encoding")
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/verification")
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/scripts")
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/solution_generation")
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))
from parser_asm import parse_asm
import asm_bytecode
import stopit
from math import ceil, floor, log2

def modifiable_path_files_init():
    parser = argparse.ArgumentParser()
    parser.add_argument("-jsons-folder", metavar='jsons_folder', action='store', type=str,
                        help="folder that contains the jsons to analyze. It must be in the proper format",
                        required=True)
    parser.add_argument("-csv-folder", metavar='csv_folder', action='store', type=str,
                        help="folder that will store the csvs containing the statistics per file. Inside that folder, "
                             "another subfolder is created: solver_name + _ + timeout + 's'", required=True)


    global args
    args = parser.parse_args()

    # Folder in which the csvs are stored. A csv is generated per each analyzed file
    global results_dir
    results_dir = args.csv_folder
    if results_dir[-1] != "/":
        results_dir += "/"

    # Folder which contains the json files to analyze. Must follow this structure:
    # - main_folder
    #   -- contract_1_folder
    #      --- block_1.json
    #      --- block_2.json
    #      ...
    #   -- contract_2_folder
    #      --- block_1.json
    #      --- block_2.json
    #      ...
    #   ...
    global contracts_dir_path
    contracts_dir_path = args.jsons_folder
    if contracts_dir_path[-1] != "/":
        contracts_dir_path += "/"


def init():
    modifiable_path_files_init()

relevant_operations = ["ADD", "MUL", "SUB", "EXP", "SHL", "AND", "OR", "XOR", "NOT"]


def update_integer_values(count_integer, reconstruct_integer, value, name):
    count_integer[value] = count_integer.get(value, 0) + 1
    current_set = reconstruct_integer.get(value, set())
    current_set.add(name)
    reconstruct_integer[value] = current_set


def negate(number, bits = 256):
    return int(format(~number & 2 ** bits - 1, "0{}b".format(bits)), 2)


def process_block(block, count_integer, reconstruct_integer, big_numbers):
    stack_act = []
    names = []
    for asm_bytecode in block.getInstructions():
        op_name = asm_bytecode.getDisasm()

        if op_name == "PUSH":
            pushed_value = int(asm_bytecode.getValue(), 16)
            if len(asm_bytecode.getValue()) > 1:
                big_numbers[pushed_value] = big_numbers.get(pushed_value, 0) + 1

            stack_act.insert(0, pushed_value)
            names.insert(0, "PUSH " + asm_bytecode.getValue())

        elif op_name == "NOT" and len(stack_act) > 0:
            op1 = stack_act[0]
            name1 = names[0]
            stack_act.pop(0)
            names.pop(0)

            names.insert(0, op_name + "(" + name1 + ")")
            stack_act.insert(0, negate(op1))

        elif len(stack_act) > 1 and op_name in relevant_operations:
            op1, op2 = stack_act[0], stack_act[1]
            name1, name2 = names[0], names[1]
            stack_act.pop(0)
            stack_act.pop(0)

            names.pop(0)
            names.pop(0)

            names.insert(0, op_name + "(" + name1 + ", " + name2 + ")")

            if op_name == "ADD":
                stack_act.insert(0, op1 + op2)
            elif op_name == "MUL":
                stack_act.insert(0, op1 * op2)
            elif op_name == "SUB":
                stack_act.insert(0, op1 - op2)
            elif op_name == "EXP":
                stack_act.insert(0, op1 ** op2)
            elif op_name == "SHL":
                stack_act.insert(0, op2 << op1)
            elif op_name == "AND":
                stack_act.insert(0, op1 & op2)
            elif op_name == "OR":
                stack_act.insert(0, op1 | op2)
            elif op_name == "XOR":
                stack_act.insert(0, op1 ^ op2)
            else:
                raise ValueError("Forgotten operation")
        else:
            for value, name in zip(stack_act, names):
                update_integer_values(count_integer, reconstruct_integer, value, name)

            stack_act = []
            names = []

    for value, name in zip(stack_act, names):
        update_integer_values(count_integer, reconstruct_integer, value, name)


def factorize_with_timeout(number, c, timeout=1):
    print(c, number)
    with stopit.ThreadingTimeout(timeout) as to_ctx_mgr:
        assert to_ctx_mgr.state == to_ctx_mgr.EXECUTING
        factorization = factorint(number)

    # OK, let's check what happened
    if to_ctx_mgr.state == to_ctx_mgr.EXECUTED:
        return factorization
    else:
        return dict()

def find_nearest_perfect_power(n):
    base = 0
    exponent = 1
    current_cost = 2*n
    current_diff = n

    for k in range(2, floor(log2(n)) + 1):
        base1 = ceil(n ** (1/k))
        base2 = floor(n ** (1/k))

        candidate1 = base1 ** k
        candidate2 = base2 ** k

        diff1 = abs(candidate1 - n)
        diff2 = abs(candidate2 - n)

        cost1 = len(hex(base1)[2:]) + len(hex(k)[2:]) + len(hex(diff1)[2:])
        cost2 = len(hex(base2)[2:]) + len(hex(k)[2:]) + len(hex(diff2)[2:])

        if cost2 <= min(cost1, current_cost):
            current_diff = diff2
            exponent = k
            base = base2
            current_cost = cost2

        elif cost1 <= min(cost2, current_cost):
            current_diff = diff1
            exponent = k
            base = base2
            current_cost = cost1

    print(n, current_diff, base, exponent)
    return current_diff, base, exponent

# That's not possible

if __name__=="__main__":
    global args
    init()
    pathlib.Path(results_dir).mkdir(parents=True, exist_ok=True)

    count_integer = dict()
    reconstruct_integer = dict()
    big_numbers = dict()

    total_blocks = 0
    for asm_file in glob.glob(contracts_dir_path + "*.json_solc"):
        asm_json = parse_asm(asm_file)
        for c in asm_json.getContracts():
            for identifier in c.getDataIds():
                blocks = c.getRunCodeOf(identifier)
                for block in blocks:
                    process_block(block, count_integer, reconstruct_integer, big_numbers)

    df = pd.DataFrame([{"hexadecimal": hex(k), "decimal":k, "count":v, "expression": str(reconstruct_integer[k])} for k, v in
                       reversed(sorted(count_integer.items(), key=lambda kv: kv[1]))])
    df.to_csv(results_dir + "integer_constants.csv")

    current_rows = []
    for k, v in reversed(sorted(big_numbers.items(), key=lambda kv: kv[1])):
        current_diff, base, exponent = find_nearest_perfect_power(k)
        current_rows.append({"hexadecimal": hex(k), "decimal": k, "count": v, "base": base, "base_hex": hex(base),
                             "exponent": exponent, "exponent_hex": hex(exponent), "final_diff": current_diff,
                             "final_diff_hex": hex(current_diff) , "current_bytes" : len(hex(k)[2:]) / 2 + 1,
                             "expected_bytes": (len(hex(base)[2:]) + len(hex(exponent)[2:]) + len(hex(current_diff)[2:])) / 2 + 4})
    df2 = pd.DataFrame(current_rows)
    df2.to_csv(results_dir + "pushed_values.csv")


    # df2 = pd.DataFrame([{"hexadecimal": hex(k), "decimal": k, "count": v, "factorization": str(factorize_with_timeout(k, v))} for k, v in
    #      reversed(sorted(big_numbers.items(), key=lambda kv: kv[1])) if v > 15])
    # df2.to_csv(results_dir + "pushed_values.csv")