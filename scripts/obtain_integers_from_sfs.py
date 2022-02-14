#!/usr/bin/python3
import argparse
import glob
import json
import os
import pathlib
import re
import shlex
import subprocess
import sys

import pandas as pd
from sympy.ntheory import factorint

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/global_params")
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/sfs_generator")
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/smt_encoding")
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/verification")
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/scripts")
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/solution_generation")
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))
from math import ceil, floor, log2

import asm_bytecode
import stopit
from parser_asm import parse_asm


def modifiable_path_files_init():
    parser = argparse.ArgumentParser()
    parser.add_argument("-jsons-folder", metavar='jsons_folder', action='store', type=str,
                        help="folder that contains the jsons to analyze. It must be in the proper format",
                        required=True)
    parser.add_argument("-csv-folder", metavar='csv_folder', action='store', type=str,
                        help="folder that will store the csvs containing the properties per file. Inside that folder, "
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


def update_integer_values(count_integer, reconstruct_integer, associated_cost, associated_bytes, value, name, n_bytes, gas_cost):
    count_integer[value] = count_integer.get(value, 0) + 1

    current_set = reconstruct_integer.get(value, set())
    current_set.add(name)
    reconstruct_integer[value] = current_set

    current_set = associated_cost.get(value, set())
    current_set.add(gas_cost)
    associated_cost[value] = current_set

    current_set = associated_bytes.get(value, set())
    current_set.add(n_bytes)
    associated_bytes[value] = current_set


def negate(number, bits = 256):
    return int(format(~number & 2 ** bits - 1, "0{}b".format(bits)), 2)


def bytes_associated_to_push(n):
    return 1 + int(ceil(len(hex(n)[2:]) / 2))


def process_block(block, count_integer, reconstruct_integer, associated_cost, associated_bytes, big_numbers):
    stack_act = []
    names = []
    current_cost = 0
    current_bytes = 0

    for asm_bytecode in block.getInstructions():
        op_name = asm_bytecode.getDisasm()

        if op_name == "PUSH":
            pushed_value = int(asm_bytecode.getValue(), 16)
            if len(asm_bytecode.getValue()) > 1:
                big_numbers[pushed_value] = big_numbers.get(pushed_value, 0) + 1

            stack_act.insert(0, pushed_value)
            names.insert(0, "PUSH " + asm_bytecode.getValue())
            current_bytes += bytes_associated_to_push(pushed_value)
            current_cost += 3

        elif op_name == "NOT" and len(stack_act) > 0:
            op1 = stack_act[0]
            name1 = names[0]
            stack_act.pop(0)
            names.pop(0)

            names.insert(0, op_name + "(" + name1 + ")")
            stack_act.insert(0, negate(op1))

            current_bytes += 1
            current_cost += 3

        elif len(stack_act) > 1 and op_name in relevant_operations:
            op1, op2 = stack_act[0], stack_act[1]
            name1, name2 = names[0], names[1]
            stack_act.pop(0)
            stack_act.pop(0)

            names.pop(0)
            names.pop(0)

            names.insert(0, op_name + "(" + name1 + ", " + name2 + ")")

            current_bytes += 1
            current_cost += 3

            if op_name == "ADD":
                stack_act.insert(0, op1 + op2)
            elif op_name == "MUL":
                stack_act.insert(0, op1 * op2)
            elif op_name == "SUB":
                stack_act.insert(0, op1 - op2)
            elif op_name == "EXP":
                stack_act.insert(0, op1 ** op2)
                current_cost += 7 + 50 * (bytes_associated_to_push(op2)-1)
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
                update_integer_values(count_integer, reconstruct_integer, associated_cost, associated_bytes, value,
                                      name, current_bytes, current_cost)

            stack_act = []
            names = []
            current_cost = 0
            current_bytes = 0

    for value, name in zip(stack_act, names):
        update_integer_values(count_integer, reconstruct_integer, associated_cost, associated_bytes, value, name,
                              current_bytes, current_cost)


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
    addition = True

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
            # base1 ** candidate1 >= n, so the diff is subtracted
            addition = False

        elif cost1 <= min(cost2, current_cost):
            current_diff = diff1
            exponent = k
            base = base2
            current_cost = cost1
            addition = True

    return current_diff, base, exponent, addition


def find_nearest_shift(n):
    base = 0
    exponent = 1
    current_cost = 2*n
    current_diff = n
    current_factor = 0
    addition = True

    for k in range(2, floor(log2(n)) + 1):
        for factor in range(1, 256):

            base1 = ceil((n / factor) ** (1/k))
            base2 = floor((n / factor) ** (1/k))

            candidate1 = (base1 * factor) ** k
            candidate2 = (base2 * factor) ** k

            diff1 = abs(candidate1 - n)
            diff2 = abs(candidate2 - n)


            # SHL(factor, k), where len(factor) == 1
            if base1 == 2:
                cost1 = bytes_associated_to_push(k) + 3

            # MUL(EXP(base, k), PUSH factor), where len(factor) == 1
            else:
                if factor > 1:
                    cost1 = bytes_associated_to_push(base1) + bytes_associated_to_push(k) + 4
                else:
                    cost1 = bytes_associated_to_push(base1) + bytes_associated_to_push(k) + 1

            # SHL(factor, k), where len(factor) == 1
            if base2 == 2:
                cost2 = bytes_associated_to_push(k) + 3

            # MUL(EXP(base, k), PUSH factor), where len(factor) == 1
            else:
                if factor > 1:
                    cost2 = bytes_associated_to_push(base2) + bytes_associated_to_push(k) + 4
                else:
                    cost2 = bytes_associated_to_push(base2) + bytes_associated_to_push(k) + 1

            if diff1 != 0:
                cost1 += bytes_associated_to_push(diff1)

            if diff2 != 0:
                cost2 += bytes_associated_to_push(diff2)

            if cost2 <= min(cost1, current_cost):
                current_diff = diff2
                exponent = k
                base = base2
                current_cost = cost2
                current_factor = factor
                # base1 ** candidate1 >= n, so the diff is subtracted
                addition = False

            elif cost1 <= min(cost2, current_cost):
                current_diff = diff1
                exponent = k
                base = base2
                current_cost = cost1
                current_factor = factor
                addition = True

    return current_diff, base, exponent, current_factor, addition


def build_best_configuration(n, remaining_bytes, already_negated):
    # We need at least two bytes to generate a number
    if remaining_bytes <= 1:
        return None, None
    cost_push = bytes_associated_to_push(n)
    expression_push = "PUSH " + hex(n)[2:]

    cost_best = cost_push
    expression_best = expression_push

    # There is no way to obtain better results if the pushed values has 2 bytes
    if len(hex(n)[2:])  <= 2:

        # There are enough bytes to represent the number
        if cost_push <= remaining_bytes:
            return cost_push, expression_push
        else:
            return None, None


    if not already_negated:
        cost, expression = build_best_configuration(negate(n), min(remaining_bytes-1, bytes_associated_to_push(negate(n))) , False)
        if cost is not None and cost + 1 < cost_best:
            cost_best = cost + 1
            expression_best = "NOT(" + expression + ")"

    current_diff, base, exponent, factor, is_addition = find_nearest_shift(n)

    cost_base, expression_base = build_best_configuration(base, min(remaining_bytes - 1, bytes_associated_to_push(base)) , True)
    cost_exponent, expression_exponent = build_best_configuration(exponent, min(remaining_bytes - 1, bytes_associated_to_push(exponent)) , True)

    if cost_base is not None and cost_exponent is not None:

        # SHL(factor, k), where len(factor) == 1
        if base == 2:
            cost_without_diff = cost_exponent + 3
            expression_without_diff = "SHL(" + expression_exponent + ", " + "PUSH " + hex(factor)[2:] + ")"

        # MUL(EXP(base, k), PUSH factor), where len(factor) == 1
        else:
            if factor > 1:
                cost_without_diff = cost_base + cost_exponent + 4
                expression_without_diff = "MUL(EXP(" + expression_base + ", " + expression_exponent + "), PUSH " + hex(factor)[2:] + ")"
            else:
                cost_without_diff = cost_base + cost_exponent + 1
                expression_without_diff = "EXP(" + expression_base + ", " + expression_exponent + ")"

    else:
        cost_without_diff = remaining_bytes + 2


    if cost_without_diff < remaining_bytes:
        if current_diff == 0:
            if cost_without_diff < cost_best:
                cost_best = cost_without_diff
                expression_best = expression_without_diff
        else:
            cost_diff, expression_diff = build_best_configuration(current_diff, min(remaining_bytes - cost_without_diff,
                                                                                    bytes_associated_to_push(current_diff)), True)
            if cost_diff is not None and cost_diff + cost_without_diff < cost_best:
                cost_best = cost_diff + cost_without_diff + 1

                if is_addition:
                    expression_best = "ADD(" + expression_without_diff  + ", " + expression_diff + ")"
                else:
                    expression_best = "SUB(" + expression_without_diff  + ", " + expression_diff + ")"

    if cost_best <= remaining_bytes:
        return cost_best, expression_best
    else:
        return None, None

if __name__=="__main__":
    global args
    init()
    pathlib.Path(results_dir).mkdir(parents=True, exist_ok=True)

    count_integer = dict()
    reconstruct_integer = dict()
    big_numbers = dict()
    associated_cost = dict()
    associated_bytes = dict()

    total_blocks = 0
    for asm_file in glob.glob(contracts_dir_path + "*.json_solc"):
        asm_json = parse_asm(asm_file)
        for c in asm_json.getContracts():
            for identifier in c.getDataIds():
                blocks = c.getRunCodeOf(identifier)
                for block in blocks:
                    process_block(block, count_integer, reconstruct_integer, associated_cost, associated_bytes, big_numbers)

    df = pd.DataFrame([{"hexadecimal": hex(k), "decimal":k, "count":v, "expression": str(reconstruct_integer[k])} for k, v in
                       reversed(sorted(count_integer.items(), key=lambda kv: kv[1]))])
    df.to_csv(results_dir + "integer_constants.csv")

    current_rows = []
    i = 0
    for k, v in reversed(sorted(count_integer.items(), key=lambda kv: kv[1])):
        if bytes_associated_to_push(k) < 3:
            continue
        print(k)
        cost_best, expression_best = build_best_configuration(k, bytes_associated_to_push(k), False)
        if cost_best < min(associated_bytes[k]):
            current_rows.append({"hexadecimal": hex(k), "decimal": k, "current_cost": str(associated_bytes[k]), "cost_best" : cost_best,
                                 "expression": str(reconstruct_integer[k]), "expression_best": expression_best})
    df2 = pd.DataFrame(current_rows)
    df2.to_csv(results_dir + "pushed_values.csv")


    # df2 = pd.DataFrame([{"hexadecimal": hex(k), "decimal": k, "count": v, "factorization": str(factorize_with_timeout(k, v))} for k, v in
    #      reversed(sorted(big_numbers.items(), key=lambda kv: kv[1])) if v > 15])
    # df2.to_csv(results_dir + "pushed_values.csv")