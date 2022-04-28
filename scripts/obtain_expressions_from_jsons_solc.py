#!/usr/bin/python3
import argparse
import glob
import json
import os
import pathlib
import re
import resource
import shlex
import subprocess
import sys

import pandas as pd

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/global_params")
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/sfs_generator")
from paths import (bclt_exec, gasol_path, json_path, oms_exec, project_path,
                   smt_encoding_path, solutions_path, z3_exec)
from utils import compute_stack_size

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/smt_encoding")
from encoding_utils import generate_phi_dict
from gasol_encoder import execute_syrup_backend

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/verification")
from sfs_verify import are_equals

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/scripts")
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/solution_generation")
import ir_block
from disasm_generation import generate_disasm_sol
from gasol_optimization import get_sfs_dict

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))
from gasol_asm import preprocess_instructions_plain_text


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


def init():
    modifiable_path_files_init()


def update_integer_values(user_instr, final_stack, integer_values):
    idx = 0
    for instr in user_instr:
        for elem in instr['inpt_sk']:
            if type(elem) == int:
                integer_values[elem] = integer_values.get(elem, 0) + 1
                idx += 1
    for elem in final_stack:
        if type(elem) == int:
            integer_values[elem] = integer_values.get(elem, 0) + 1
            idx += 1


if __name__=="__main__":
    global args
    init()
    pathlib.Path(gasol_path).mkdir(parents=True, exist_ok=True)
    pathlib.Path(results_dir).mkdir(parents=True, exist_ok=True)

    integer_values = dict()
    total_blocks = 0
    for contract_path in [f.path for f in os.scandir(contracts_dir_path) if f.is_dir()]:
        rows_list = []
        log_dict = dict()
        contract_name = contract_path.split('/')[-1]


        for file in glob.glob(contract_path + "/*.json"):
            total_blocks += 1
            with open(file) as path:
                data = json.load(path)
                bs = data['max_sk_sz']
                user_instr = data['user_instrs']
                final_stack = data['tgt_ws']
                update_integer_values(user_instr, final_stack, integer_values)

    df = pd.DataFrame([{"hexadecimal": hex(k), "decimal":k, "count":v} for k, v in reversed(sorted(integer_values.items(), key=lambda kv: kv[1]))])
    df.to_csv(results_dir + "pushed_values.csv")

    print(str(total_blocks) + " blocks have been analyzed")