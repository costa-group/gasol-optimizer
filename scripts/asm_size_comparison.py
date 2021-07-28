#!/usr/bin/env python3
import os
import sys
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))
import glob
import pathlib
import pandas as pd
import subprocess
import shlex
import resource
from global_params.paths import gasol_exec, log_file, oms_exec, project_path, smt_encoding_path, gasol_path
from sfs_generator.parser_asm import parse_asm
from sfs_generator.utils import compute_number_of_instructions_in_asm_json_per_file
import re

parent_directory = project_path + "/examples/prueba"
final_directory = project_path + "/results/"

def run_command(cmd):
    FNULL = open(os.devnull, 'w')
    solc_p = subprocess.Popen(shlex.split(cmd), stdout=subprocess.PIPE,
                              stderr=FNULL)
    return solc_p.communicate()[0].decode()


def run_and_measure_command(cmd):
    usage_start = resource.getrusage(resource.RUSAGE_CHILDREN)
    solution = run_command(cmd)
    usage_stop = resource.getrusage(resource.RUSAGE_CHILDREN)
    return solution, usage_stop.ru_utime + usage_stop.ru_stime - usage_start.ru_utime - usage_start.ru_stime

if __name__ == "__main__":

    pathlib.Path(final_directory).mkdir(parents=True, exist_ok=True)

    row_list = []
    for asm_json in glob.glob(parent_directory + "/*.json_solc"):
        contract_name = asm_json.split("/")[-1].rstrip(".json_solc")
        csv_row = {'name': contract_name}
        try:
            solution_output, total_time = run_and_measure_command(gasol_exec + " " + asm_json)

            if re.search("Optimized bytecode has been checked successfully", solution_output):
                csv_row['verified_correctly'] = True
            else:
                csv_row['verified_correctly'] = False

            csv_row['total_time'] = round(total_time, 3)
            old_asm = parse_asm(asm_json)
            new_asm = parse_asm(contract_name + "_optimized.json_solc")
            csv_row['old_size'] = compute_number_of_instructions_in_asm_json_per_file(old_asm)
            csv_row['new_size'] = compute_number_of_instructions_in_asm_json_per_file(new_asm)
            csv_row['size_relation'] = round( 100*(1 - csv_row['new_size'] / csv_row['old_size']), 3)
            csv_row['correct'] = True
        except:
            csv_row['correct'] = False

        row_list.append(csv_row)
    df = pd.DataFrame(row_list, columns=['name', 'verified_correctly', 'total_time', 'old_size',
                                         'new_size', 'size_relation', 'correct'])

    csv_file = final_directory + "size_comparison.csv"
    df.to_csv(csv_file)
