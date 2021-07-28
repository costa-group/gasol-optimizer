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
            run_command(gasol_exec + " " + asm_json + " -log ")
            sol_output = run_command(gasol_exec + " " + asm_json + " " + "-optimize-gasol-from-log-file " +
                                     gasol_path + contract_name + ".log")
            _, oms_time = run_and_measure_command(oms_exec + " " + smt_encoding_path + "verify_oms.smt2")

            if re.search("Solution generated from log file has been verified correctly", sol_output):
                csv_row['log_verified'] = True
            else:
                csv_row['log_verified'] = False

            csv_row['oms_time'] = round(oms_time, 3)

            csv_row['log_size'] = os.path.getsize(log_file)
            csv_row['correct'] = True
        except:
            csv_row['correct'] = False

        row_list.append(csv_row)
    df = pd.DataFrame(row_list, columns=['name', 'log_size', 'oms_time', 'log_verified', 'correct'])
    csv_file = final_directory + "log_comparison.csv"
    df.to_csv(csv_file)
