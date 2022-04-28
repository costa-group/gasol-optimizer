import os
import re
import resource
import shlex
import subprocess

import global_params.paths as paths


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


def get_solver_to_execute(smt_file, solver, tout):
    if solver == "z3":
        return paths.z3_exec + " -smt2 " + smt_file
    elif solver == "barcelogic":
        if tout is None:
            return paths.bclt_exec + " -file " + smt_file
        else:
            return paths.bclt_exec + " -file " + smt_file + " -tlimit " + str(tout)
    else:
        return paths.oms_exec + " " + smt_file + " -optimization=True"


# Calls syrup and computes the solution. Returns the raw output from the corresponding solver
def generate_solution(block_name, solver, tout):
    # encoding_file = encoding_path+"encoding_Z3.smt2"
    encoding_file = paths.smt_encoding_path + block_name + "_" + solver + ".smt2"

    exec_command = get_solver_to_execute(encoding_file, solver, tout)

    print("Executing " + solver + " for file " + block_name)
    solution, solver_time = run_and_measure_command(exec_command)

    return solution, solver_time


def obtain_solver_output(block_name, solver, tout):
    return generate_solution(block_name, solver, tout)