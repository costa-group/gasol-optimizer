import shlex
import subprocess
from global_params.paths import *
import re
import resource

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
        return z3_exec + " -smt2 " + smt_file
    elif solver == "barcelogic":
        if tout is None:
            return bclt_exec + " -file " + smt_file
        else:
            return bclt_exec + " -file " + smt_file + " -tlimit " + str(tout)
    else:
        return oms_exec + " " + smt_file


# Calls syrup and computes the solution. Returns the raw output from the corresponding solver
def generate_solution(block_name, solver, tout):
    # encoding_file = encoding_path+"encoding_Z3.smt2"
    encoding_file = smt_encoding_path + block_name + "_" + solver + ".smt2"

    exec_command = get_solver_to_execute(encoding_file, solver, tout)

    print("Executing " + solver + " for file " + block_name)
    solution, solver_time = run_and_measure_command(exec_command)

    return solution, solver_time


def obtain_solver_output(block_name, solver, tout):
    return generate_solution(block_name, solver, tout)


def analyze_file_oms(solution):
    pattern = re.compile("\(gas (.*)\)")
    for match in re.finditer(pattern, solution):
        number = int(match.group(1))
        pattern2 = re.compile("range")
        if re.search(pattern2, solution):
            return number, False
        return number, True


def submatch_z3(string):
    subpattern = re.compile("\(interval (.*) (.*)\)")
    for submatch in re.finditer(subpattern, string):
        return int(submatch.group(2))
    return -1


def analyze_file_z3(solution):
    pattern = re.compile("\(gas (.*)\)")
    for match in re.finditer(pattern, solution):
        number = submatch_z3(match.group(1))
        if number == -1:
            return int(match.group(1)), True
        else:
            return number, False


def submatch_barcelogic(string):
    subpattern = re.compile("\(cost (.*)\)")
    for submatch in re.finditer(subpattern, string):
        return int(submatch.group(1))
    return -1


def analyze_file_barcelogic(solution):
    pattern = re.compile("\(optimal (.*)\)")
    for match in re.finditer(pattern, solution):
        return int(match.group(1)), True
    return submatch_barcelogic(solution), False


def analyze_file(solution, solver):
    if solver == "oms":
        return analyze_file_oms(solution)
    elif solver == "z3":
        return analyze_file_z3(solution)
    else:
        return analyze_file_barcelogic(solution)