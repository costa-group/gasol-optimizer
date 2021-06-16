import os
import shlex
import subprocess

def init():
    global project_path
    project_path = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))

    global tmp_costabs
    tmp_costabs = "/tmp/gasol/"

    global encoding_path
    encoding_path = tmp_costabs + "smt_encoding/"

    global z3_exec
    z3_exec = project_path + "/bin/z3"

    global bclt_exec
    bclt_exec = project_path + "/bin/barcelogic"

    global oms_exec
    oms_exec = project_path + "/bin/optimathsat"


def run_command(cmd):
    FNULL = open(os.devnull, 'w')
    solc_p = subprocess.Popen(shlex.split(cmd), stdout=subprocess.PIPE,
                              stderr=FNULL)
    return solc_p.communicate()[0].decode()


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
    encoding_file = encoding_path + block_name + "_" + solver + ".smt2"

    exec_command = get_solver_to_execute(encoding_file, solver, tout)

    print("Executing " + solver + " for file " + block_name)
    solution = run_command(exec_command)

    return solution


def obtain_solver_output(block_name, solver, tout):
    init()
    return generate_solution(block_name, solver, tout)