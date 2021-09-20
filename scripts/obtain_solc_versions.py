#!/usr/bin/env python3
import os
import sys
sys.path.append("../")
import glob
import pathlib
import subprocess
import shlex
from global_params.paths import project_path

parent_directory = project_path + "/examples/solidity"
normal_directory = project_path + "/examples/jsons_solc_normal"
noyul_directory = project_path + "/examples/jsons_solc_noyul"
opt_directory = project_path + "/examples/jsons_solc_opt"

normal_flags = " "
noyul_flags = " --optimize --no-optimize-yul "
opt_flags = " --optimize "

def run_command(cmd):
    FNULL = open(os.devnull, 'w')
    solc_p = subprocess.Popen(shlex.split(cmd), stdout=subprocess.PIPE,
                              stderr=FNULL)
    return solc_p.communicate()[0].decode()


if __name__ == "__main__":

    pathlib.Path(normal_directory).mkdir(parents=True, exist_ok=True)

    pathlib.Path(noyul_directory).mkdir(parents=True, exist_ok=True)

    pathlib.Path(opt_directory).mkdir(parents=True, exist_ok=True)

    for sol_file in glob.glob(parent_directory + "/*.sol"):
        
        name = sol_file.split("/")[-1].rstrip(".sol")
        normal_version = run_command("solc --combined-json asm " + normal_flags + " " + sol_file)
        noyul_version = run_command("solc --combined-json asm " + noyul_flags + " " + sol_file)
        opt_version = run_command("solc --combined-json asm " + opt_flags + " " + sol_file)

        final_name = name + ".json_solc"

        with open(normal_directory + "/" + final_name, 'w') as f:
            f.write(normal_version)
        
        with open(noyul_directory + "/" + final_name, 'w') as f:
            f.write(noyul_version)

        with open(opt_directory + "/" + final_name, 'w') as f:
            f.write(opt_version)

