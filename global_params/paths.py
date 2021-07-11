import os

tmp_path = "/tmp/"
gasol_path = tmp_path + "gasol/"
gasol_folder = "gasol"
json_path =  gasol_path + "jsons"
smt_encoding_path = gasol_path +"smt_encoding/"

project_path = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))

gasol_exec = project_path + "/gasol_asm.py"

z3_exec = project_path + "/bin/z3"

bclt_exec = project_path + "/bin/barcelogic"

oms_exec = project_path + "/bin/optimathsat"

log_file = gasol_path + "verification.log"

csv_file = gasol_path + "solutions/statistics.csv"