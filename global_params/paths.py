import os
import uuid

tmp_path = "/tmp/"
gasol_folder = "gasol_" + uuid.uuid4().hex
gasol_path = tmp_path + gasol_folder + "/"
json_path =  gasol_path + "jsons"
smt_encoding_path = gasol_path +"smt_encoding/"
solutions_path = gasol_path +"solutions/"
dot_path = gasol_path + "dot/"

project_path = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))

gasol_exec = project_path + "/gasol_asm.py"

z3_exec = project_path + "/bin/z3"

bclt_exec = project_path + "/bin/barcelogic"

oms_exec = project_path + "/bin/optimathsat"

csv_file = gasol_path + "solutions/statistics.csv"