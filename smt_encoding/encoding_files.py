import sys
import pathlib
import json
import os
sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/global_params")

from paths import smt_encoding_path

def init():

    global encoding_name
    encoding_name = "encoding.smt2"

    global instr_map_file
    instr_map_file = "instruction.json"

    global opcode_map_file
    opcode_map_file = "opcode.json"

    global gas_map_file
    gas_map_file = "gas.json"

    global encoding_stream
    encoding_stream = sys.stdout


def initialize_dir_and_streams(solver,source_name = None):
    global encoding_stream
    global encoding_name
    global instr_map_file
    global opcode_map_file
    global gas_map_file

    init()

    if source_name:
        name = source_name.split("/")[-1].rstrip(".json")
        encoding_name = name+"_"+solver+".smt2"
        instr_map_file = name + "_" + instr_map_file
        opcode_map_file = name + "_" + opcode_map_file
        gas_map_file = name + "_" + gas_map_file

    pathlib.Path(smt_encoding_path).mkdir(parents=True, exist_ok=True)
    encoding_stream = open(smt_encoding_path + encoding_name, 'w')

    return encoding_stream


def write_encoding(string):
    print(string, file=encoding_stream)


def close_encoding():
    sys.stdout.close()


def write_instruction_map(theta_instr):
    print(instr_map_file)
    with open(smt_encoding_path + instr_map_file, 'w') as f:
        f.write(json.dumps(theta_instr))


def write_opcode_map(instr_opcodes):
    with open(smt_encoding_path + opcode_map_file, 'w') as f:
        f.write(json.dumps(instr_opcodes))


def write_gas_map(gas_instr):
    with open(smt_encoding_path + gas_map_file, 'w') as f:
        f.write(json.dumps(gas_instr))