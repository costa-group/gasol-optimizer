#!/usr/bin/python3
import re
import json
import collections
import pathlib

from global_params.paths import gasol_path
from sfs_generator.asm_bytecode import AsmBytecode

def init():
    global instruction_json
    instruction_json = gasol_path + "smt_encoding/instruction.json"

    global opcodes_json
    opcodes_json = gasol_path + "smt_encoding/opcode.json"

    global gas_json
    gas_json = gasol_path + "smt_encoding/gas.json"

    global solution_file
    solution_file = gasol_path + "solution.txt"

    global instruction_final_solution
    instruction_final_solution = gasol_path + "optimized_block_instructions.disasm_opt"

    global opcodes_final_solution
    opcodes_final_solution = gasol_path + "optimized_block_opcodes.evm"

    global gas_final_solution
    gas_final_solution = gasol_path + "gas.txt"

# Push is determined by the number of bytes of pushed value
def decide_push_type(elem):
    return (len(bin(int(elem))[2:]) - 1) // 8 + 1


def change_instr_push_type(position, instr, pushed_value):
    if instr == "PUSH":
        push_type = decide_push_type(pushed_value)
        return position, "PUSH" + str(push_type)
    return position, instr


def change_opcode_push_type(position, opcode, pushed_value):
    # Opcode 60 corresponds to PUSH (in fact, to PUSH1, but we use
    # that value in general)
    if opcode == "60":
        hex_pushed_value = hex(int(pushed_value))[2:]
        push_type = decide_push_type(pushed_value)
        # Convert 59 hex number to decimal, add the length of the pushed value to
        # obtain the corresponding value, transform it again to hex and append the pushed value also in hex
        return position, hex(int("59",16) + int(str(push_type), 16))[2:] + hex_pushed_value
    return position, opcode


def generate_file_names(contract_name, block_name):
    global instruction_json
    global opcodes_json
    global gas_json
    global instruction_final_solution
    global opcodes_final_solution
    global gas_final_solution

    instruction_json = gasol_path+"smt_encoding/"+block_name+"_instruction.json"
    opcodes_json = gasol_path+"smt_encoding/"+block_name+"_opcode.json"
    gas_json = gasol_path+"smt_encoding/"+block_name+"_gas.json"

    instruction_final_solution = gasol_path+"solutions/" + contract_name + "/disasm/" + block_name + "_optimized.disasm_opt"
    opcodes_final_solution = gasol_path+"solutions/" + contract_name + "/evm/" + block_name+"_optimized.evm"
    gas_final_solution = gasol_path + "solutions/" + contract_name + "/total_gas/" + block_name + "_real_gas.txt"


# Given the sequence of instructions in disassembly format, in opcode format and the pushed values, returns
# the same sequences well ordered and with the corresponding PUSHx value.
def generate_ordered_structures(instr_sol, opcode_sol, pushed_values_decimal):

    # We need to change PUSH instructions and opcode to the corresponding PUSHx version
    instr_sol = dict(map(lambda pair: change_instr_push_type(pair[0], pair[1], pushed_values_decimal.get(pair[0], 0)), instr_sol.items()))
    opcode_sol = dict(map(lambda pair: change_opcode_push_type(pair[0], pair[1], pushed_values_decimal.get(pair[0], 0)), opcode_sol.items()))

    # We order by position in the sequence in order to write them in the adequate order
    instr_sol = collections.OrderedDict(sorted(instr_sol.items(), key=lambda kv: kv[0]))
    opcode_sol = collections.OrderedDict(sorted(opcode_sol.items(), key=lambda kv: kv[0]))

    return instr_sol, opcode_sol, pushed_values_decimal


# Following the exchange format used when generating the encoding, this method reads the corresponding files
# that contain three dicts: for disassembly, for opcodes and for gas cost.
def read_initial_dicts_from_files(contract_name, block_name):
    init()
    generate_file_names(contract_name, block_name)

    with open(opcodes_json, 'r') as path:
        opcodes_theta_dict = json.load(path)
    with open(instruction_json, 'r') as path:
        instruction_theta_dict = json.load(path)
    with open(gas_json, 'r') as path:
        gas_theta_dict = json.load(path)
    return opcodes_theta_dict, instruction_theta_dict, gas_theta_dict


# Generates three structures containing all the info from the solver: the sequence of instructions
# in plain text, the sequence of instructions converted to hexadecimal, the pushed values corresponding to push
# opcodes and an int that contains the gas cost of this solution.
def generate_info_from_solution(solver_output, opcodes_theta_dict, instruction_theta_dict, gas_theta_dict):
    instr_sol = {}
    opcode_sol = {}
    pushed_values_decimal = {}

    pattern1 = re.compile("t_([0-9]*) ([0-9]*)")
    pattern2 = re.compile("a_([0-9]*) ([0-9]*)")

    total_gas = 0

    for line in solver_output.splitlines():
        for match in re.finditer(pattern1, line):
            instruction_position = int(match.group(1))
            instruction_theta = match.group(2)
                # Nops are excluded. theta(NOP) = 2
            if instruction_theta == '2':
                break
            instr_sol[instruction_position] = instruction_theta_dict[instruction_theta]
            opcode_sol[instruction_position] = opcodes_theta_dict[instruction_theta]
            total_gas += gas_theta_dict[instruction_theta]

        for match in re.finditer(pattern2, line):
            instruction_position = int(match.group(1))
            pushed_value = match.group(2)
            pushed_values_decimal[instruction_position] = pushed_value

    instr_sol, opcode_sol, pushed_values_decimal = generate_ordered_structures(instr_sol, opcode_sol, pushed_values_decimal)
    return instr_sol, opcode_sol, pushed_values_decimal, total_gas


def generate_disasm_sol_from_output(contract_name, solver_output,
                                    opcodes_theta_dict, instruction_theta_dict, gas_theta_dict):
    init()
    instr_sol, opcode_sol, pushed_values_decimal, total_gas = \
        generate_info_from_solution(solver_output, opcodes_theta_dict, instruction_theta_dict, gas_theta_dict)

    pathlib.Path(gasol_path+"solutions/" + contract_name + "/disasm/").mkdir(parents=True, exist_ok=True)
    pathlib.Path(gasol_path+"solutions/" + contract_name + "/evm/").mkdir(parents=True, exist_ok=True)
    pathlib.Path(gasol_path+"solutions/" + contract_name + "/total_gas/").mkdir(parents=True, exist_ok=True)


    opcode_list = []
    evm_list = []
    
    with open(opcodes_final_solution, 'w') as opcodes_file:
        for position, opcode in opcode_sol.items():
            push_match = re.match(re.compile('PUSH([0-9]+)'), instr_sol[position])
            if push_match:
                val2write = opcode + hex(int(pushed_values_decimal[position]))[2:]
                opcodes_file.write(val2write)
                evm_list.append(val2write)
            else:
                opcodes_file.write(opcode)
                evm_list.append(opcode)
                
    with open(instruction_final_solution, 'w') as instruction_file:
        for position, instr in instr_sol.items():
            if re.match(re.compile('PUSH([0-9]+)'), instr):
                val2write = instr + " " + pushed_values_decimal[position] + " "
                instruction_file.write(val2write)
                opcode_list.append(val2write)
            else:
                instruction_file.write(instr + " ")
                opcode_list.append(instr + " ")
                
    with open(gas_final_solution, 'w') as gas_file:
        gas_file.write(str(total_gas))

    return opcode_list

# Generates three structures containing all the info from the solver: the sequence of instructions
# in plain text, the sequence of instructions converted to hexadecimal, the pushed values corresponding to push
# opcodes and an int that contains the gas cost of this solution.
def generate_info_from_sequence(instr_sequence, opcodes_theta_dict,
                                instruction_theta_dict, gas_theta_dict):
    instr_sol = {}
    opcode_sol = {}
    pushed_values_decimal = {}

    total_gas = 0

    for instruction_position, sequence_elem in enumerate(instr_sequence):
        # If sequence_elem > 0, then the sequence element represents a theta value.
        if sequence_elem > 0:
            # Nops are excluded. theta(NOP) = 2
            sequence_elem = sequence_elem
            if sequence_elem == 2:
                break
            instr_sol[instruction_position] = instruction_theta_dict[sequence_elem]
            opcode_sol[instruction_position] = opcodes_theta_dict[sequence_elem]
            total_gas += gas_theta_dict[sequence_elem]
        # Otherwise, it represents a theta value
        else:
            instr_sol[instruction_position] = "PUSH"
            opcode_sol[instruction_position] = "60"
            pushed_values_decimal[instruction_position] = -sequence_elem
            total_gas += 3

    instr_sol, opcode_sol, pushed_values_decimal = generate_ordered_structures(instr_sol, opcode_sol,
                                                                               pushed_values_decimal)
    return instr_sol, opcode_sol, pushed_values_decimal, total_gas


# Generates a sequence of instructions following the convention used in this module.
# This sequence is generated from the sequence of instruction, pushed values, and the theta dict.
def obtain_log_representation_from_solution(opcodes, pushed_values, theta_dict):
    i, j = 0,0
    instr_seq = []
    while i < len(opcodes):
        if opcodes[i] == "PUSH":
            instr_seq.append(-pushed_values[j])
            j += 1
        # If we have a push that is not PUSHDEPLOYADDRESS, ASSIGNIMMUTABLE nor PUSHSIZE, then we need to
        # "consume" the pushed value from the list of pushed values.
        elif opcodes[i].startswith("PUSH") and not opcodes[i].startswith("PUSHDEPLOYADDRESS") \
                and not opcodes[i].startswith("ASSIGNIMMUTABLE") and not opcodes[i].startswith("PUSHSIZE") :
            instr_seq.append(theta_dict[opcodes[i]])
            j += 1
        else:
            instr_seq.append(theta_dict[opcodes[i]])
        i += 1
    return instr_seq


# Given a sequence of instructions and the corresponding dicts, writes the final solution in the corresponding folders.
def generate_disasm_sol_from_log_block(contract_name, block_name, instr_sequence,
                                       opcodes_theta_dict, instruction_theta_dict, gas_theta_dict):
    init()
    generate_file_names(contract_name, block_name)
    instr_sol, opcode_sol, pushed_values_decimal, total_gas = \
        generate_info_from_sequence(instr_sequence, opcodes_theta_dict, instruction_theta_dict, gas_theta_dict)

    pathlib.Path(gasol_path + "solutions/" + contract_name + "/disasm/").mkdir(parents=True, exist_ok=True)
    pathlib.Path(gasol_path + "solutions/" + contract_name + "/evm/").mkdir(parents=True, exist_ok=True)
    pathlib.Path(gasol_path + "solutions/" + contract_name + "/total_gas/").mkdir(parents=True, exist_ok=True)

    opcode_list = []
    evm_list = []

    with open(opcodes_final_solution, 'w') as opcodes_file:
        for position, opcode in opcode_sol.items():
            push_match = re.match(re.compile('PUSH([0-9]+)'), instr_sol[position])
            if push_match:
                val2write = opcode + hex(int(pushed_values_decimal[position]))[2:]
                opcodes_file.write(val2write)
                evm_list.append(val2write)
            else:
                opcodes_file.write(opcode)
                evm_list.append(opcode)

    with open(instruction_final_solution, 'w') as instruction_file:
        for position, instr in instr_sol.items():
            if re.match(re.compile('PUSH([0-9]+)'), instr):
                val2write = instr + " " + str(pushed_values_decimal[position]) + " "
                instruction_file.write(val2write)
                opcode_list.append(val2write)
            else:
                instruction_file.write(instr + " ")
                opcode_list.append(instr + " ")

    with open(gas_final_solution, 'w') as gas_file:
        gas_file.write(str(total_gas))

    return opcode_list


# Given the user instructions and the theta dict, generates a dict with the values associated
# to "uninterpreted" PUSH instructions (PUSH data, PUSH[$] ...) linked to the corresponding instruction id
def obtain_push_values_dict_from_uninterpreted_push(user_instr):
    theta_uninterpreted_push_dict = {}

    for instr in user_instr:
        id = instr['id']
        value = instr.get('value', None)
        if value is not None:
            theta_uninterpreted_push_dict[id] = value

    return theta_uninterpreted_push_dict

# Given the output obtained from executing the corresponding SMT solver and the corresponding dicts, it generates
# the optimized sub-block following the AsmBytecode format.
def generate_sub_block_asm_representation_from_output(solver_output, opcodes_theta_dict, instruction_theta_dict,
                                                      gas_theta_dict, values_dict):

    sub_block_instructions_asm = []

    instr_sol, _, pushed_values_decimal, _ = \
        generate_info_from_solution(solver_output, opcodes_theta_dict, instruction_theta_dict, gas_theta_dict)
    for position, instr in instr_sol.items():

        # Push match refers to usual PUSH instructions that are introduced as basic operations
        push_match = re.match(re.compile('PUSH([0-9]+)'), instr)

        # Basic stack instructions refer to those instruction that only manage the stack: SWAPk, POP or DUPk.
        # These instructions just initialize each field in the asm format to -1
        basic_stack_instr_match = re.match(re.compile('SWAP|POP|DUP'), instr)
        if push_match:
            value = hex(int(pushed_values_decimal[position]))[2:]
            sub_block_instructions_asm.append(AsmBytecode(-1,-1,-1,"PUSH",value))
        elif basic_stack_instr_match:
            sub_block_instructions_asm.append(AsmBytecode(-1,-1,-1,instr,None))
        else:
            # TODO: Add information retrieval from uninterpreted functions
            value = values_dict.get(instr, None)
            sub_block_instructions_asm.append(AsmBytecode(-1,-1,-1,instr, value))
    return sub_block_instructions_asm
