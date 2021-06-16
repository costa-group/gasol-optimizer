#!/usr/bin/python3
import re
import json
import collections
import pathlib


def init():
    global tmp_costabs
    tmp_costabs = "/tmp/gasol/"

    global instruction_json
    instruction_json = tmp_costabs + "smt_encoding/instruction.json"

    global opcodes_json
    opcodes_json = tmp_costabs + "smt_encoding/opcode.json"

    global gas_json
    gas_json = tmp_costabs + "smt_encoding/gas.json"

    global solution_file
    solution_file = tmp_costabs + "solution.txt"

    global instruction_final_solution
    instruction_final_solution = tmp_costabs + "optimized_block_instructions.disasm_opt"

    global opcodes_final_solution
    opcodes_final_solution = tmp_costabs + "optimized_block_opcodes.evm"

    global gas_final_solution
    gas_final_solution = tmp_costabs + "gas.txt"

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

    instruction_json = tmp_costabs+"smt_encoding/"+block_name+"_instruction.json"
    opcodes_json = tmp_costabs+"smt_encoding/"+block_name+"_opcode.json"
    gas_json = tmp_costabs+"smt_encoding/"+block_name+"_gas.json"

    instruction_final_solution = tmp_costabs+"solutions/" + contract_name + "/disasm/" + block_name + "_optimized.disasm_opt"
    opcodes_final_solution = tmp_costabs+"solutions/" + contract_name + "/evm/" + block_name+"_optimized.evm"
    gas_final_solution = tmp_costabs + "solutions/" + contract_name + "/total_gas/" + block_name + "_real_gas.txt"


# Generates three structures containing all the info from the solver: the sequence of instructions
# in plain text, the sequence of instructions converted to hexadecimal, the pushed values corresponding to push
# opcodes and an int that contains the gas cost of this solution.
def generate_info_from_solution(contract_name, block_name, solver_output):
    init()
    generate_file_names(contract_name, block_name)
    
    with open(opcodes_json, 'r') as path:
        opcodes_theta_dict = json.load(path)
    with open(instruction_json, 'r') as path:
        instruction_theta_dict = json.load(path)
    with open(gas_json, 'r') as path:
        gas_theta_dict = json.load(path)

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

    # We need to change PUSH instructions and opcode to the corresponding PUSHx version
    instr_sol = dict(map(lambda pair: change_instr_push_type(pair[0], pair[1], pushed_values_decimal.get(pair[0], 0)), instr_sol.items()))
    opcode_sol = dict(map(lambda pair: change_opcode_push_type(pair[0], pair[1], pushed_values_decimal.get(pair[0], 0)), opcode_sol.items()))

    # We order by position in the sequence in order to write them in the adequate order
    instr_sol = collections.OrderedDict(sorted(instr_sol.items(), key=lambda kv: kv[0]))
    opcode_sol = collections.OrderedDict(sorted(opcode_sol.items(), key=lambda kv: kv[0]))

    return instr_sol, opcode_sol, pushed_values_decimal, total_gas


def generate_disasm_sol(contract_name, block_name, solver_output):
    instr_sol, opcode_sol, pushed_values_decimal, total_gas = generate_info_from_solution(contract_name, block_name, solver_output)

    pathlib.Path(tmp_costabs+"solutions/" + contract_name + "/disasm/").mkdir(parents=True, exist_ok=True)
    pathlib.Path(tmp_costabs+"solutions/" + contract_name + "/evm/").mkdir(parents=True, exist_ok=True)
    pathlib.Path(tmp_costabs+"solutions/" + contract_name + "/total_gas/").mkdir(parents=True, exist_ok=True)


    with open(opcodes_final_solution, 'w') as opcodes_file:
        for position, opcode in opcode_sol.items():
            push_match = re.match(re.compile('PUSH([0-9]+)'), instr_sol[position])
            if push_match:
                opcodes_file.write(opcode + hex(int(pushed_values_decimal[position]))[2:])
            else:
                opcodes_file.write(opcode)
    with open(instruction_final_solution, 'w') as instruction_file:
        for position, instr in instr_sol.items():
            if re.match(re.compile('PUSH'), instr):
                instruction_file.write(instr + " " + pushed_values_decimal[position] + " ")
            else:
                instruction_file.write(instr + " ")

    with open(gas_final_solution, 'w') as gas_file:
        gas_file.write(str(total_gas))



if __name__ == "__main__":

    init()
    
    with open(opcodes_json, 'r') as path:
        opcodes_theta_dict = json.load(path)
    with open(instruction_json, 'r') as path:
        instruction_theta_dict = json.load(path)
    with open(gas_json, 'r') as path:
        gas_theta_dict = json.load(path)

    instr_sol = {}
    opcode_sol = {}
    pushed_values_decimal = {}

    pattern1 = re.compile("t_([0-9]*) ([0-9]*)")
    pattern2 = re.compile("a_([0-9]*) ([0-9]*)")

    total_gas = 0

    with open(solution_file, 'r') as sol_file:
        for line in sol_file:
            for match in re.finditer(pattern1, line):
                instruction_position = int(match.group(1))
                instruction_theta = match.group(2)
                # Nops are excluded
                if instruction_theta == '2':
                    break
                instr_sol[instruction_position] = instruction_theta_dict[instruction_theta]
                opcode_sol[instruction_position] = opcodes_theta_dict[instruction_theta]
                total_gas += gas_theta_dict[instruction_theta]

            for match in re.finditer(pattern2, line):
                instruction_position = int(match.group(1))
                pushed_value = match.group(2)
                pushed_values_decimal[instruction_position] = pushed_value

    # We need to change PUSH instructions and opcode to the corresponding PUSHx version
    instr_sol = dict(map(lambda pair: change_instr_push_type(pair[0], pair[1], pushed_values_decimal.get(pair[0], 0)), instr_sol.items()))
    opcode_sol = dict(map(lambda pair: change_opcode_push_type(pair[0], pair[1], pushed_values_decimal.get(pair[0], 0)), opcode_sol.items()))

    # We order by position in the sequence in order to write them in the adequate order
    instr_sol = collections.OrderedDict(sorted(instr_sol.items(), key=lambda kv: kv[0]))
    opcode_sol = collections.OrderedDict(sorted(opcode_sol.items(), key=lambda kv: kv[0]))

    with open(opcodes_final_solution, 'w') as opcodes_file:
        for position, opcode in opcode_sol.items():
            push_match = re.match(re.compile('PUSH([0-9]*)'), instr_sol[position])
            if push_match:
                opcodes_file.write(opcode + hex(int(pushed_values_decimal[position]))[2:])
            else:
                opcodes_file.write(opcode)
    with open(instruction_final_solution, 'w') as instruction_file:
        for position, instr in instr_sol.items():
            if re.match(re.compile('PUSH'), instr):
                instruction_file.write(instr + " " + pushed_values_decimal[position] + " ")
            else:
                instruction_file.write(instr + " ")
    with open(gas_final_solution, 'w') as gas_file:
        gas_file.write(str(total_gas))