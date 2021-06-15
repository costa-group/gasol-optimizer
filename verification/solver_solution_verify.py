import re


# Given a sequence of theta opcodes tj and the corresponding aj, generates a dict for storing
# the important info. In case tj = 0, then current instruction is a push and we store -aj. Otherwise, we
# store tj. This way, we identify with strictly positive numbers the theta values, and with 0 or negative
# the pushed ones (as aj >= 0).
def generate_dict_with_instructions(theta_sequence, pushed_values):
    json_dict = []
    ordered_theta_sequence = {k: v for k, v in sorted(theta_sequence.items(), key=lambda item: item[0])}
    for pos, theta_value in ordered_theta_sequence.items():
        # 0 is theta("PUSH") see generate_stack_theta in encoding_utils
        if theta_value == 0:
            aj = int(pushed_values[pos])
            json_dict.append(-aj)
        else:
            json_dict.append(theta_value)

        # 2 == theta("NOP")
        # As soon as we find the first nop, we return the sequence
        if theta_value == 2:
            return json_dict
    return json_dict


# Generates a dict containing info to transform into a json
def generate_solution_dict(solver_output):
    pushed_values_decimal = {}
    theta_sol = {}
    pattern1 = re.compile("t_([0-9]*) ([0-9]*)")
    pattern2 = re.compile("a_([0-9]*) ([-]*[0-9]*)")

    for line in solver_output.splitlines():
        for match in re.finditer(pattern1, line):
            instruction_position = int(match.group(1))
            instruction_theta = match.group(2)
            theta_sol[instruction_position] = int(instruction_theta)

        for match in re.finditer(pattern2, line):
            instruction_position = int(match.group(1))
            pushed_value = match.group(2)
            pushed_values_decimal[instruction_position] = pushed_value
    return generate_dict_with_instructions(theta_sol, pushed_values_decimal)


def check_solver_output_is_correct(solver_output):
    # Sat for OMS, Z3 and optimal for barcelogic.
    pattern1 = re.compile("sat|optimal")
    for line in solver_output.splitlines():
        for _ in re.finditer(pattern1, line):
            return True
    return False
