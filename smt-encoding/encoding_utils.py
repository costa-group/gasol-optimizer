# Module that contains parameter declarations and
# other auxiliary methods to generate the encoding

from smtlib_utils import *
from collections import OrderedDict
import re

# We set the maximum k dup and swap instructions
# can have.

max_k_dup = 16
max_k_swap = 16

# Maximum size integers have in the EVM

int_limit = 2**256

# Methods for generating string corresponding to
# variables we will be using for the encoding


def u(i,j):
    return var2str("u", i,j)


def x(i,j):
    return var2str("x", i, j)


def t(i):
    return var2str('t', i)


def a(i):
    return var2str('a', i)

# Auxiliary methods for defining the constraints

def move(j, alpha, beta, delta):
    and_variables = []

    # Move can be empty
    if alpha > beta:
        return "true"
    for i in range(alpha, beta+1):
        first_and = add_eq(u(i+delta, j+1), u(i,j))
        second_and = add_eq(x(i+delta, j+1), x(i,j))
        and_variables.append(add_and(first_and, second_and))
    return add_and(*and_variables)


def generate_stack_theta(bs):
    theta = {"PUSH": 0, "POP": 1, "NOP": 2}
    initial_index = 3
    for i in range(1, min(bs, max_k_dup+1)):
        theta["DUP" + str(i)] = initial_index
        initial_index += 1
    for i in range(1, min(bs, max_k_swap+1)):
        theta["SWAP" + str(i)] = initial_index
        initial_index += 1
    return theta


# Returns two different dictionaries: the first one, for
# commutative functions and the second one for
# non-commutative functions
def generate_uninterpreted_theta(user_instr, initial_index):
    theta_comm = {}
    theta_non_comm = {}
    for instr in user_instr:
        if instr['commutative']:
            theta_comm[instr['id']] = initial_index
        else:
            theta_non_comm[instr['id']] = initial_index
        initial_index += 1
    return theta_comm, theta_non_comm


# Separates user instructions in two groups, according to whether they
# are commutative or not.
def separe_usr_instr(user_instr):
    comm_functions = []
    non_comm_functions = []
    for instr in user_instr:
        if instr['commutative']:
            comm_functions.append(instr)
        else:
            non_comm_functions.append(instr)
    return comm_functions, non_comm_functions


# Generates an ordered dict that contains all instructions associated value of theta
# as keys, and their gas cost as values. Ordered by increasing costs
def generate_costs_ordered_dict(bs, user_instr, theta_dict):
    instr_costs = {theta_dict["PUSH"]: 3, theta_dict["POP"]: 2, theta_dict["NOP"]: 0}
    for i in range(1, min(bs, max_k_dup + 1)):
        instr_costs[theta_dict["DUP" + str(i)]] = 3
    for i in range(1, min(bs, max_k_swap + 1)):
        instr_costs[theta_dict["SWAP" + str(i)]] = 3
    for instr in user_instr:
        instr_costs[theta_dict[instr['id']]] = instr['gas']
    return OrderedDict(sorted(instr_costs.items(), key=lambda t: t[1]))


# Generates an ordered dict that has the cost of Wp sets as keys
# and the theta value of opcodes with that cost as values.
# Ordered by increasing costs
def generate_disjoint_sets_from_cost(ordered_costs):
    disjoint_set = {}
    for id in ordered_costs:
        gas_cost = ordered_costs[id]
        if gas_cost in disjoint_set:
            disjoint_set[gas_cost].append(id)
        else:
            disjoint_set[gas_cost] = [id]
    return OrderedDict(sorted(disjoint_set.items(), key=lambda t: t[0]))


# Given a instruction, a dict that links each instruction to a lower bound to the number of instructions
# # needed to obtain the output from that dict, and another dict
# that links each instruction to the previous instructions needed to execute that instruction,
# updates both dicts for that instruction and returns the corresponding values associated to the instruction.
def generate_instr_dependencies(instr, number_of_instructions_to_execute, previous_values, dependency_theta_graph):

    # Base case: it has been already analyzed, so we return the values associated.
    if instr in previous_values:
        return number_of_instructions_to_execute[instr], previous_values[instr]

    # Base case: if the instruction is a push, it doesn't have any previous instruction, so
    # it needs 0 instructions and doesn't have any dependency.
    if instr == 'PUSH':
        return 0, set()

    number_of_instructions_needed = 0
    instructions_dependency = set()

    # Recursive case: we obtain the output for each previous instruction and update the values
    for previous_instr, aj in dependency_theta_graph[instr]:

        previous_number_of_instr_needed, previous_instructions_dependency = \
            generate_instr_dependencies(previous_instr, number_of_instructions_to_execute,
                                        previous_values, dependency_theta_graph)
        # We need the number of instructions needed for previous instruction plus one (executing that instruction)
        number_of_instructions_needed += previous_number_of_instr_needed + 1

        # We ignore push instructions from this point, as they don't add any info
        if previous_instr == 'PUSH':
            continue

        # We need to add previous instruction to its associated values, as it wasn't added yet
        previous_instructions = previous_instructions_dependency | {previous_instr}

        # See detailed explanation for more information to understand this step
        repeated_instructions = instructions_dependency.intersection(previous_instructions)

        # Maximal elements are those that don't appear as a previous instruction for any of the repeated instructions
        maximal_elements = repeated_instructions.difference(set().union(*[previous_values[repeated_instr]
                                                                          for repeated_instr in repeated_instructions]))
        for repeated_instr in maximal_elements:

            # If it is the maximal representative, then the necessary number of previous instructions is 0
            # (as it could have been duplicated)
            number_of_instructions_needed -= number_of_instructions_to_execute[repeated_instr]

        # We update instructions_dependency
        instructions_dependency = instructions_dependency.union(previous_instructions)

    number_of_instructions_to_execute[instr] = number_of_instructions_needed
    previous_values[instr] = instructions_dependency

    # print(instr, ":", previous_values)

    return number_of_instructions_needed, instructions_dependency


# Given the dict containing the dependency among different instructions, we generate
# another dict that links each instruction to the number of instructions that must be
# executed previously to be able to execute that instruction.
def generate_number_of_previous_instr_dict(dependency_theta_graph):
    previous_values = {}
    number_of_instructions_to_execute = {'PUSH': 0}
    for instr in dependency_theta_graph:
        generate_instr_dependencies(instr, number_of_instructions_to_execute, previous_values, dependency_theta_graph)

    return number_of_instructions_to_execute


# First time an instruction cannot appear is b0-h, where h is the tree height. We recursively obtain this value,
# taking into account that we may have different trees and the final value is the min for all possible ones
def update_with_tree_level(b0, dependency_theta_graph, current_idx, instr, first_position_instr_cannot_appear):
    # We don't consider push instructions
    if instr == 'PUSH':
        return
    first_position_instr_cannot_appear[instr] = min(current_idx, first_position_instr_cannot_appear.get(instr, b0))
    for prev_instr, _ in dependency_theta_graph[instr]:
        update_with_tree_level(b0, dependency_theta_graph, current_idx-1, prev_instr, first_position_instr_cannot_appear)


# Generates a dict that given b0, returns the first position in which a instruction cannot appear
# due to dependencies with other instructions.
def generate_first_position_instr_cannot_appear(b0, final_stack_instr, dependency_graph, top_elem_is_instruction):
    first_position_instr_cannot_appear = {'PUSH': b0}

    # We consider instructions in the final stack, as they determine which position is the last possible one (following
    # the dependencies to reach it). We are assuming each other instruction is related to these instructions. Otherwise,
    # it would mean that there exists some intermediate instructions that do not affect the final results and thus,
    # they must be omitted.

    # If first instruction corresponds to top of the stack, we initialize the search with b0. Otherwise,
    # it means that another extra instruction must be performed after this, and thus, we start searching with b0 - 1.
    if top_elem_is_instruction:
        b0_aux = b0
    else:
        b0_aux = b0 - 1

    for final_instr in final_stack_instr:
        update_with_tree_level(b0, dependency_graph, b0_aux, final_instr, first_position_instr_cannot_appear)

        # If it isn't top of the stack, another instruction must go before it (SWAP or DUP). Only works once
        b0_aux = b0 - 1
    return first_position_instr_cannot_appear


# We generate a dict that given the id of an instruction, returns the
# the id of instructions that must be executed to obtain its input and the corresponding
# aj. Note that aj must be only assigned when push, in other cases we just set aj value to -1.
def generate_dependency_graph(user_instr):
    dependency_theta_graph = {}
    for instr in user_instr:
        instr_id = instr['id']
        dependency_theta_graph[instr_id] = list()
        for stack_elem in instr['inpt_sk']:
            # We search for another instruction that generates the
            # stack elem as an output and add it to the set
            if type(stack_elem) == str:
                previous_instr = list(filter(lambda instruction: instruction['outpt_sk'][0] == stack_elem, user_instr))

                # It might be in the initial stack, so the list can be empty
                if previous_instr:
                    # We add previous instr id
                    dependency_theta_graph[instr['id']].append((previous_instr[0]['id'], -1))
            # If we have an int, then we must perform a PUSHx to obtain that value
            else:
                dependency_theta_graph[instr_id].append(('PUSH', stack_elem))

    return dependency_theta_graph


# Method that returns all necessary structures for generating constraints related to
# instruction order: dependency graph, first_position_instr_appears_dict and first_position_instr_cannot_appear_dict.
# Read the corresponding methods for more info.
def generate_instruction_order_structures(b0, user_instr, final_stack_ids, top_elem_is_instruction):
    dependency_graph = generate_dependency_graph(user_instr)
    first_position_instr_appears_dict = generate_number_of_previous_instr_dict(dependency_graph)
    first_position_instr_cannot_appear_dict = generate_first_position_instr_cannot_appear(b0, final_stack_ids,
                                                                                          dependency_graph, top_elem_is_instruction)
    return dependency_graph, first_position_instr_appears_dict, first_position_instr_cannot_appear_dict


# Generate a dict that contains the real value as a key, and
# its associated index as a value.
def generate_phi_dict(user_instr, final_stack):
    idx = 0
    phi = {}
    for instr in user_instr:
        for elem in instr['inpt_sk']:
            if type(elem) == int and elem not in phi:
                phi[elem] = idx
                idx += 1
    for elem in final_stack:
        if type(elem) == int and elem not in phi:
            phi[elem] = idx
            idx += 1
    return phi


# Generate a dict that contains the theta associated to a
# instruction as values, and its corresponding opcode representation as values.
# Note that push has several possible opcodes depending on the size of the pushed value,
# and nop has no opcode associated. We will associated push to 60, the corresponding opcode
# for PUSH1.
def generate_disasm_map(user_instr, theta_instr):

    pattern_swap = re.compile("SWAP(.*)")
    pattern_dup = re.compile("DUP(.*)")

    instr_opcodes = {0: "60", 1: "50"}
    for id, theta in theta_instr.items():
        # This cases are already considered
        if id == "PUSH" or id == "POP" or id == "NOP":
            continue

        uninterpreted_function = True
        for match in re.finditer(pattern_swap, id):
            opcode = hex(int(match.group(1)) + int(str("90"), 16) - 1)[2:]
            uninterpreted_function = False
        for match in re.finditer(pattern_dup, id):
            opcode = hex(int(match.group(1)) + int(str("80"), 16) - 1)[2:]
            uninterpreted_function = False
        if uninterpreted_function:
            instr = list(filter(lambda instr: instr['id'] == id, user_instr))[0]
            opcode = instr['opcode']
        instr_opcodes[theta] = opcode

    return instr_opcodes


# Generate a dict that contains the theta associated to a instruction
# as keys and its corresponding EVM opcode as values. Note that it is similar
# to theta_comm and theta_non_comm, but instead of using id, we directly use
# disasm field (i.e. intead of having 14 : ADD_0, we would have 14 : ADD)
def generate_instr_map(user_instr, theta_stack, theta_comm, theta_non_comm):

    # We will consider in general the theta associated to instructions
    # in user instr structure
    theta_uninterpreted = dict(theta_comm, **theta_non_comm)

    # We reverse the theta stack, to have the theta value as key,
    # and its corresponding instruction as values
    theta_dict_reversed = {v: k for k, v in theta_stack.items()}
    for instr in user_instr:
        theta_value = theta_uninterpreted[instr['id']]
        disasm = instr['disasm']
        theta_dict_reversed[theta_value] = disasm

    return theta_dict_reversed