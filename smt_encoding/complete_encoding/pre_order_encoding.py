import itertools

from smt_encoding.encoding_utils import l
from smt_encoding.smtlib_utils import declare_intvar
from smt_encoding.encoding_memory_instructions import l_variable_order_constraint, mem_variable_equivalence_constraint, direct_order_constraint

# We generate a dict that given the id of an instruction, returns
# the id of instructions that must be executed to obtain its input and the corresponding
# aj. Note that aj must be only assigned when push, in other cases we just set aj value to -1.
def generate_dependency_graph(uninterpreted_instr, order_tuples):
    dependency_graph = {}
    for instr in uninterpreted_instr:
        instr_id = instr.id
        dependency_graph[instr_id] = list()
        for stack_elem in instr.input_stack:

            # We search for another instruction that generates the
            # stack elem as an output and add it to the set
            if type(stack_elem) == str:
                previous_instr = list(filter(lambda instruction: len(instruction.output_stack) == 1 and
                                                                 instruction.output_stack[0] == stack_elem, uninterpreted_instr))

                # It might be in the initial stack, so the list can be empty
                if previous_instr:
                    # We add previous instr id
                    dependency_graph[instr.id].append(previous_instr[0].id)

            # If we have an int, then we must perform a PUSHx to obtain that value
            else:
                dependency_graph[instr_id].append('PUSH')

    # We need to consider also the order given by the tuples
    for id1, id2 in order_tuples:
        if not list(filter(lambda x: x[0] == id1, dependency_graph[id2])):
            dependency_graph[id2].append(id1)

    return dependency_graph


# Given an instruction, a dict that links each instruction to a lower bound to the number of instructions
# # needed to obtain the output from that dict, and another dict
# that links each instruction to the previous instructions needed to execute that instruction,
# updates both dicts for that instruction and returns the corresponding values associated to the instruction.
def generate_instr_dependencies(instr, number_of_instructions_to_execute, previous_values, dependency_graph):

    # Base case: it has been already analyzed, so we return the values associated.
    if instr in previous_values:
        return number_of_instructions_to_execute[instr], previous_values[instr]

    number_of_instructions_needed = 0
    instructions_dependency = set()

    # Recursive case: we obtain the output for each previous instruction and update the values
    for previous_instr in dependency_graph[instr]:

        previous_number_of_instr_needed, previous_instructions_dependency = \
            generate_instr_dependencies(previous_instr, number_of_instructions_to_execute,
                                        previous_values, dependency_graph)

        # We need the number of instructions needed for previous instruction plus one (executing that instruction)
        number_of_instructions_needed += previous_number_of_instr_needed + 1

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

    return number_of_instructions_needed, instructions_dependency


# Given the dict containing the dependency among different instructions, we generate
# another dict that links each instruction to the number of instructions that must be
# executed previously to be able to execute that instruction.
def generate_number_of_previous_instr_dict(dependency_graph):
    previous_values = {}
    number_of_instructions_to_execute = {}
    for instr in dependency_graph:
        generate_instr_dependencies(instr, number_of_instructions_to_execute, previous_values, dependency_graph)

    return number_of_instructions_to_execute


# First time an instruction cannot appear is b0-h, where h is the tree height. We recursively obtain this value,
# taking into account that we may have different trees and the final value is the min for all possible ones
def update_with_tree_level(b0, input_stacks_dict, dependency_graph, current_idx, instr, first_position_instr_cannot_appear, theta_comm):

    # Neither we consider push instructions nor instructions that already have appeared and appear before the best
    # result so far. On the other hand, if current index > already considered index, we need to traverse the tree in order to
    # update the values, as we neet to consider the biggest position in which the instruction cannot appear
    if instr in first_position_instr_cannot_appear and current_idx <= first_position_instr_cannot_appear[instr] :
        return

    first_position_instr_cannot_appear[instr] = current_idx

    # If an instruction is not commutative, then only topmost previous element can be obtained
    # just before and the remaining ones need at least a SWAP to be placed in their position
    dependent_instr = set(dependency_graph[instr])
    previous_idx = current_idx - 1
    for prev_instr in input_stacks_dict[instr]:
        update_with_tree_level(b0, input_stacks_dict, dependency_graph, previous_idx, prev_instr,
                               first_position_instr_cannot_appear, theta_comm)

        # If an instruction is not commutative, then only topmost previous element can be obtained
        # just before and the remaining ones need at least a SWAP to be placed in their position
        if prev_instr not in theta_comm:
            previous_idx = current_idx - 2

    # There can be other related instructions that are not considered before. As we do not know exactly
    # where they can appear, we assume worst case (current_idx - 1)
    for prev_instr in dependent_instr.difference(set(input_stacks_dict[instr])):
        update_with_tree_level(b0, input_stacks_dict, dependency_graph, current_idx - 1, prev_instr,
                               first_position_instr_cannot_appear, theta_comm)


# Generates a dict that given b0, returns the first position in which a instruction cannot appear
# due to dependencies with other instructions.
def generate_first_position_instr_cannot_appear(b0, input_stacks_dict, final_stack_instr,
                                                dependency_graph, mem_ids, comm_ids, top_elem_is_instruction):
    first_position_instr_cannot_appear = {}

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
        update_with_tree_level(b0, input_stacks_dict, dependency_graph, b0_aux, final_instr, first_position_instr_cannot_appear, comm_ids)

        # If it isn't top of the stack, another instruction must go before it (SWAP or DUP). Only works once
        b0_aux = b0 - 1

    for final_instr in mem_ids:
        update_with_tree_level(b0, input_stacks_dict, dependency_graph, b0, final_instr, first_position_instr_cannot_appear, comm_ids)

    return first_position_instr_cannot_appear


# Generates the corresponding structures for both instruction encoding and
# instruction order. If flags -instruction-order is activated, then it returns
# dependency graph, first_position_instr_appears_dict and first_position_instr_cannot_appear_dict.
# If not, it returns empty dicts that simulates the behaviour of these structures. There's no problem
# with being empty, as they are accessed using get method with the corresponding correct values by default.
def generate_instruction_dicts(b0, user_instr, final_stack, flags, order_tuples):
    # We obtain the id of those instructions whose output is in the final stack
    final_stack_instrs = list(filter(lambda instr: instr['outpt_sk'] and (instr['outpt_sk'][0] in final_stack),user_instr))

    mem_instrs = list(map(lambda instr: instr['id'],filter(lambda instr: instr['storage'],user_instr)))

    comm_instrs = list(map(lambda instr: instr['id'],filter(lambda instr: instr['commutative'],user_instr)))


    index_map = {v: i for i, v in enumerate(final_stack)}

    # We order instructions according to its position in the final stack. This is important to generate
    # the first_position_instruction_can_occur dict, as position is taken into account.
    final_stack_ids = list(map(lambda instr: instr['id'],
                                  sorted(final_stack_instrs, key= lambda instr: index_map[instr['outpt_sk'][0]])))

    # We check if any the top element in the stack corresponds to the output of an uninterpreted function
    top_elem_is_instruction = any([0 == index_map[instr['outpt_sk'][0]] for instr in final_stack_instrs])


class PreOrderEncoding:

    def __init__(self, instructions, order_tuples, b0, bs):
        self._instructions = instructions
        self._order_tuples = order_tuples
        self._dependency_theta_graph = generate_dependency_graph(instructions, order_tuples)
        self._b0 = b0
        self._bs = bs


    def _generate_order_from_instructions(self):
        return None


    def first_position_in_sequence(self, instruction):
        return self._first_position_instr.get(instruction, 0)


    def last_position_in_sequence(self, instruction):
        return self._last_position_instr.get(instruction, self._b0)


    def encode_order(self, **kwargs):
        constraints = []

        l_encoding_flag = kwargs["l_var"]

        if l_encoding_flag:
            pass


        # Those instructions which has a unique id associated are considered as part of the encoding order
        unique_instructions = list(filter(lambda instr: instr.unique_id, self._instructions))
        constraints.extend(itertools.chain.from_iterable([initialize_l_vars(instr.theta) for instr in unique_instructions]))
        constraints.extend(itertools.chain.from_iterable([mem_variable_equivalence_constraint(instr.theta) for instr in unique_instructions]))

        constraints.extend(itertools.chain.from_iterable([initialize_l_vars(instr.theta) for instr in unique_instructions]))
        constraints.extend(itertools.chain.from_iterable([initialize_l_vars(instr.theta) for instr in unique_instructions]))







