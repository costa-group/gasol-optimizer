from encoding_utils import *
from encoding_files import write_encoding
from encoding_memory_instructions import _l_variable_order_constraint, _mem_variable_equivalence_constraint

# Aditional contraints


# Each uninterpreted function is used at least once
def each_function_is_used_at_least_once(b0, initial_idx, end_idx):
    write_encoding("; All uninterpreted functions are eventually used")
    for i in range(initial_idx, end_idx):
        or_variables = []
        for j in range(b0):
            or_variables.append(add_eq(t(j), i))
        write_encoding(add_assert(add_or(*or_variables)))


# Each uninterpreted function is used at most once. This means that
# if we assign a instruction to tj, then we cannot assign the same
# function for any other ti. This restriction holds iff associated_gas >= 0
def each_function_is_used_at_most_once(b0, valid_theta):
    write_encoding("; All interpreted functions can be used at most once")
    # We need at least two elements to be a valid restriction
    if b0 <= 1:
        return
    for j in range(b0):
        remaining_pos = set(range(b0))
        remaining_pos.remove(j)
        for instr in valid_theta:
            write_encoding(add_assert(add_implies(add_eq(t(j), instr),
                                         add_and(*list(map(lambda i: add_not(add_eq(t(i), instr)), remaining_pos))))))


# Only a pop can be performed if no instruction introducing a value in the stack was performed just before.
# At this point, this means only pop, swap and storage instructions are valid before a pop.
def no_output_before_pop(b0, theta_stack, theta_mem):
    write_encoding("; If we push or dup a value, the following instruction cannot be a pop")
    theta_pop = theta_stack["POP"]
    theta_swaps = [v for k,v in theta_stack.items() if k.startswith('SWAP')]
    no_output_instr_theta = [theta_pop, *theta_swaps, *theta_mem.values()]
    for j in range(b0-1):
        write_encoding(add_assert(add_implies(add_eq(t(j+1), theta_pop),
                         add_or(*list(map(lambda instr: add_eq(t(j), instr), no_output_instr_theta))))))


# As we assume that each value that appears in the ops is needed, then we need to
# push each value at least once.
def push_each_element_at_least_once(b0, theta_push, pushed_elements):
    write_encoding("; All values are eventually pushed")
    for i in pushed_elements:
        or_variables = []
        for j in range(b0):
            or_variables.append(add_and(add_eq(t(j), theta_push), add_eq(a(j), i)))
        write_encoding(add_assert(add_or(*or_variables)))


# We can generate a graph that represents the dependencies between different opcodes
# (input). Then, we can assume that each one has to follow that restriction.
def restrain_instruction_order(b0, dependency_graph, first_position_instr_appears_dict,
                               first_position_instr_cannot_appear_dict, theta_conflicting, theta_dict, initial_idx = 0):
    write_encoding("; Constraints using l variables")

    for id, theta_store in theta_conflicting.items():
        initial_possible_idx = first_position_instr_appears_dict.get(id, 0) + initial_idx
        final_possible_idx = first_position_instr_cannot_appear_dict.get(id, b0) + initial_idx

        write_encoding(add_assert(add_and(add_leq(initial_possible_idx, l(theta_store)), add_lt(l(theta_store), final_possible_idx))))
        for j in range(initial_possible_idx, final_possible_idx):
            _mem_variable_equivalence_constraint(j, theta_store)

    for instr, previous_instrs in dependency_graph.items():

        # We only consider instructions that have a dependency with at least other instruction
        # (could be push)
        if not previous_instrs:
            continue

        for previous_instr_name, aj in previous_instrs:
            if previous_instr_name in theta_conflicting and instr in theta_conflicting :
                _l_variable_order_constraint(theta_conflicting[previous_instr_name], theta_conflicting[instr])
                continue

        # Previous values stores possible values previous instructions may have, represented
        # as tj = theta_instr. It will be a dict where keys are the instruction id and values are a list
        # of equalities of the form tj= theta_instr
        previous_values = {}
        for previous_instr_name, aj in previous_instrs:

            # If previous instruction doesn't appear in previous_values, we initialize to empty list
            if previous_instr_name not in previous_values:
                previous_values[previous_instr_name] = []

            # We add a clause for each possible position in which previous equation may appear before current one.
            # This means that we have to take the min between current position or last position previous instruction
            # could occur.
            for previous_position in range(first_position_instr_appears_dict.get(previous_instr_name,0),
                                           min(first_position_instr_appears_dict.get(instr,0),
                                               first_position_instr_cannot_appear_dict.get(previous_instr_name, b0))):
                # If aj == -1, then we don't need to consider to assign aj
                if aj == -1:
                    previous_values[previous_instr_name].append(add_eq(t(previous_position), theta_dict[previous_instr_name]))
                else:
                    previous_values[previous_instr_name].append(add_and(add_eq(t(previous_position), theta_dict[previous_instr_name]),
                                                   add_eq(a(previous_position), aj)))

        # We add a clause for every position the instruction may appear.
        for position in range(first_position_instr_appears_dict.get(instr,0), first_position_instr_cannot_appear_dict.get(instr, b0)):

            # If current instruction is chosen for position j, then previous instructions must be places in previous
            # positions. This means that (tj = theta) => and_{instr in prev_instr}
            # (or_{i in possible_positions}(ti = instr))
            or_instr = [add_or(*possible_equalities) for possible_equalities in previous_values.values()]
            write_encoding(add_assert(add_implies(add_eq(t(position), theta_dict[instr]), add_and(*or_instr))))

            # We update previous values list to add the possibility that previous instructions could be
            # executed in current position
            for previous_instr_name, aj in previous_instrs:

                # If first position an instruction cannot appear is less or equal than current position, then
                # we don't need to consider adding it to current clause
                if first_position_instr_cannot_appear_dict.get(previous_instr_name, b0) <= position:
                    continue

                # If aj == -1, then we don't need to consider to assign aj
                if aj == -1:
                    previous_values[previous_instr_name].append(add_eq(t(position), theta_dict[previous_instr_name]))
                else:
                    previous_values[previous_instr_name].append(add_and(add_eq(t(position), theta_dict[previous_instr_name]),
                                                   add_eq(a(position), aj)))

# Each uninterpreted function is used at least once
def each_instruction_is_used_at_least_once_with_instruction_order(b0, theta_dict, first_position_instr_appears_dict,
                                                                  first_position_instr_cannot_appear_dict):
    write_encoding("; All uninterpreted functions in the final stack are eventually used")
    for instr_id, theta_instr in theta_dict.items():
        or_variables = []

        initial_idx = first_position_instr_appears_dict.get(instr_id,0)
        final_idx = first_position_instr_cannot_appear_dict.get(instr_id, b0)

        for j in range(initial_idx, final_idx):
            or_variables.append(add_eq(t(j), theta_instr))
        write_encoding(add_assert(add_or(*or_variables)))