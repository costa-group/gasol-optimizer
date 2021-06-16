from encoding_utils import *
from encoding_files import write_encoding

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
# At this point, this means only pop and swap instructions are valid before a pop.
def no_output_before_pop(b0, theta_stack):
    write_encoding("; If we push or dup a value, the following instruction cannot be a pop")
    theta_pop = theta_stack["POP"]
    theta_swaps = [v for k,v in theta_stack.items() if k.startswith('SWAP')]
    no_output_instr_theta = [theta_pop, *theta_swaps]
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
def restrain_instruction_order(depencency_graph, first_position_instr_appears_dict, first_position_instr_cannot_appear_dict, theta):
    write_encoding("; Constraints that reflect the order among instructions")
    for instr, previous_instrs in depencency_graph.items():

        # We only consider instructions that have a dependency with at least other instruction
        # (could be push)
        if not previous_instrs:
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
            for previous_position in range(first_position_instr_appears_dict[previous_instr_name],
                                           min(first_position_instr_appears_dict[instr],
                                               first_position_instr_cannot_appear_dict[previous_instr_name])):
                # If aj == -1, then we don't need to consider to assign aj
                if aj == -1:
                    previous_values[previous_instr_name].append(add_eq(t(previous_position), theta[previous_instr_name]))
                else:
                    previous_values[previous_instr_name].append(add_and(add_eq(t(previous_position), theta[previous_instr_name]),
                                                   add_eq(a(previous_position), aj)))

        # We add a clause for every position the instruction may appear.
        for position in range(first_position_instr_appears_dict[instr], first_position_instr_cannot_appear_dict[instr]):

            # If current instruction is chosen for position j, then previous instructions must be places in previous
            # positions. This means that (tj = theta) => and_{instr in prev_instr}
            # (or_{i in possible_positions}(ti = instr))
            or_instr = [add_or(*possible_equalities) for possible_equalities in previous_values.values()]
            write_encoding(add_assert(add_implies(add_eq(t(position), theta[instr]), add_and(*or_instr))))

            # We update previous values list to add the possibility that previous instructions could be
            # executed in current position
            for previous_instr_name, aj in previous_instrs:

                # If first position an instruction cannot appear is less or equal than current position, then
                # we don't need to consider adding it to current clause
                if first_position_instr_cannot_appear_dict[previous_instr_name] <= position:
                    continue

                # If aj == -1, then we don't need to consider to assign aj
                if aj == -1:
                    previous_values[previous_instr_name].append(add_eq(t(position), theta[previous_instr_name]))
                else:
                    previous_values[previous_instr_name].append(add_and(add_eq(t(position), theta[previous_instr_name]),
                                                   add_eq(a(position), aj)))

# Each uninterpreted function is used at least once
def each_instruction_in_final_stack_is_used_at_least_once(b0, final_stack_theta_dict, first_position_instr_appears_dict,
                                        first_position_instr_cannot_appear_dict):
    write_encoding("; All uninterpreted functions in the final stack are eventually used")
    for instr_id, theta_instr in final_stack_theta_dict.items():
        or_variables = []

        initial_idx = first_position_instr_appears_dict.get(instr_id,0)
        final_idx = first_position_instr_cannot_appear_dict.get(instr_id, b0)

        for j in range(initial_idx, final_idx):
            or_variables.append(add_eq(t(j), theta_instr))
        write_encoding(add_assert(add_or(*or_variables)))