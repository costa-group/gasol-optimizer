# This function infers statically the number of necessary instructions without
# taking into account SWAPs, the number of necessary instructions and the number of push
# instructions.
def infer_size_relation(initial_stack, final_stack, instructions):
    n_instrs = len(instructions)
    n_push = 0
    stack_var_count = dict()
    for elem in initial_stack:
        stack_var_count[elem] = stack_var_count.get(elem, 0) + 1
    for elem in final_stack:
        if type(elem) == int:
            n_push += 1
        stack_var_count[elem] = stack_var_count.get(elem, 0) - 1

    # For every instruction, we consider the number of elements generated
    # and consumed. This will indicate the number of necessary instructions
    for instr in instructions:
        for elem in instr['inpt_sk']:
            if type(elem) == int:
                n_push += 1
            stack_var_count[elem] = stack_var_count.get(elem, 0) - 1

        for elem in instr['outpt_sk']:
            stack_var_count[elem] = stack_var_count.get(elem, 0) + 1

    # A lower bound is the different between consumed and produced elements + number
    # of instructions. If we consume more elements that produce, we need at least to generate
    # elements via PUSH or DUP instructions. Otherwise, we need to apply POP. As we know that
    # each of these instructions produces/consumes one element, we can directly infer the number
    # of instructions needed by the difference between consumed and produced elements in abs.
    num_stack_ops = 0
    for elem in stack_var_count.values():
        num_stack_ops += abs(elem)

    # At least one instruction must be applied, as we assume init stack and target
    # stack are not the same. Thus, we consider the max between the expected result and one.
    # Needed because for some relations we divide by this number
    return max(num_stack_ops + len(instructions), 1), n_instrs, n_push


# Computes the corresponding static parameters and enables the corresponding flags according
# to them.
def activate_default_encoding(initial_stack, final_stack, instructions, initial_seq_length, flags):
    expected_seq_length, n_instrs, n_push = infer_size_relation(initial_stack, final_stack, instructions)
    flags['no-output-before-pop'] = True
    if expected_seq_length / initial_seq_length >= 0.7:
        flags['pushed-at-least'] = True
    if initial_seq_length <= 15:
        flags['pushed-at-least'] = True
    return flags
