# Methods containing the generation of constraints
# for applying superoptimization. It is assumed the
# SFS has already been generated

from encoding_utils import *
from encoding_initialize import initialize_variables, variables_assignment_constraint, \
    initial_stack_encoding, final_stack_encoding
from encoding_cost import paper_soft_constraints, label_name, alternative_soft_constraints, \
    number_instructions_soft_constraints
from encoding_instructions import instructions_constraints
from encoding_redundant import *
from encoding_files import write_encoding, write_opcode_map, write_instruction_map, write_gas_map
from default_encoding import activate_default_encoding
from encoding_reconstruct_solution import generate_encoding_from_log_json_dict

# Method to generate redundant constraints according to flags (at least once is included by default)
def generate_redundant_constraints(flags, b0, user_instr, theta_stack, theta_comm, theta_non_comm, final_stack,
                                   dependency_graph, first_position_instr_appears_dict,
                                   first_position_instr_cannot_appear_dict, theta_dict):
    if flags['at-most']:
        valid_theta = list(map(lambda instr: theta_comm[instr['id']] if instr['commutative'] else theta_non_comm[instr['id']],
                             filter(lambda instr: instr['gas'] > 2, user_instr)))
        each_function_is_used_at_most_once(b0, valid_theta)
    if flags['pushed-at-least']:
        pushed_values = generate_phi_dict(user_instr, final_stack)
        push_each_element_at_least_once(b0, theta_stack['PUSH'], pushed_values)
    if flags['no-output-before-pop']:
        no_output_before_pop(b0, theta_stack)
    if flags['instruction-order']:
        final_stack_instrs = list(filter(lambda instr: instr['outpt_sk'] and (instr['outpt_sk'][0] in final_stack), user_instr))
        final_stack_dict = {instr['id']: theta_dict[instr['id']] for instr in final_stack_instrs}
        each_instruction_in_final_stack_is_used_at_least_once(b0, final_stack_dict,
                                                              first_position_instr_appears_dict,
                                                              first_position_instr_cannot_appear_dict)
        restrain_instruction_order(dependency_graph, first_position_instr_appears_dict,
                                   first_position_instr_cannot_appear_dict, theta_dict)

    # If flag isn't set, then we use by default the generation for each function used at least once in each position
    else:
        each_function_is_used_at_least_once(b0, len(theta_stack),
                                            len(theta_stack) + len(theta_comm) + len(theta_non_comm))


# Method to generate optional asserts according to additional info. It includes that info that relies on the
# specific solver
def generate_asserts_from_additional_info(additional_info):
    if additional_info['tout'] is not None:
        if additional_info['solver'] == "z3":
            write_encoding(set_timeout(1000 * additional_info['tout']))
        elif additional_info['solver'] == "oms":
            write_encoding(set_timeout(float(additional_info['tout'])))


def generate_soft_constraints(solver_name, b0, bs, usr_instr, theta_dict, flags,
                              current_cost, instr_seq):
    is_barcelogic = solver_name == "barcelogic"

    # We need to address whether the want to encode the initial solution (in which case,
    # weight is assigned to -1) or not. Only paper soft constraints take into account this value.
    if flags['initial-solution']:
        weight = current_cost
    else:
        weight = -1

    if flags['inequality-gas-model']:
        alternative_soft_constraints(b0, bs, usr_instr, theta_dict, is_barcelogic)
    elif flags['number-instruction-gas-model']:
        number_instructions_soft_constraints(b0, theta_dict['NOP'], is_barcelogic)
    else:
        paper_soft_constraints(b0, bs, usr_instr, theta_dict, is_barcelogic, instr_seq, weight)


def generate_cost_functions(solver_name):
    if solver_name == "oms":
        write_encoding(set_minimize_function(label_name))


def generate_configuration_statements(solver_name):
    if solver_name == "oms":
        write_encoding(set_model_true())


# Generates the corresponding structures for both instruction encoding and
# instruction order. If flags -instruction-order is activated, then it returns
# dependency graph, first_position_instr_appears_dict and first_position_instr_cannot_appear_dict.
# If not, it returns empty dicts that simulates the behaviour of these structures. There's no problem
# with being empty, as they are accessed using get method with the corresponding correct values by default.
def generate_instruction_dicts(b0, user_instr, final_stack, flags):
    if flags['instruction-order']:
        # We obtain the id of those instructions whose output is in the final stack
        final_stack_instrs = list(filter(lambda instr: instr['outpt_sk'] and (instr['outpt_sk'][0] in final_stack),user_instr))

        index_map = {v: i for i, v in enumerate(final_stack)}

        # We order instructions according to its position in the final stack. This is important to generate
        # the first_position_instruction_can_occur dict, as position is taken into account.
        final_stack_ids = list(map(lambda instr: instr['id'],
                                      sorted(final_stack_instrs, key= lambda instr: index_map[instr['outpt_sk'][0]])))

        # We check if any the top element in the stack corresponds to the output of an uninterpreted function
        top_elem_is_instruction = any([0 == index_map[instr['outpt_sk'][0]] for instr in final_stack_instrs])
        return generate_instruction_order_structures(b0, user_instr, final_stack_ids, top_elem_is_instruction)
    else:
        return dict(), dict(), dict()


# Adding necessary statements after check_sat statement.
# Barcelogic doesn't support (get-objectives) statement.
def generate_final_statements(solver_name):
    if solver_name == "z3":
        write_encoding(get_objectives())
    elif solver_name == "oms":
        write_encoding(get_objectives())
        # If solver is OMS, we allow to generate the model for non-optimal solutions
        write_encoding(load_objective_model())


# Method to generate complete representation
def generate_smtlib_encoding(b0, bs, usr_instr, variables, initial_stack, final_stack, flags, additional_info):
    solver_name = additional_info['solver']
    current_cost = additional_info['current_cost']
    instr_seq = additional_info['instr_seq']
    theta_stack = generate_stack_theta(bs)
    theta_comm, theta_non_comm = generate_uninterpreted_theta(usr_instr, len(theta_stack))
    comm_instr, non_comm_instr = separe_usr_instr(usr_instr)
    dependency_graph, first_position_instr_appears_dict, first_position_instr_cannot_appear_dict = \
        generate_instruction_dicts(b0, usr_instr, final_stack, flags)
    theta_dict = dict(theta_stack, **theta_comm, **theta_non_comm)

    # Before generating the encoding, we activate the default encoding if its corresponding flag is activated
    if flags['default-encoding']:
        flags = activate_default_encoding(initial_stack, final_stack, usr_instr, b0, flags)

    write_encoding(set_logic('QF_LIA'))
    generate_configuration_statements(solver_name)
    generate_asserts_from_additional_info(additional_info)
    initialize_variables(variables, bs, b0)
    variables_assignment_constraint(variables)
    instructions_constraints(b0, bs, comm_instr, non_comm_instr, theta_stack, theta_comm, theta_non_comm,
                             first_position_instr_appears_dict, first_position_instr_cannot_appear_dict)
    initial_stack_encoding(initial_stack, bs)
    final_stack_encoding(final_stack, bs, b0)
    generate_redundant_constraints(flags, b0, usr_instr, theta_stack, theta_comm, theta_non_comm, final_stack,
                                   dependency_graph, first_position_instr_appears_dict,
                                   first_position_instr_cannot_appear_dict, theta_dict)
    generate_soft_constraints(solver_name, b0, bs, usr_instr, theta_dict, flags, current_cost, instr_seq)
    generate_cost_functions(solver_name)
    if additional_info['previous_solution'] is not None:
        generate_encoding_from_log_json_dict(additional_info['previous_solution'])
    write_encoding(check_sat())
    generate_final_statements(solver_name)
    # get_model()
    for j in range(b0):
        write_encoding(get_value(t(j)))
        write_encoding(get_value(a(j)))
    write_encoding("; Stack: " + str(theta_stack))
    write_encoding("; Comm: " + str(theta_comm))
    write_encoding("; Non-Comm: " + str(theta_non_comm))

    write_instruction_map(generate_instr_map(usr_instr, theta_stack, theta_comm, theta_non_comm))
    write_opcode_map(generate_disasm_map(usr_instr, theta_dict))
    write_gas_map(generate_costs_ordered_dict(bs, usr_instr, theta_dict))


# Method to generate complete representation given
def generate_smtlib_encoding_appending(b0, bs, usr_instr, variables, initial_stack, final_stack,
                                       previous_solution, previous_idx):
    theta_stack = generate_stack_theta(bs)
    theta_comm, theta_non_comm = generate_uninterpreted_theta(usr_instr, len(theta_stack))
    comm_instr, non_comm_instr = separe_usr_instr(usr_instr)

    initialize_variables(variables, bs, b0, previous_idx)
    variables_assignment_constraint(variables, previous_idx)
    instructions_constraints(b0, bs, comm_instr, non_comm_instr, theta_stack, theta_comm, theta_non_comm,
                             {}, {}, previous_idx)
    initial_stack_encoding(initial_stack, bs, previous_idx)
    final_stack_encoding(final_stack, bs, b0, previous_idx)
    generate_encoding_from_log_json_dict(previous_solution, previous_idx)
