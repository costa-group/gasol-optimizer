# Methods containing the generation of constraints
# for applying superoptimization. It is assumed the
# SFS has already been generated
import copy

from smt_encoding.default_encoding import activate_default_encoding
from smt_encoding.encoding_cost import (label_name, gas_group_constraints, gas_direct_constraints,
                                        size_direct_constraints, size_group_constraints,
                                        number_instructions_soft_constraints, paper_soft_constraints)
from smt_encoding.encoding_files import (write_encoding, write_gas_map,
                                         write_instruction_map,
                                         write_opcode_map)
from smt_encoding.encoding_initialize import (final_stack_encoding,
                                              initial_stack_encoding,
                                              initialize_variables,
                                              variables_assignment_constraint)
from smt_encoding.encoding_memory_instructions import (
    memory_model_constraints_direct, memory_model_constraints_l_conflicting)
from smt_encoding.encoding_reconstruct_solution import \
    generate_encoding_from_log_json_dict
from smt_encoding.encoding_redundant import (
    each_function_is_used_at_least_once, each_function_is_used_at_most_once,
    each_instruction_is_used_at_least_once_with_instruction_order,
    no_output_before_pop, push_each_element_at_least_once,
    restrain_instruction_order)
from smt_encoding.encoding_stack_instructions import stack_constraints
from smt_encoding.encoding_utils import (a, divide_usr_instr,
                                         generate_costs_ordered_dict,
                                         generate_disasm_map,
                                         generate_instr_map,
                                         generate_instruction_order_structures,
                                         generate_phi_dict,
                                         generate_stack_theta,
                                         generate_uninterpreted_theta, t)
from smt_encoding.smtlib_utils import (check_sat, get_objectives, get_value,
                                       load_objective_model, set_logic,
                                       set_minimize_function, set_model_true,
                                       set_timeout)


# Method to generate redundant constraints according to flags (at least once is included by default)
def generate_redundant_constraints(flags, b0, user_instr, theta_stack, theta_comm, theta_non_comm, final_stack,
                                   dependency_graph, first_position_instr_appears_dict,
                                   first_position_instr_cannot_appear_dict, theta_dict, theta_mem, theta_l_dict):
    if flags['at-most']:
        valid_theta = list(map(lambda instr: theta_comm[instr['id']] if instr['commutative'] else theta_non_comm[instr['id']],
                             filter(lambda instr: instr['gas'] > 2, user_instr)))
        each_function_is_used_at_most_once(b0, valid_theta)
    if flags['pushed-at-least']:
        pushed_values = generate_phi_dict(user_instr, final_stack)
        push_each_element_at_least_once(b0, theta_stack['PUSH'], pushed_values)
    if flags['no-output-before-pop']:
        no_output_before_pop(b0, theta_stack, theta_mem)
    if flags['instruction-order']:
        theta_non_stack_dict = dict(theta_comm, **theta_non_comm, **theta_mem)
        non_used_variables = set(theta_non_stack_dict.keys()).difference(set(theta_l_dict.keys()))
        theta_non_l = {instr: theta_non_stack_dict[instr] for instr in non_used_variables}
        each_instruction_is_used_at_least_once_with_instruction_order(b0, theta_non_l,
                                                                      first_position_instr_appears_dict,
                                                                      first_position_instr_cannot_appear_dict)
        restrain_instruction_order(b0, dependency_graph, first_position_instr_appears_dict,
                               first_position_instr_cannot_appear_dict, theta_l_dict, theta_dict)

    # If flag isn't set, then we use by default the generation for each function used at least once in each position
    else:
        each_function_is_used_at_least_once(b0, len(theta_stack), len(theta_dict))


# Method to generate optional asserts according to additional info. It includes that info that relies on the
# specific solver
def generate_asserts_from_additional_info(additional_info):
    if additional_info['tout'] is not None:
        if additional_info['solver'] == "z3":
            write_encoding(set_timeout(1000 * additional_info['tout']))
        elif additional_info['solver'] == "oms":
            write_encoding(set_timeout(float(additional_info['tout'])))


def generate_soft_constraints(solver_name, b0, user_instr, theta_dict, first_position_dict, last_position_dict, flags):
    is_barcelogic = solver_name == "barcelogic"

    if flags['inequality-gas-model']:
        gas_direct_constraints(user_instr, theta_dict, first_position_dict, last_position_dict, is_barcelogic)
    elif flags['number-instruction-gas-model']:
        number_instructions_soft_constraints(b0, theta_dict['NOP'], is_barcelogic)
    elif flags['bytecode-size-soft-constraints']:
        size_group_constraints(theta_dict, first_position_dict, last_position_dict, is_barcelogic)
    elif flags['inequality-size-model']:
        size_direct_constraints(theta_dict, first_position_dict, last_position_dict, is_barcelogic)
    else:
        gas_group_constraints(user_instr, theta_dict, first_position_dict, last_position_dict, is_barcelogic)
        # paper_soft_constraints(b0, b0, user_instr, theta_dict, is_barcelogic)


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
def generate_instruction_dicts(b0, user_instr, final_stack, flags, order_tuples):
    if flags['instruction-order']:
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
        return generate_instruction_order_structures(b0, user_instr, final_stack_ids, top_elem_is_instruction,
                                                     comm_instrs, mem_instrs, order_tuples)
    else:
        return dict(), dict(), dict()


# Determines how to encode the memory depending on the flags
def generate_memory_constraints(flags, memory_encoding, b0, theta_dict, theta_mem, order_tuples, first_position_instr_appears_dict,
                                   first_position_instr_cannot_appear_dict):
    # If instruction-order flag is enabled, memory constraints are considered as part of the encoding of uninterpreted functions
    # so it is not needed to encode at this point
    if memory_encoding == "l_vars":
        if not flags['instruction-order']:
            memory_model_constraints_l_conflicting(b0, order_tuples, theta_dict, theta_mem, first_position_instr_appears_dict,
                                                   first_position_instr_cannot_appear_dict)
    else:
        memory_model_constraints_direct(b0, order_tuples, theta_dict, first_position_instr_appears_dict,
                                        first_position_instr_cannot_appear_dict)


# Determine which l variables must be initialized depending on the memory encoding
def generate_l_theta_dict(flags, memory_encoding, theta_dict, user_instr, order_tuples):
    if memory_encoding == "l_vars":
        # First case: if instruction-order flag is enabled then all uninterpreted functions without input parameters
        # are considered for l variables
        if flags['instruction-order']:
            return dict((map(lambda instr: (instr['id'], theta_dict[instr['id']]),
                             filter(lambda instr: len(instr['inpt_sk']) > 0, user_instr))))

        # Otherwise, only conflicting memory instructions are considered
        else:
            conflicting_instructions_ids = set()
            for pair in order_tuples:
                conflicting_instructions_ids.add(pair[0])
                conflicting_instructions_ids.add(pair[1])
            return dict((map(lambda instr: (instr['id'], theta_dict[instr['id']]),
                             filter(lambda instr: instr['id'] in conflicting_instructions_ids , user_instr))))
    # No l variables are used, then return an empty dict
    else:
        return dict()


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
    order_tuples = additional_info['mem_order']
    memory_encoding = additional_info['memory_encoding']

    theta_stack = generate_stack_theta(bs)
    theta_comm, theta_non_comm, theta_mem = generate_uninterpreted_theta(usr_instr, len(theta_stack))
    comm_instr, non_comm_instr, mem_instr = divide_usr_instr(usr_instr)
    dependency_graph, first_position_instr_appears_dict, first_position_instr_cannot_appear_dict = \
        generate_instruction_dicts(b0, usr_instr, final_stack, flags, order_tuples)
    theta_dict = dict(theta_stack, **theta_comm, **theta_non_comm, **theta_mem)
    l_theta_dict = generate_l_theta_dict(flags, memory_encoding, theta_dict, usr_instr, order_tuples)
    additional_info['tout'] = additional_info['tout'] * (len(theta_mem) + 1)

    # Before generating the encoding, we activate the default encoding if its corresponding flag is activated
    if flags['default-encoding']:
        flags = activate_default_encoding(initial_stack, final_stack, usr_instr, b0, flags)

    write_encoding(set_logic('QF_IDL'))
    generate_configuration_statements(solver_name)
    generate_asserts_from_additional_info(additional_info)
    initialize_variables(variables, bs, b0, l_theta_dict)
    variables_assignment_constraint(variables)
    stack_constraints(b0, bs, comm_instr, non_comm_instr, mem_instr, theta_stack, theta_comm, theta_non_comm, theta_mem,
                      first_position_instr_appears_dict, first_position_instr_cannot_appear_dict)

    initial_stack_encoding(initial_stack, bs)
    final_stack_encoding(final_stack, bs, b0)
    generate_memory_constraints(flags, memory_encoding, b0, theta_dict, theta_mem, order_tuples, first_position_instr_appears_dict,
                                first_position_instr_cannot_appear_dict)
    generate_redundant_constraints(flags, b0, usr_instr, theta_stack, theta_comm, theta_non_comm, final_stack,
                                   dependency_graph, first_position_instr_appears_dict,
                                   first_position_instr_cannot_appear_dict, theta_dict, theta_mem, l_theta_dict)

    # Only consider instructions that do not belong to the l dict
    user_instr_cost = []
    not_l_theta_dict = {}
    last_position_dict = {}
    first_position_dict = {}
    for instr in usr_instr:
        new_instr = copy.deepcopy(instr)
        instr_id = new_instr['id']
        if instr_id not in l_theta_dict:
            user_instr_cost.append(new_instr)

    for instr_id in set(theta_dict.keys()).difference(set(l_theta_dict.keys())):
        theta_instr = theta_dict[instr_id]
        not_l_theta_dict[instr_id] = theta_dict[instr_id]
        first_position_dict[theta_instr] = first_position_instr_appears_dict.get(instr_id, 0)
        last_position_dict[theta_instr] = first_position_instr_cannot_appear_dict.get(instr_id, b0)


    generate_soft_constraints(solver_name, b0, user_instr_cost, not_l_theta_dict, first_position_dict, last_position_dict, flags)
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
    write_encoding("; Mem: " + str(theta_mem))
    write_encoding("; L dict: " + str(l_theta_dict))

    write_instruction_map(generate_instr_map(usr_instr, theta_stack, theta_comm, theta_non_comm, theta_mem))
    write_opcode_map(generate_disasm_map(usr_instr, theta_dict))
    write_gas_map(generate_costs_ordered_dict(bs, usr_instr, theta_dict))


# Method to generate complete representation given
def generate_smtlib_encoding_appending(b0, bs, usr_instr, variables, initial_stack, final_stack,
                                       previous_solution, previous_idx, order_tuples):
    theta_stack = generate_stack_theta(bs)
    theta_comm, theta_non_comm, theta_mem = generate_uninterpreted_theta(usr_instr, len(theta_stack))
    comm_instr, non_comm_instr, mem_instr = divide_usr_instr(usr_instr)
    theta_dict = dict(theta_stack, **theta_comm, **theta_non_comm, **theta_mem)

    initialize_variables(variables, bs, b0, {}, previous_idx)
    variables_assignment_constraint(variables, previous_idx)
    stack_constraints(b0, bs, comm_instr, non_comm_instr, mem_instr, theta_stack, theta_comm, theta_non_comm, theta_mem,
                      {}, {}, previous_idx)

    memory_model_constraints_direct(b0, order_tuples, theta_dict, {}, {}, previous_idx)
    initial_stack_encoding(initial_stack, bs, previous_idx)
    final_stack_encoding(final_stack, bs, b0, previous_idx)
    generate_encoding_from_log_json_dict(previous_solution, previous_idx)
