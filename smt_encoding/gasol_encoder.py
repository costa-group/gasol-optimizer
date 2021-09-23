#!/usr/bin/env python3

from superoptimization_enconding import generate_smtlib_encoding, generate_smtlib_encoding_appending
from utils_bckend import add_bars_and_index_to_string
import json
from encoding_files import initialize_dir_and_streams, write_encoding
from smtlib_utils import set_logic, check_sat
import re
from encoding_utils import generate_disasm_map, generate_costs_ordered_dict, generate_stack_theta, generate_instr_map, \
    generate_uninterpreted_theta, generate_uninterpreted_push_map
import copy

def parse_data(json_path, var_initial_idx=0, with_simplifications=True):
    # We can pass either the path to a json file, or
    # directly the dict that contains the SFS.
    if type(json_path) == str:
        with open(json_path) as path:
            data = json.load(path)
    else:
        data = json_path

    bs = data['max_sk_sz']

    # If simplifications have been applied, then we retrieve field "user_instrs". Otherwise,
    # field "non_inter" is retrieved.
    if with_simplifications:
        user_instr = data['user_instrs']

        # Note that b0 can be either max_progr_len
        # or init_progr_len
        # b0 = data['max_progr_len']
        b0 = data['init_progr_len']

    else:
        user_instr = data['init_info']['non_inter']
        # If no simplifications were made, we take the max_progr_len instead to ensure there is
        # no problem with index.
        b0 = data['max_progr_len']

    # To avoid errors, we copy user instr to generate a new one
    new_user_instr = []

    for instr in user_instr:
        new_instr = copy.deepcopy(instr)
        new_instr['outpt_sk'] = list(map(lambda x: add_bars_and_index_to_string(x, var_initial_idx), instr['outpt_sk']))
        new_instr['inpt_sk'] = list(map(lambda x: add_bars_and_index_to_string(x, var_initial_idx), instr['inpt_sk']))
        new_user_instr.append(new_instr)

    initial_stack = list(map(lambda x: add_bars_and_index_to_string(x, var_initial_idx), data['src_ws']))
    final_stack = list(map(lambda x: add_bars_and_index_to_string(x, var_initial_idx), data['tgt_ws']))
    variables = list(map(lambda x: add_bars_and_index_to_string(x, var_initial_idx), data['vars']))

    current_cost = data['current_cost']
    instr_seq = data.get('disasm_seq', [])
    mem_order = data.get('storage_dep', [])
    return b0, bs, new_user_instr, variables, initial_stack, final_stack, current_cost, instr_seq, mem_order



def initialize_flags_and_additional_info(args_i, current_cost, instr_seq, previous_solution_dict, mem_order):
    if args_i is None:
        flags = {'at-most': False, 'pushed-at-least': False,
                 'instruction-order': False,
                 'no-output-before-pop': False, 'inequality-gas-model': False,
                 'initial-solution': False, 'default-encoding': False,
                 'number-instruction-gas-model': False}
        additional_info = {'tout': 10, 'solver': "oms", 'current_cost': current_cost, 'instr_seq': instr_seq,
                           'previous_solution': previous_solution_dict, 'mem_order': mem_order}
    else:
        flags = {'at-most': args_i.at_most, 'pushed-at-least': args_i.pushed_once,
                 'instruction-order': args_i.instruction_order,
                 'no-output-before-pop': args_i.no_output_before_pop,
                 'inequality-gas-model': args_i.inequality_gas_model,
                 'initial-solution': args_i.initial_solution, 'default-encoding': args_i.default_encoding,
                 'number-instruction-gas-model': args_i.number_instruction_gas_model}
        additional_info = {'tout': args_i.tout, 'solver': args_i.solver, 'current_cost': current_cost,
                           'instr_seq': instr_seq, 'previous_solution': previous_solution_dict, 'mem_order': mem_order}
    return flags, additional_info


# Executes the smt encoding generator from the main script
def execute_syrup_backend(args_i,json_file = None, previous_solution_dict = None, block_name = None, timeout=10):
    # Args_i is None if the function is called from syrup-asm. In this case
    # we assume by default oms, and json_file already contains the sfs dict
    if args_i is None:
        es = initialize_dir_and_streams("oms", block_name)
        json_path = json_file
    else:
        if json_file:
            json_path = json_file
        else:
            json_path = args_i.source

        solver = args_i.solver
        es = initialize_dir_and_streams(solver, json_path)

    b0, bs, user_instr, variables, initial_stack, final_stack, current_cost, instr_seq, mem_order = parse_data(json_path)

    flags, additional_info = initialize_flags_and_additional_info(args_i, current_cost, instr_seq, previous_solution_dict, mem_order)

    additional_info['tout'] = timeout

    generate_smtlib_encoding(b0, bs, user_instr, variables, initial_stack, final_stack, flags, additional_info)

    es.close()


# Executes the gasol encoder combining different blocks in the same SMT problem
def execute_syrup_backend_combined(sfs_dict, instr_sequence_dict, contract_name, solver):
    next_empty_idx = 0
    # Stores the number of previous stack variables to ensures there's no collision
    next_var_idx = 0

    es = initialize_dir_and_streams(solver, contract_name)

    write_encoding(set_logic('QF_LIA'))

    for block in sfs_dict:

        sfs_block = sfs_dict[block]

        log_dict = instr_sequence_dict[block]

        b0, bs, user_instr, variables, initial_stack, final_stack, \
            current_cost, instr_seq, mem_order = parse_data(sfs_block, next_var_idx)

        generate_smtlib_encoding_appending(b0, bs, user_instr, variables, initial_stack, final_stack,
                                           log_dict, next_empty_idx, mem_order)
        next_empty_idx += b0 + 1

        # Next available index for assigning var values is equal to the maximum of previous ones
        if variables:
            next_var_idx = max(map(lambda x: int(re.search('\d+', x).group()), variables)) + 1

    write_encoding(check_sat())
    es.close()


# Given the max stack size (bs) and the user instructions directly from the json, generates four dicts:
# one for the conversion of an opcode id to the corresponding theta value, other for the disasm associated
# to the theta value, another for the bytecode associated to the theta value, and finally, the cost of each
# opcode associated to a theta value.
def generate_theta_dict_from_sequence(bs, usr_instr):
    theta_stack = generate_stack_theta(bs)
    theta_comm, theta_non_comm, theta_mem = generate_uninterpreted_theta(usr_instr, len(theta_stack))
    theta_dict = dict(theta_stack, **theta_comm, **theta_non_comm, **theta_mem)
    instr_map = generate_instr_map(usr_instr, theta_stack, theta_comm, theta_non_comm, theta_mem)
    disasm_map = generate_disasm_map(usr_instr, theta_dict)
    costs_map = generate_costs_ordered_dict(bs, usr_instr, theta_dict)
    value_map = generate_uninterpreted_push_map(usr_instr, theta_dict)
    return theta_dict, instr_map, disasm_map, costs_map, value_map