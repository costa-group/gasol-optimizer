#!/usr/bin/python3
import json
import os
from re import split
import shutil
import sys
from typing import Tuple, Optional, List, Dict, Set
from copy import deepcopy
from timeit import default_timer as dtimer
from argparse import ArgumentParser, Namespace

import pandas as pd
from pandas.core.algorithms import duplicated
from pandas.core.internals import blocks
from pandas.core.internals.managers import blockwise_all

import greedy
from gasol_ml import opcodes
from split_stack_calculator.split_calculator import Split_calculator

sys.path.append(os.path.dirname(os.path.realpath(__file__)) + "/gasol_ml")

from collections import defaultdict
import global_params.constants as constants
import global_params.paths as paths
import sfs_generator.ir_block as ir_block
from sfs_generator.gasol_optimization import get_sfs_dict
from sfs_generator.parser_asm import (parse_asm, parse_json_asm,
                                      generate_block_from_plain_instructions,
                                      parse_blocks_from_plain_instructions)
from sfs_generator.utils import process_blocks_split
from verification.sfs_verify import verify_block_from_list_of_sfs, are_equals
from solution_generation.optimize_from_sub_blocks import rebuild_optimized_asm_block, rebuild_optimized_asm_block_minstack
from sfs_generator.asm_block import AsmBlock, AsmBytecode
from sfs_generator.asm_contract import AsmContract
from smt_encoding.block_optimizer import BlockOptimizer, OptimizeOutcome
from solution_generation.ids2asm import asm_from_ids
from verification.forves_verification import compare_forves
from statistics.statistics_from_asm_block import csv_from_asm_block
from global_params.options import OptimizationParams
from greedy.block_generation import greedy_from_json, greedy_standalone
from smt_encoding.json_with_dependencies import extended_json_with_instr_dep_and_bounds, extended_json_with_minlength, generate_dot_graph_from_sms
from dzn.dzn_api import dzn_optimization_from_sms


def init():
    global previous_gas
    previous_gas = 0

    global new_gas
    new_gas = 0

    global previous_size
    previous_size = 0

    global new_size
    new_size = 0

    global new_n_instrs
    new_n_instrs = 0

    global prev_n_instrs
    prev_n_instrs = 0


def select_model_and_config(model: str, criteria: str, i: int) -> Tuple[str, int]:
    configurations = {"bound_size": ("bound_size.pyt", 4), "bound_gas": ("bound_gas.pyt", 4),
                      "opt_size": ("opt_size.pyt", 0),
                      "opt_gas": ("opt_gas.pyt", 0)}

    selected_config = configurations.get(f"{model}_{criteria}", [])
    return f"models/{selected_config[0]}", selected_config[1]


def create_ml_models(params: OptimizationParams) -> None:
    if params.bound_select or params.opt_select:
        import torch
        torch.set_num_threads(1)
        torch.set_num_interop_threads(1)

    # For length, we use the same model as gas. Hence,
    # we cannot use the parameter directly
    criteria = "size" if params.criteria == "size" else "gas"

    if params.bound_select:
        import gasol_ml.bound_predictor as bound_predictor

        model_name, conf = select_model_and_config("bound", criteria, params.bound_select)
        params.bound_model = bound_predictor.ModelQuery(model_name, conf)

    if params.opt_select:
        import gasol_ml.opt_predictor as opt_predictor

        model_name, conf = select_model_and_config("opt", criteria, params.opt_select)
        params.optimized_predictor_model = opt_predictor.ModelQuery(model_name, conf)


def compute_original_sfs_with_simplifications(block: AsmBlock, params: OptimizationParams):
    stack_size = block.source_stack
    block_name = block.block_name
    block_id = block.block_id
    instructions = block.to_plain()

    instructions_to_optimize = block.instructions_to_optimize_plain()

    revert_flag = ("REVERT" in instructions or "RETURN" in instructions) and params.terminal

    block_data = {"instructions": instructions_to_optimize, "input": stack_size}

    fname = params.input_file.split("/")[-1].split(".")[0]

    exit_code, subblocks_list = \
        ir_block.evm2rbr_compiler(file_name=fname, block=block_data, block_name=block_name, block_id=block_id,
                                  simplification=params.rules_enabled, storage=params.split_storage,
                                  size=params.size_rules_enabled, part=params.split_partition,
                                  pop=params.pop_uninterpreted, push=not params.push_basic, revert=revert_flag,
                                  debug_info=params.verbose)

    sfs_dict = get_sfs_dict()

    return sfs_dict, subblocks_list


# Assume optimized criteria and optimized greedy have returned a valid model
def compare_best_block(original_seq: List[AsmBytecode], optimized_superopt: List[AsmBytecode],
                       optimized_greedy: List[AsmBytecode], criterion: str) -> Tuple[List[AsmBytecode], str]:
    if criterion == 'size':
        saved_optimized = sum([instr.bytes_required for instr in original_seq]) - sum([instr.bytes_required for instr in optimized_superopt])
        saved_greedy = sum([instr.bytes_required for instr in original_seq]) - sum([instr.bytes_required for instr in optimized_greedy])

    elif criterion == 'gas':
        saved_optimized = sum([instr.gas_spent for instr in original_seq]) - sum([instr.gas_spent for instr in optimized_superopt])
        saved_greedy = sum([instr.gas_spent for instr in original_seq]) - sum([instr.gas_spent for instr in optimized_greedy])

    else:
        saved_optimized = len(original_seq) - len(optimized_superopt)
        saved_greedy = len(original_seq) - len(optimized_greedy)

    if saved_optimized <= 0 and saved_greedy <= 0:
        return optimized_superopt, 'both_worse_or_equal'
    elif saved_optimized == saved_greedy:
        return optimized_superopt, 'tie'
    elif saved_optimized < saved_greedy:
        return optimized_greedy, 'greedy'
    else:
        return optimized_superopt, 'superopt'


def search_optimal(sfs_block: Dict, params: OptimizationParams, tout: int,
                   block_name: str, iteration: int) -> Tuple[OptimizeOutcome, float, List[str], Optional[List[str]]]:
    """
    Decides which superoptimization algorithm (or greedy standalone) is applied, using the bound by the greedy if
    the corresponding option is enabled. Returns the optimization outcome, the time spent in the search, the ids
    from the optimized sequence and from the greedy algorithm
    """
    # Must come before extended json with instr dep and bounds to apply the new ub to the bounds generation
    if params.ub_greedy and not params.greedy:
        try:
            new_data, _, _, greedy_ids, error = greedy_from_json(sfs_block)
            # Only choose the greedy if the obtained ub is better
            print("GREEDY IDS BEF", greedy_ids)
            # Check there is no error in the generated solution (as to consider it for the greedy)
            if error == 0:
                # For smt, we are only interested in improving the bound
                if len(greedy_ids) < sfs_block['init_progr_len']:
                    sfs_block['init_progr_len'] = len(greedy_ids)

            else:
                greedy_ids = None
        except:
            greedy_ids = None
    else:
        greedy_ids = None

    # Greedy standalone configuration
    if params.greedy:
        optimization_outcome_str, solver_time, optimized_ids = greedy_standalone(sfs_block)
        optimization_outcome = OptimizeOutcome.non_optimal if optimization_outcome_str == "non_optimal" else OptimizeOutcome.error

    elif params.dzn or (params.split_block == "not-ordered" and iteration == 1) or params.split_block == "ordered" or params.split_block == "complete":
        optimization_outcome, solver_time, optimized_ids = dzn_optimization_from_sms(sfs_block, tout, params)

    elif params.split_block == "not-ordered": 
        optimization_outcome, solver_time, optimized_ids = dzn_optimization_from_sms(sfs_block, tout, params, "dzn/evmopt-generic-reorder.mzn")

    # Otherwise, SMT superoptimization
    else:
        optimizer = BlockOptimizer(block_name, sfs_block, params, tout)
        optimization_outcome, solver_time, optimized_ids = optimizer.optimize_block()

    return optimization_outcome, solver_time, optimized_ids, greedy_ids


def choose_best_solution(original_asm: List[AsmBytecode], optimized_asm: List[AsmBytecode],
                         greedy_asm: Optional[List[AsmBytecode]], optimization_outcome: OptimizeOutcome,
                         params: OptimizationParams):
    chosen_solution_tag = None
    if params.ub_greedy:
        criterion = params.criteria

        # Case: no solution found by the superoptimizer and the greedy has found a solution
        if (optimization_outcome == OptimizeOutcome.no_model or optimization_outcome == OptimizeOutcome.unsat) \
                and greedy_asm is not None:
            optimized_asm, chosen_solution_tag = greedy_asm, 'greedy_no_model'

        # Case: both the greedy and the superoptimizer has found no solution
        elif optimization_outcome == OptimizeOutcome.no_model or optimization_outcome == OptimizeOutcome.unsat:
            optimized_asm, chosen_solution_tag = [], 'both_worse_or_equal'

        # Case: no solution found by the greedy algorithm but the superoptimizer has found a solution
        elif greedy_asm is None:
            optimized_asm, chosen_solution_tag = compare_best_block(original_asm, optimized_asm,
                                                                    original_asm, criterion)

        # Case: both the greedy and the superoptimizer have returned a sequence
        else:
            optimized_asm, chosen_solution_tag = compare_best_block(original_asm, optimized_asm, greedy_asm, criterion)

    # We just return the corresponding optimization assembly code and the tag indicating in which situation
    # we have fallen into
    return optimized_asm, chosen_solution_tag


# Given the sequence of bytecodes, the initial stack size, the contract name and the
# block id, returns the output given by the solver, the name given to that block and current gas associated
# to that sequence.
def optimize_block(sfs_dict, params: OptimizationParams) -> List[Tuple[AsmBlock, OptimizeOutcome, float, \
        List[AsmBytecode], Optional[str], int, int, List[str], List[str]]]:
    block_solutions = []

    # in the Ordered mode of splitted optimization, the block is divided and the duplicated elements of the intermediate output
    # stack are eliminated preserving the order. The input portion of the stack is the portion in which we have the same elements
    # we can find in the source_stack (if there is such portion we dont want to modify it). The output portion is the other portion
    block_names = [name for name in sfs_dict]

    if params.split_block == "ordered" or params.split_block == "not-ordered" or params.split_block == "complete": 

        blk1 = sfs_dict[block_names[0]]
        blk2 = sfs_dict[block_names[1]]
        total_length = blk1["init_progr_len"] + blk2["init_progr_len"]

    if params.split_block == "ordered" or params.split_block == "not-ordered": 
        assert len(sfs_dict) == 2 # the ordered and not-ordered execution must be made with two blocks
        element_correspondence = {}
        blk1_tgt = []


        tblk = {}

        
        blk1_tgt = blk1["tgt_ws"]

        element_correspondence, dups = get_blk1_blk2_correspondance(blk1_tgt, sfs_dict[block_names[1]]["src_ws"])

        blk2 = rename_duplicated(blk2, dups)

        #total_blk_calculation
        if len(blk1_tgt) > len(blk2["src_ws"]):

            #tblk.src = blk1.src
            tblk["src_ws"] = [extend_stack_element(100, elem) for elem in blk1["src_ws"]] 

            #tblk.tgt = [blk2.tgt|blk1.src']
            tblk["tgt_ws"] = [extend_stack_element(200, elem) for elem in blk2["tgt_ws"]] \
                           + [extend_stack_element(100, elem) for elem in blk1_tgt[len(blk2["src_ws"]):]] 

        elif len(blk1_tgt) < len(blk2["src_ws"]):
            #tblk.src = [blk1.src|blk2.src']
            tblk["src_ws"] = [extend_stack_element(100, elem) for elem in blk1["src_ws"]] \
                           + [extend_stack_element(200, elem) for elem in blk2["src_ws"][len(blk1_tgt):]] 

            #tblk.tgt = blk2.tgt
            tblk["tgt_ws"] = [extend_stack_element(200, elem) for elem in blk2["tgt_ws"]] 

        else:
            #tblk.src = blk1.src
            tblk["src_ws"] = [extend_stack_element(100, elem) for elem in blk1["src_ws"]]
            #tblk.tgt = blk2.tgt
            tblk["tgt_ws"] = [extend_stack_element(200, elem) for elem in blk2["tgt_ws"]]

    

    # SFS dict of syrup contract contains all sub-blocks derived from a block after splitting
    for i, block_name in enumerate(sfs_dict):
        sfs_block = sfs_dict[block_name]
        initial_solver_bound = sfs_block['init_progr_len']
        original_instr = sfs_block['original_instrs']
        previous_bound = sfs_block['init_progr_len']
        sfs_block['max_sk_sz'] = sfs_block['max_sk_sz'] + 1
        original_block = generate_block_from_plain_instructions(original_instr, block_name)

        if params.bound_model is not None:
            inferred_bound = params.bound_model.eval(sfs_block)
            if inferred_bound == 0:
                new_bound = previous_bound
            else:
                new_bound = min(previous_bound, inferred_bound)
            sfs_block['init_progr_len'] = new_bound

            if params.verbose:
                print(f"Previous bound: {previous_bound} Inferred bound: {inferred_bound} Final bound: {new_bound}")

        # To match previous results, multiply timeout by number of storage instructions
        # TODO devise better heuristics to deal with timeouts
        if params.direct_timeout:
            tout = params.timeout
        else:
            tout = params.timeout * (1 + len([True for instr in sfs_block['user_instrs'] if instr["storage"]]))

        print(f"Optimizing {block_name}... Timeout:{str(tout)}")


        sfs_block = extended_json_with_minlength(extended_json_with_instr_dep_and_bounds(sfs_block))

        aggressive_1 = 10
        aggressive_2 = 10


        if params.split_block == "complete":
            if i == 0: #blk1_modification
                original_length = sfs_block["init_progr_len"] 
                sfs_block["init_progr_len"] = original_length - round(original_length*aggressive_1/100)


            if i == 2: #blk2_modification
                original_length = total_length - len(optimized_asm)
                sfs_block["init_progr_len"] = original_length - round(original_length*aggressive_2/100)

        if params.split_block == "ordered":
            assert len(sfs_dict) == 2

            if i == 0: #blk1_modification
                target = sfs_block["tgt_ws"]

                out_portion, in_portion = separate_stack_portions(sfs_block["src_ws"], target)
                out_portion = eliminate_duplicates(out_portion)
                blk1_tgt = out_portion + in_portion

                target = out_portion + in_portion

                sfs_block["tgt_ws"] = blk1_tgt
                original_length = sfs_block["init_progr_len"] 
                sfs_block["init_progr_len"] = original_length - round(original_length*aggressive_1/100)

            if i == 1: #blk2_modification

                if optimization_outcome == OptimizeOutcome.no_model: # it is not worth to continue
                    continue

                init_stack = [element_correspondence[elem] for elem in blk1_tgt]

                # 1. add the first block variables to the variable list blk2[vars]
                original_var_len = len(sfs_block["vars"])
                variables = merge_unique(sfs_block["vars"], init_stack)
                sfs_block["vars"] = variables

                
                # 2. Modify the input stack by translating from the first block to the second
                sfs_block["src_ws"] = init_stack + eliminate_duplicates(sfs_block["src_ws"])[len(init_stack):]

                # 3. Modify the output stack by translating from the total block to the second (if an element cant be mapped to the second, map to the first)
                tgt_stack = get_tgt_stack(tblk, element_correspondence)
                sfs_block["tgt_ws"] = tgt_stack

                # 4. Modify the bounds (min_stack, min_prog_len...)
                sfs_block["max_sk_sz"] = max(sfs_block["max_sk_sz"] + len(sfs_block["vars"]) - original_var_len, len(tgt_stack), len(sfs_block["src_ws"]))
                original_length = total_length - len(optimized_asm)
                sfs_block["init_progr_len"] = original_length - round(original_length*aggressive_2/100)

                sfs_block = extended_json_with_minlength(extended_json_with_instr_dep_and_bounds(sfs_block))

        if params.split_block == "not-ordered":
            assert len(sfs_dict) == 2

            if i == 0: #blk1_modification
                
                sfs_block["tgt_ws"] = eliminate_duplicates(sfs_block["tgt_ws"])# helps the solver
                original_length = sfs_block["init_progr_len"] 
                sfs_block["init_progr_len"] = original_length - round(original_length*aggressive_1/100)


            if i == 1: #blk2_modification
                if optimization_outcome == OptimizeOutcome.no_model: # it is not worth to continue
                    continue

                blk1_tgt = simulate_execution_from_instr_sequence(optimized_ids, sfs_dict[block_names[0]])

                init_stack = [element_correspondence[elem] for elem in blk1_tgt]

                # 1. add the first block variables to the variable list blk2[vars]
                original_var_len = len(sfs_block["vars"])
                variables = merge_unique(sfs_block["vars"], init_stack)
                sfs_block["vars"] = variables
                
                # 2. Modify the input stack by translating from the optimized target stack of first block to the second (since it has been treated as a set)
                sfs_block["src_ws"] = init_stack + eliminate_duplicates(sfs_block["src_ws"])[len(init_stack):]

                # 3. Modify the output stack by translating from the total block to the second (if an element cant be mapped to the second, map to the first)
                tgt_stack = get_tgt_stack(tblk, element_correspondence)
                sfs_block["tgt_ws"] = tgt_stack

                # 4. Modify the bounds (min_stack, min_prog_len...)
                sfs_block["max_sk_sz"] = max(sfs_block["max_sk_sz"] + len(sfs_block["vars"]) - original_var_len, len(tgt_stack), len(sfs_block["src_ws"]))
                original_length = total_length - len(optimized_asm)
                sfs_block["init_progr_len"] = original_length - round(original_length*aggressive_2/100)

                sfs_block = extended_json_with_minlength(extended_json_with_instr_dep_and_bounds(sfs_block))


        # We have enabled the optimization process (otherwise, we just generate the intermediate SMT files)
        if params.dot_generation:
            generate_dot_graph_from_sms(sfs_block, block_name)
        elif params.optimization_enabled:
            optimization_outcome, solver_time, optimized_ids, greedy_ids = search_optimal(sfs_block, params, tout, block_name, i)
            optimized_asm = asm_from_ids(sfs_block, optimized_ids) if optimized_ids is not None else []
            greedy_asm = asm_from_ids(sfs_block, greedy_ids) if greedy_ids is not None else None

            # We only determine the best solution if we have enabled previously the greedy algorithm
            if params.ub_greedy:
                chosen_seq, chosen_tag = choose_best_solution(original_block.instructions, optimized_asm, greedy_asm, optimization_outcome, params)
            else:
                chosen_seq, chosen_tag = optimized_asm, "greedy_not_enabled"
            block_solutions.append((original_block, optimization_outcome, solver_time,
                                    chosen_seq, chosen_tag, tout, initial_solver_bound, sfs_block['rules'], optimized_ids))
        else:
            optimizer = BlockOptimizer(block_name, sfs_block, params, tout)
            optimizer.generate_intermediate_files()

    return block_solutions


def get_blk1_blk2_correspondance(tgt_stack:List, src_stack:List):
    '''
    Given an tgt stack and source stack of the following block returns a mapping
    elements of the first block to the elements of the second block
    '''

    mapping = {}
    duplicated = defaultdict(list)
    for i, elem in enumerate(tgt_stack):
        if elem in mapping:
            if i < len(src_stack):
                duplicated[mapping[elem]].append(src_stack[i])
            continue

        if i < len(src_stack):
            mapping[elem] = src_stack[i]
        else:
            mapping[elem] = extend_stack_element(100, elem)

    return mapping, duplicated

def rename_duplicated(sfs, dups):
    '''
    Given a block and given a dictionary with the elements that correspond to the same value
    it modifies the block so that the values are unified
    '''

    for elem in dups.keys():
        for dup in dups[elem]:
            sfs["vars"].remove(dup)
            sfs["src_ws"] = rename_list(sfs["src_ws"], dup, elem)
            sfs["tgt_ws"] = rename_list(sfs["tgt_ws"], dup, elem)

            for instr in sfs["user_instrs"]:
                instr["inpt_sk"] = rename_list(instr["inpt_sk"], dup, elem)
                instr["outpt_sk"] = rename_list(instr["outpt_sk"], dup, elem)

    return sfs

def rename_list(lst, fr, to):
    return [to if x == fr else x for x in lst]
    
def extend_stack_element(prefix: int, element: str):
    return f"s({prefix + int(element.replace('s(', '').replace(')', '')) })" # the element has the form s(x)

def reduce_stack_element(element:str):
    return f"s({int(element.replace('s(', '').replace(')', '')[1:]) })" # the element has the form s(x)


def separate_stack_portions(in_stack:List, out_stack:List):
    '''
    An output stack can have two regions, one with elements only used to read and another with calculated values
    Given an input stack and output stack, divide the regions in read only elements and read write elements
    '''
    i = len(in_stack) - 1
    j = len(out_stack) - 1
    common_length = 0

    while i >= 0 and j >= 0 and in_stack[i] == out_stack[j]:
        common_length += 1
        i -= 1
        j -= 1
    
    if common_length == 0:
        return out_stack, []
    else:
        return out_stack[:-common_length], out_stack[-common_length:]


def get_tgt_stack(tblk:dict, corresp:dict):
    '''
    Given the target stack of the whole block, the function translates it to the elements
    found in blk2
    '''
    tgt_stack = []

    for elem in tblk["tgt_ws"]:
        if elem.startswith('s(2'):
            tgt_stack.append(reduce_stack_element(elem))
        else:
            reduced = reduce_stack_element(elem)
            if reduced in corresp:
                tgt_stack.append(corresp[reduced])
            else:
                tgt_stack.append(elem)

    return tgt_stack

def eliminate_duplicates(array:List):
    seen = set()
    return [x for x in array if not (x in seen or seen.add(x))]

def merge_unique(arr1:List, arr2:List):
    seen = set(arr1)
    return arr1 + [x for x in arr2 if not (x in seen or seen.add(x))]
    


# Given the log file loaded in json format, current block and the contract name, generates three dicts: one that
# contains the sfs from each block, the second one contains the sequence of instructions and
# the third one is a set that contains all block ids.
def generate_sfs_dicts_from_log(block, json_log, params: OptimizationParams):
    contracts_dict, sub_block_list = compute_original_sfs_with_simplifications(block, params)
    syrup_contracts = contracts_dict["syrup_contract"]

    # Contains sfs blocks considered to check the SMT problem. Therefore, a block is added from
    # sfs_original iff solver could not find an optimized solution, and from sfs_dict otherwise.
    optimized_sfs_dict = {}

    # Dict that contains all instr sequences
    instr_sequence_dict = {}

    # Set that contains all ids
    ids = set()

    # We need to inspect all sub-blocks in the sfs dict.
    for block_id in syrup_contracts:

        ids.add(block_id)

        # If the id is not at json log, this means it has not been optimized
        if block_id not in json_log:
            continue

        instr_sequence = json_log[block_id]

        sfs_block = syrup_contracts[block_id]

        optimized_sfs_dict[block_id] = sfs_block
        instr_sequence_dict[block_id] = instr_sequence

    return syrup_contracts, optimized_sfs_dict, sub_block_list, instr_sequence_dict, ids


# Given a dict with the sfs from each block and another dict that contains whether previous block was optimized or not,
# generates the corresponding solution. All checks are assumed to have been done previously
def optimize_asm_block_from_log(block, sfs_dict, sub_block_list, instr_sequence_dict: Dict[str, List[str]]):
    # Optimized blocks. When a block is not optimized, None is pushed to the list.
    optimized_blocks = {}

    for sub_block_name, sfs_sub_block in sfs_dict.items():

        if sub_block_name not in instr_sequence_dict:
            optimized_blocks[sub_block_name] = None
        else:
            new_sub_block = asm_from_ids(sfs_sub_block, instr_sequence_dict[sub_block_name])
            optimized_blocks[sub_block_name] = new_sub_block

    new_block = rebuild_optimized_asm_block(block, sub_block_list, optimized_blocks)

    return new_block


def optimize_asm_from_log(params: OptimizationParams, json_log: Dict):
    asm = parse_asm(params.input_file)

    # Blocks from all contracts are checked together. Thus, we first will obtain the needed
    # information from each block
    sfs_dict_to_check, instr_sequence_dict, file_ids = {}, {}, set()
    contracts = []

    for c in asm.contracts:

        new_contract = deepcopy(c)

        # If it does not have the asm field, then we skip it, as there are no instructions to optimize
        if not c.has_asm_field:
            contracts.append(new_contract)
            continue

        contract_name = c.shortened_name
        init_code = c.init_code
        init_code_blocks = []

        print("\nAnalyzing Init Code of: " + contract_name)
        print("-----------------------------------------\n")
        for block in init_code:

            if block.instructions_to_optimize_plain() == []:
                init_code_blocks.append(deepcopy(block))
                continue

            sfs_all, sfs_optimized, sub_block_list, instr_sequence_dict_block, block_ids = \
                generate_sfs_dicts_from_log(block, json_log, params)

            new_block = optimize_asm_block_from_log(block, sfs_all, sub_block_list, instr_sequence_dict_block)
            eq, reason = compare_asm_block_asm_format(block, new_block, params)

            if not eq:
                raise ValueError(f"Error parsing the log file. [REASON]: {reason}")

            init_code_blocks.append(new_block)

        new_contract.init_code = init_code_blocks

        print("\nAnalyzing Runtime Code of: " + contract_name)
        print("-----------------------------------------\n")
        for identifier in c.get_data_ids_with_code():
            blocks = c.get_run_code(identifier)

            run_code_blocks = []

            for block in blocks:

                if block.instructions_to_optimize_plain() == []:
                    run_code_blocks.append(deepcopy(block))
                    continue

                sfs_all, sfs_optimized, sub_block_list, instr_sequence_dict_block, block_ids = \
                    generate_sfs_dicts_from_log(block, json_log, params)

                new_block = optimize_asm_block_from_log(block, sfs_all, sub_block_list, instr_sequence_dict_block)
                eq, reason = compare_asm_block_asm_format(block, new_block, params)

                if not eq:
                    raise ValueError(f"Error parsing the log file. [REASON]: {reason}")

                run_code_blocks.append(new_block)

            new_contract.set_run_code(identifier, run_code_blocks)

        contracts.append(new_contract)

    print("Solution generated from log file has been verified correctly")
    new_asm = deepcopy(asm)
    new_asm.contracts = contracts

    with open(params.optimized_file, 'w') as f:
        f.write(json.dumps(new_asm.to_json()))

    print("")
    print("Optimized code stored at " + params.optimized_file)


def optimize_isolated_asm_block(params: OptimizationParams):
    seqs_rows = []
    blocks_rows = []

    with open(params.input_file, "r") as f:
        instructions = f.read()

    if params.split_block == "ml":
        predicted = predict_split_mode(instructions)

        if predicted == "original":
            params.dzn = True 
            params.split_block = "none"
        else:
            params.split_block = predicted



    blocks: List[AsmBlock] = parse_blocks_from_plain_instructions(instructions, params.block_name, params.block_name_prefix)
    asm_blocks = []

    # split block


    for old_block in blocks:
        asm_block, log_element, statistics_csv = optimize_asm_block_asm_format(old_block, params)
        seqs_rows.extend(statistics_csv)

        eq, reason = compare_asm_block_asm_format(old_block, asm_block, params)


        if not eq:
            print("Comparison failed, so initial block is kept")
            print("\t[REASON]: " + reason)
            print(old_block.to_plain())
            print(asm_block.to_plain())
            print("")
            asm_block = old_block

        update_gas_count(old_block, asm_block)
        update_length_count(old_block, asm_block)
        update_size_count(old_block, asm_block)
        asm_blocks.append(asm_block)

    if params.optimization_enabled:
        print("")
        print("Initial sequence (basic block per line):")
        print('\n'.join([old_block.to_plain_with_byte_number() for old_block in blocks]))
        print("")
        print("Optimized sequence (basic block per line):")
        print('\n'.join([asm_block.to_plain_with_byte_number() for asm_block in asm_blocks]))
        with open(params.optimized_file, 'w') as f:
            f.write('\n'.join([asm_block.to_plain_with_byte_number() for asm_block in asm_blocks]))

        pd.DataFrame(blocks_rows).to_csv(params.blocks_file)
        pd.DataFrame(seqs_rows).to_csv(params.seqs_file)



def update_gas_count(old_block: AsmBlock, new_block: AsmBlock):
    global previous_gas
    global new_gas

    previous_gas += old_block.gas_spent
    new_gas += new_block.gas_spent


def update_size_count(old_block: AsmBlock, new_block: AsmBlock):
    global previous_size
    global new_size

    previous_size += old_block.bytes_required
    new_size += new_block.bytes_required


def update_length_count(old_block: AsmBlock, new_block: AsmBlock):
    global prev_n_instrs
    global new_n_instrs

    prev_n_instrs += len([True for instruction in old_block.instructions if instruction.disasm != 'tag'])
    new_n_instrs += len([True for instruction in new_block.instructions if instruction.disasm != 'tag'])


def generate_statistics_info(original_block: AsmBlock, outcome: Optional[OptimizeOutcome], solver_time: float,
                             optimized_block: AsmBlock, chosen_tag: Optional[str], initial_bound: int, tout: int, rules: List[str]) -> Dict:
    block_name = original_block.block_name
    original_instr = ' '.join(original_block.instructions_to_optimize_plain())

    statistics_row = {"block_id": block_name, "previous_solution": original_instr, "timeout": tout,
                      "initial_n_instrs": initial_bound, 'initial_estimated_size': original_block.bytes_required,
                      'initial_estimated_gas': original_block.gas_spent, 'rules': ','.join(rules),
                      'initial_length': len(original_block.instructions_to_optimize_plain()),
                      'saved_length': 0, 'chosen_block_tag': chosen_tag}

    # The outcome of the solver is unsat
    if outcome == OptimizeOutcome.unsat:
        statistics_row.update(
            {"model_found": False, "shown_optimal": False, "solver_time_in_sec": round(solver_time, 3),
             "saved_size": 0, "saved_gas": 0, 'outcome': 'unsat'})

    # The solver has returned no model
    elif outcome == OptimizeOutcome.no_model:
        statistics_row.update(
            {"model_found": False, "shown_optimal": False, "solver_time_in_sec": round(solver_time, 3),
             "saved_size": 0, "saved_gas": 0, 'outcome': 'no_model'})

    # The solver has returned a valid model
    else:
        shown_optimal = outcome == OptimizeOutcome.optimal
        optimized_size = optimized_block.bytes_required
        optimized_gas = optimized_block.gas_spent
        optimized_length = len(optimized_block.instructions_to_optimize_plain())
        initial_size = original_block.bytes_required
        initial_gas = original_block.gas_spent
        initial_length = len(original_block.instructions_to_optimize_plain())

        statistics_row.update({"solver_time_in_sec": round(solver_time, 3), "saved_size": initial_size - optimized_size,
                               "saved_gas": initial_gas - optimized_gas, "model_found": True,
                               "shown_optimal": shown_optimal,
                               "solution_found": ' '.join([instr.to_plain() for instr in optimized_block.instructions]),
                               "optimized_n_instrs": optimized_length, 'optimized_length': optimized_length,
                               'optimized_estimated_size': optimized_size, 'optimized_estimated_gas': optimized_gas,
                               'outcome': 'model', 'saved_length': initial_length - optimized_length})

    return statistics_row


def improves_criterion(saved_criterion: int, *saved_other):
    if saved_criterion > 0:
        return True
    elif saved_criterion == 0:
        any_improves = False
        for crit in saved_other:
            if crit > 0:
                any_improves = True
            elif crit < 0:
                return False
        return any_improves
    else:
        return False


def block_has_been_optimized(original_block: AsmBlock, optimized_block: AsmBlock,
                             criteria: str) -> bool:
    saved_size = original_block.bytes_required - optimized_block.bytes_required
    saved_gas = original_block.gas_spent - optimized_block.gas_spent
    saved_length = original_block.length - optimized_block.length

    return (criteria == "size" and improves_criterion(saved_size, saved_gas)) or \
        (criteria == "length" and improves_criterion(saved_length, saved_gas, saved_size)) or \
        (criteria == "gas" and improves_criterion(saved_gas, saved_size))


# Given an asm_block and its contract name, returns the asm block after the optimization
def optimize_asm_block_asm_format(block: AsmBlock, params: OptimizationParams) -> Tuple[AsmBlock, Dict, List[Dict]]:
    csv_statistics = []
    new_block = deepcopy(block)

    # Optimized blocks. When a block is not optimized, None is pushed to the list.
    optimized_blocks = {}

    log_dicts = {}

    instructions = block.instructions_to_optimize_plain()

    sfs_dict = {}
    # No instructions to optimize
    if instructions == []:
        return new_block, {}, []


    if params.optimized_predictor_model is not None and params.optimization_enabled:

        stack_size = block.source_stack

        instructions_to_optimize = block.instructions_to_optimize_plain()
        block_data = {"instructions": instructions_to_optimize, "input": stack_size}
        sub_block_list = ir_block.get_subblocks(block_data, storage=params.split_storage, part=params.split_partition)
        subblocks2analyze = [instructions for instructions in process_blocks_split(sub_block_list)]



        for i, subblock in enumerate(subblocks2analyze):
            # If we have an empty sub block, we just consider it has not been optimized and go on with the new block
            if subblock == []:
                continue

            ins_str = " ".join(subblock)
            new_block = parse_blocks_from_plain_instructions(ins_str)[0]
            new_block.set_block_name(block.get_block_name())
            new_block.set_block_id(i)

            out = params.optimized_predictor_model.eval(ins_str)

            # The new sub block name is generated as follows. Important to match the format in the sfs_dict
            sub_block_name = f'{new_block.get_block_name()}_{new_block.get_block_id()}'

            # Out == 1 means the predictors predicts the block won't lead to any optimization, and hence, it's not worthy
            # to try optimization
            if out == 0:
                optimized_blocks[sub_block_name] = None
                if params.verbose:
                    print(f"{block.block_name} has been chosen not to be optimized")

            else:
                try:
                    contracts_dict, _ = compute_original_sfs_with_simplifications(new_block, params)
                except Exception as e:
                    failed_row = {'instructions': instructions, 'exception': str(e)}
                    return new_block, {}, []

                old_name = list(contracts_dict["syrup_contract"].keys())[0]
                sfs_dict[sub_block_name] = contracts_dict["syrup_contract"][old_name]


    else:
        try:
            if params.split_block != "none":

                split_mode = "dag"

                contracts_dict = {}
                syrup_contract = {}
                sub_block_list = []

                #split block
                split_calculator = Split_calculator()

                if split_mode == "min_stack":
                    min_stack, instr_num = split_calculator.calculate_minstack_split(block)

                if split_mode == "dag":
                    contracts_dict_aux, _ = compute_original_sfs_with_simplifications(block, params)

                    sfs_block = contracts_dict_aux["syrup_contract"]["isolated_block_0_0"]

                    sfs_block = extended_json_with_minlength(extended_json_with_instr_dep_and_bounds(sfs_block))

                    min_stack, instr_num = split_calculator.calculate_extended_dao_split(sfs_block)

                #print(f"splittocsv: {min_stack};{instr_num}")


                #create new contracts_dict with the subblocks
                for i, blk in enumerate(block.divide_block(instr_num)):
                    partial_contracts_dict, partial_sub_block_list = compute_original_sfs_with_simplifications(blk, params)

                    syrup_contract[blk.block_name + f"_{i}"] = partial_contracts_dict["syrup_contract"][blk.block_name + "_0"]
                    sub_block_list.extend(partial_sub_block_list)

                contracts_dict["syrup_contract"] = syrup_contract

            else:
                contracts_dict, sub_block_list = compute_original_sfs_with_simplifications(block, params)

        except Exception as e:
            print("exception: ", e)
            failed_row = {'instructions': instructions, 'exception': str(e)}
            return new_block, {}, []

        sfs_dict = contracts_dict["syrup_contract"]

    if not params.optimization_enabled:
        optimize_block(sfs_dict, params)
        return new_block, {}, []

    for sub_block, optimization_outcome, solver_time, optimized_asm, chosen_tag, tout, initial_solver_bound, rules, optimized_log_rep in optimize_block(
            sfs_dict, params):

        optimal_block = AsmBlock('optimized', sub_block.block_id, sub_block.block_name, sub_block.is_init_block)
        optimal_block.instructions = optimized_asm


        statistics_info = generate_statistics_info(sub_block, optimization_outcome, solver_time, optimal_block, chosen_tag,
                                                   initial_solver_bound, tout, rules)

        if "solution_found" in statistics_info:
            statistics_info["forves_checker"] = compare_forves(statistics_info["previous_solution"],
                                                               statistics_info["solution_found"],
                                                               "size" if params.criteria == "size" else "gas",
                                                               params.forves_enabled)
        else:
            statistics_info["forves_checker"] = "true"

        csv_statistics.append(statistics_info)

        # Only check if the new block is considered if the solver has generated a new one
        if optimization_outcome == OptimizeOutcome.non_optimal or optimization_outcome == OptimizeOutcome.optimal:
            sub_block_name = sub_block.block_name

            if params.split_block != "none": 
                optimized_blocks[sub_block_name] = optimized_asm
                log_dicts[sub_block_name] = optimized_log_rep
                new_block = rebuild_optimized_asm_block_minstack(block, sub_block_list, optimized_blocks)
                if not block_has_been_optimized(block, new_block, params.criteria):
                    optimized_blocks = {}
                    log_dicts = {}
                    new_block = rebuild_optimized_asm_block_minstack(block, sub_block_list, optimized_blocks)
                    print("The resulting block was worst than the original")
            else:
                if block_has_been_optimized(sub_block, optimal_block, params.criteria):
                    optimized_blocks[sub_block_name] = optimized_asm
                    log_dicts[sub_block_name] = optimized_log_rep
                else:
                    optimized_blocks[sub_block_name] = None

    if params.split_block == "none":
        new_block = rebuild_optimized_asm_block(block, sub_block_list, optimized_blocks)

    return new_block, log_dicts, csv_statistics


def compare_asm_block_asm_format(old_block: AsmBlock, new_block: AsmBlock, params: OptimizationParams) -> Tuple[bool, str]:
    # Change new block name to store the corresponding sfs with the new change
    original_block_name = new_block.get_block_name()
    new_block.set_block_name("alreadyOptimized_"+ original_block_name)
    new_sfs_information, _ = compute_original_sfs_with_simplifications(new_block, params)
    new_block.set_block_name(original_block_name)

    new_sfs_dict = new_sfs_information["syrup_contract"]

    old_sfs_information, _ = compute_original_sfs_with_simplifications(old_block, params)

    old_sfs_dict = old_sfs_information["syrup_contract"]


    #print("old: ", old_sfs_dict)
    #print("new: ", new_sfs_dict)


    final_comparison, reason = verify_block_from_list_of_sfs(old_sfs_dict, new_sfs_dict)

    # We also must check intermediate instructions match i.e those that are not sub blocks
    initial_instructions_old = old_block.instructions_initial_bytecode()
    initial_instructions_new = new_block.instructions_initial_bytecode()

    final_instructions_old = old_block.instructions_final_bytecode()
    final_instructions_new = new_block.instructions_final_bytecode()

    return final_comparison and (initial_instructions_new == initial_instructions_old) and \
           final_instructions_new == final_instructions_old, reason

def simulate_execution_from_instr_sequence(instr_secuence, sfs):
    '''
    Given an instruction sequence where every instruction is a reference to an entry in sfs["user_instrs"]
    it returns the tgt stack from the src stack of the sfs
    '''
    stack = sfs["src_ws"]

    user_instr_dict = defaultdict(dict)

    for instr in sfs["user_instrs"]:
        user_instr_dict[instr["id"]] = instr

    for instr in instr_secuence:
        temp_stack = stack.copy()
        usr_instr = user_instr_dict[instr]

        if instr.startswith("SWAP"):
            value = int(instr.replace("SWAP", ""))
            stack[0], stack[value] = stack[value], stack[0]

        elif instr.startswith("DUP"):
            value = int(instr.replace("DUP", ""))-1
            stack = [stack[value]] + stack

        elif instr.startswith("POP"):
            stack = stack[1:]

        else:
            temp_stack = temp_stack[len(usr_instr["inpt_sk"]):]
            temp_stack = usr_instr["outpt_sk"] + temp_stack
            stack = temp_stack

    return stack


def csv_from_asm_blocks(old_contract_blocks: List[AsmBlock], new_contract_blocks: List[AsmBlock],
                        params: OptimizationParams) -> List[Dict]:
    return [csv_from_asm_block(old_contract_block, new_contract_block,
                               *compare_asm_block_asm_format(old_contract_block, new_contract_block, params),
                               compare_forves(old_contract_block.to_plain(), new_contract_block.to_plain(),
                                              "size" if params.criteria == "size" else "gas",
                                              params.forves_enabled))
            for old_contract_block, new_contract_block in zip(old_contract_blocks, new_contract_blocks)]


def optimize_asm_contract(c: AsmContract, params: OptimizationParams) -> Tuple[AsmContract, List[Dict], Dict, List[Dict]]:
    seq_rows, log_dicts, blocks_rows = [], {}, []
    new_contract = deepcopy(c)

    # If it does not have the asm field, then we skip it, as there are no instructions to optimize. Same if a
    # contract has been specified and current name does not match.
    contract_name = c.shortened_name
    init_code = c.init_code

    print("\nAnalyzing Init Code of: " + contract_name)
    print("-----------------------------------------\n")

    init_code_blocks = []

    for old_block in init_code:
        optimized_block, log_element, csv_statistics = optimize_asm_block_asm_format(old_block, params)
        seq_rows.extend(csv_statistics)

        eq, reason = compare_asm_block_asm_format(old_block, optimized_block, params)

        if not eq:
            print("Comparison failed, so initial block is kept")
            print("\t[REASON]: " + reason)
            print(old_block.to_plain())
            print(optimized_block.to_plain())
            print("")
            optimized_block = old_block
            log_element = {}

        log_dicts.update(log_element)
        init_code_blocks.append(optimized_block)

        # Deployment size is not considered when measuring it
        update_gas_count(old_block, optimized_block)
        update_length_count(old_block, optimized_block)

    new_contract.init_code = init_code_blocks
    if params.forves_enabled:
        print("Checking optimized basic blocks in init_code with forves...")

    blocks_rows.extend(csv_from_asm_blocks(init_code, init_code_blocks, params))

    print("\nAnalyzing Runtime Code of: " + contract_name)
    print("-----------------------------------------\n")
    for identifier in c.get_data_ids_with_code():
        blocks = c.get_run_code(identifier)

        run_code_blocks = []
        for old_block in blocks:
            optimized_block, log_element, csv_statistics = optimize_asm_block_asm_format(old_block, params)
            seq_rows.extend(csv_statistics)

            eq, reason = compare_asm_block_asm_format(old_block, optimized_block, params)

            if not eq:
                print("Comparison failed, so initial block is kept")
                print("\t[REASON]: " + reason)
                print(old_block.to_plain())
                print(optimized_block.to_plain())
                print("")
                optimized_block = old_block
                log_element = {}

            log_dicts.update(log_element)
            run_code_blocks.append(optimized_block)

            update_gas_count(old_block, optimized_block)
            update_length_count(old_block, optimized_block)
            update_size_count(old_block, optimized_block)

        if params.forves_enabled:
            print("Checking optimized basic blocks in init_code with forves...")

        blocks_rows.extend(csv_from_asm_blocks(blocks, run_code_blocks, params))
        new_contract.set_run_code(identifier, run_code_blocks)
    return new_contract, seq_rows, log_dicts, blocks_rows


def optimize_asm_in_asm_format(params: OptimizationParams):
    seqs_rows = []
    blocks_rows = []

    asm = parse_asm(params.input_file)
    log_dicts = {}
    contracts = []
    new_contract = None

    for c in asm.contracts:
        if not c.has_asm_field or (params.contract is not None and c.shortened_name != params.contract):
            contracts.append(c)
        else:
            new_contract, contract_seq_rows, contract_log_dicts, contract_block_rows = optimize_asm_contract(c, params)
            contracts.append(new_contract)

            # Update the corresponding information
            log_dicts.update(contract_log_dicts)
            seqs_rows.extend(contract_seq_rows)
            blocks_rows.extend(contract_block_rows)

    new_asm = deepcopy(asm)
    new_asm.contracts = contracts

    if params.generate_log:
        with open(params.log_file, "w") as log_f:
            json.dump(log_dicts, log_f)

    if params.optimization_enabled:
        with open(params.optimized_file, 'w') as f:
            if params.contract is not None:
                if new_contract is None or new_contract.shortened_name != params.contract:
                    raise ValueError("Specified contract cannot be found")
                else:
                    f.write(json.dumps(new_contract.to_asm_json()))

            else:
                f.write(json.dumps(new_asm.to_json()))

        pd.DataFrame(seqs_rows).to_csv(params.seqs_file)
        pd.DataFrame(blocks_rows).to_csv(params.blocks_file)


def optimize_asm_from_asm_json(params: OptimizationParams):
    c = parse_json_asm(params.input_file)
    new_contract, contract_seq_rows, contract_log_dicts, contract_block_rows = optimize_asm_contract(c, params)

    if params.generate_log:
        with open(params.log_file, "w") as log_f:
            json.dump(contract_log_dicts, log_f)

    if params.optimization_enabled:
        with open(params.optimized_file, 'w') as f:
            f.write(json.dumps(c.to_asm_json()))

        pd.DataFrame(contract_seq_rows).to_csv(params.seqs_file)
        pd.DataFrame(contract_block_rows).to_csv(params.blocks_file)


def optimize_from_sfs(params: OptimizationParams):
    block_name = 'isolated_block_sfs'

    with open(params.input_file, 'r') as f:
        sfs_dict = json.load(f)

    csv_statistics = []
    for original_block, optimization_outcome, solver_time, optimized_asm, chosen_tag, tout, initial_solver_bound, rules, optimized_log_rep \
            in optimize_block(sfs_dict, params):

        optimal_block = AsmBlock('optimized', original_block.block_id, original_block.block_name,
                                 original_block.is_init_block)
        optimal_block.instructions = optimized_asm

        statistics_info = generate_statistics_info(original_block, optimization_outcome, solver_time, optimal_block, chosen_tag,
                                                   initial_solver_bound, tout, rules)

        csv_statistics.append(statistics_info)
    # print(json.dumps(sfs_dict, indent=4))

    if params.optimization_enabled:
        pd.DataFrame(csv_statistics).to_csv(params.seqs_file)
        print("")
        print("Initial sequence (basic block per line):")
        print(original_block.to_plain_with_byte_number())
        print("")
        print("Optimized sequence (basic block per line):")
        print(optimal_block.to_plain_with_byte_number())


def modify_file_names(params: OptimizationParams) -> None:
    input_file_name = params.input_file.split("/")[-1].split(".")[0]

    if params.optimized_file is None:
        if params.input_format == "block":
            output_file = input_file_name + "_optimized.txt"
        elif params.input_format == "sfs":
            output_file = input_file_name + "_optimized.json"
        elif params.input_format == "single-asm":
            output_file = input_file_name + "_optimized.json"
        elif params.from_log is not None:
            output_file = input_file_name + "_optimized_from_log.json_solc"
        else:
            output_file = input_file_name + "_optimized.json_solc"

        params.optimized_file = output_file

    if params.seqs_file is None:
        params.seqs_file = input_file_name + "_statistics_seq.csv"

    if params.blocks_file is None:
        params.blocks_file = input_file_name + "_statistics_blocks.csv"

    if params.log_file is None:
        params.log_file = input_file_name + ".log"


def options_gasol(ap: ArgumentParser) -> None:
    # Unused options
    # ap.add_argument("-last-constants", "--last-constants", help="It removes the last instructions of a block when they generate a constant value", dest="last_constants", action = "store_true")
    # ap.add_argument("-mem40", "--mem40", help="It assumes that pos 64 in memory is not dependant with variables", action = "store_true")
    input = ap.add_argument_group('Input options')

    input.add_argument('input_path', help='Path to input file that contains the code to optimize. Can be either asm'
                                          'either from the --combined-json asm or --json-asm options, '
                                          'plain instructions or a json containing the SFS. The corresponding flag'
                                          'must be enabled')
    group_input = input.add_mutually_exclusive_group()
    group_input.add_argument("-bl", "--block", help="Enable analysis of a single asm block", action="store_true")
    group_input.add_argument("-sfs", "--sfs", dest='sfs', help="Enable analysis of a single SFS", action="store_true")
    group_input.add_argument("-c", "--contract", dest="contract", action='store',
                             help='Specify the specific contract in the json_solc from the combined json to be optimized. '
                                  'The name of the contract must match the name that appears in the solc file. Produces'
                                  'a json file that only includes the information of the corresponding contract, as if'
                                  'it was produced using the solc option --asm-json.')
    group_input.add_argument("-single-json", "--single-json", dest='json_asm', action="store_true",
                             help="Enables analysis of a single contract generated by the --json-asm option.")

    output = ap.add_argument_group('Output options')

    output.add_argument("-o", help="Path for storing the optimized code", dest='output_path', action='store')
    output.add_argument("-csv", help="CSV file path for the seqs optimization report", dest='seq_csv_path',
                        action='store')
    output.add_argument("-block-csv", help="CSV file path for the blocks optimization report", dest='blocks_file',
                        action='store')

    output.add_argument("-backend", "--backend", action="store_false",
                        help="Disables backend generation, so that only intermediate files are generated")
    output.add_argument("-intermediate", "--intermediate", action="store_true",
                        help="Keeps temporary intermediate files. "
                             "These files contain the sfs representation, smt encoding...")
    output.add_argument("-d", "--debug", help="It prints debugging information", dest='debug_flag', action="store_true")
    output.add_argument("-forves", "--forves", help="Enables the verification via the forves checker",
                        dest='forves_enabled', action="store_true")
    output.add_argument("-dot", "--dot", help="Disables the optimization and generates a dot file for each dependency"
                                              "graph induced by the instructions. Red edges mark memory dependencies",
                        action="store_true", dest="dot_generation")

    log_generation = ap.add_argument_group('Log generation options', 'Options for managing the log generation')

    log_generation.add_argument("-log", "--generate-log", help="Enable log file for verification",
                                action="store_true", dest='log')
    log_generation.add_argument("-dest-log", help="Log output path", action="store", dest='log_stored_final')
    log_generation.add_argument("-optimize-from-log", dest='log_path', action='store', metavar="log_file",
                                help="Generates the same optimized bytecode than the one associated to the log file")

    basic = ap.add_argument_group('SearchOptimal general options',
                                  'Basic options for solving the corresponding constraint solver')

    basic.add_argument("-ub-greedy", "--ub-greedy", dest='ub_greedy', help='Enables greedy algorithm to predict the upper bound', action='store_true')
    basic.add_argument('-greedy', '--greedy', dest='greedy', help='Uses greedy directly to generate the results', action='store_true')
    basic.add_argument('-dzn', '--dzn', dest='dzn', help='Superoptimization via a MiniZinc model', action='store_true')
    basic.add_argument("-solver", "--solver", help="Choose the solver", choices=["z3", "barcelogic", "oms"],
                       default="oms")
    basic.add_argument("-tout", metavar='timeout', action='store', type=int,
                       help="Timeout in seconds. By default, set to 2s per block.", default=2)
    basic.add_argument("-direct-tout", dest='direct_timeout', action='store_true',
                       help="Sets the Max-SMT timeout to -tout directly, "
                            "without considering the structure of the block")
    basic.add_argument("-push0", "--push0", dest='push0_enabled', action='store_false',
                       help="Assumes PUSH0 opcode cannot be used in the optimizations.")
    basic.add_argument('-no-simplification', "--no-simplification", action='store_true', dest='no_simp',
                       help='Disables the application of simplification rules')

    blocks = ap.add_argument_group('Split block options', 'Options for deciding how to split blocks when optimizing')

    blocks.add_argument("-storage", "--storage", help="Split using SSTORE, MSTORE and MSTORE8", action="store_true")
    blocks.add_argument("-partition", "--partition", help="It enables the partition in blocks of 24 instructions",
                        action="store_true")

    hard = ap.add_argument_group('Hard constraints', 'Options for modifying the hard constraint generation')

    hard.add_argument("-memory-encoding", help="Choose the memory encoding model", choices=["l_vars", "direct"],
                      default="direct", dest='memory_encoding')
    hard.add_argument('-push-basic', action='store_true', dest='push_basic',
                      help='Disables push instruction as uninterpreted functions')
    hard.add_argument('-pop-uninterpreted', action='store_true', dest='pop_uninterpreted',
                      help='Encodes pop instruction as uninterpreted functions')
    hard.add_argument('-order-bounds', action='store_false', dest='order_bounds',
                      help='Disables bounds on the position instructions can appear in the encoding')
    hard.add_argument('-empty', action='store_true', dest='empty',
                      help='Consider "empty" value as part of the encoding to reflect some stack position is empty,'
                           'instead of using a boolean term')
    hard.add_argument('-term-encoding', action='store', dest='encode_terms',
                      choices=['int', 'stack_vars', 'uninterpreted_uf', 'uninterpreted_int'],
                      help='Decides how terms are encoded in the SMT encoding: directly as numbers, using stack'
                           'variables or introducing uninterpreted functions', default='uninterpreted_uf')
    hard.add_argument('-terminal', action='store_true', dest='terminal',
                      help='(UNSUPPORTED) Encoding for terminal blocks that end with REVERT or RETURN. '
                           'Instead of considering the full stack order, just considers the two top elements')
    hard.add_argument('-ac', action='store_true', dest='ac_solver',
                      help='(UNSUPPORTED) Commutativity in operations is considered as an extension inside the solver. '
                           'Can only be combined with Z3')

    soft = ap.add_argument_group('Soft constraints', 'Options for modifying the soft constraint generation')
    group = soft.add_mutually_exclusive_group()
    group.add_argument("-size", "--size", action="store_true",
                       help="It enables size cost model for optimization and disables rules that increase the size"
                            "The simplification rules are applied only if they reduce the size")

    group.add_argument("-length", "--length", action="store_true",
                       help="It enables the #instructions cost model. Every possible simplification rule is applied")

    soft.add_argument("-direct-inequalities", dest='direct_soft', action='store_true',
                      help="Soft constraints with inequalities instead of equalities and without grouping")

    additional = ap.add_argument_group('Additional constraints',
                                       'Constraints that can help to speed up the optimization process, but are not '
                                       'necessary')
    additional.add_argument('-at-most', action='store_true', dest='at_most',
                            help='add a constraint for each uninterpreted function so that they are used at most once')
    additional.add_argument('-pushed-once', action='store_true', dest='pushed_once',
                            help='add a constraint to indicate that each pushed value is pushed at least once')
    additional.add_argument("-no-output-before-pop", action='store_false', dest='no_output_before_pop',
                            help='Remove the constraint representing the fact that the previous instruction'
                                 'of a pop can only be a instruction that does not produce an element')
    additional.add_argument('-order-conflicts', action='store_false', dest='order_conflicts',
                            help='Disable the order among the uninterpreted opcodes in the encoding')

    ml_options = ap.add_argument_group('ML Options', 'Options to execute the different ML modules')
    ml_options.add_argument('-bound-model', "--bound-model", action='store_true', dest='bound_select',
                            help="Enable bound regression model")
    ml_options.add_argument('-opt-model', "--opt-model", action='store_true', dest='opt_select',
                            help="Select which representation model is used for the opt classification")

    minizinc_options = ap.add_argument_group('Minizinc Options', 'Options for enabling flags in Minizinc')
    minizinc_options.add_argument('-length-bound', action='store_true', dest='length_bound', help='')
    minizinc_options.add_argument('-gcc-bounds', action='store_true', dest='gcc_bounds', help='')
    minizinc_options.add_argument('-unary-shrink', action='store_true', dest='unary_shrink', help='')
    minizinc_options.add_argument('-binary-shrink', action='store_true', dest='binary_shrink', help='')
    minizinc_options.add_argument('-pop-unused', action='store_true', dest='pop_unused', help='')


    s_o = ap.add_argument_group('Split Options', 'Options for deciding where to split the block')
    split_options = s_o.add_mutually_exclusive_group()
    split_options.add_argument( "-split", help="Choose the split mode", choices=["complete", "ordered", "not-ordered", "none"],
        default="none", dest='split_block')

    split_options.add_argument( "-split-ml", "--split-ml", help="Choose split mode with machine learning", dest='split_block', 
        action='store_const', const='ml')


def parse_encoding_args(ap: ArgumentParser):
    return ap.parse_args()


def split_bytecode_(block):
    """
    Using the imported opcodes module to split the bytecode
    This is assumed to be the implementation of opcodes.split_bytecode_
    """
    return opcodes.split_bytecode_(block)

def transform(op: str) -> str:
    """
    Transform an opcode to its hexadecimal representation
    """
    if op.startswith("#"):
        return op

    return f"{hex(opcodes.get_opcode(op)[0])}"

def parse_block(instruction):
    """
    Process a single instruction by splitting it into opcodes and transforming each opcode
    """

    instruction = instruction.replace('\n', '')

    # Split the instruction into opcodes
    splitted = split_bytecode_(instruction)

    # Transform each opcode to its hexadecimal representation
    ops = [transform(op) for op in splitted]
    
    # Return the list of transformed opcodes
    return ops


def predict_split_mode(text):
    import tensorflow as tf
    import pickle 
    import numpy as np

    text = parse_block(text)

    model = tf.keras.models.load_model('ml_model/model.keras')

    # Tokenizer
    with open('ml_model/tokenizer.pkl', 'rb') as f:
        tokenizer = pickle.load(f)

    # MultiLabelBinarizer
    with open('ml_model/mlb.pkl', 'rb') as f:
        mlb = pickle.load(f)

    num_classes = len(mlb.classes_)

    text = ' '.join(text)

    # Tokeniza igual que en el entrenamiento
    sequences = tokenizer.texts_to_sequences(text)
    padded = tf.keras.preprocessing.sequence.pad_sequences(sequences, maxlen=100)

     # Predicción
    prediccion = model.predict(padded)

    # Check if predicted class is within the known range
    predicted_class_index = np.argmax(prediccion[0])  # Get predicted class index
    predicted = mlb.inverse_transform(np.eye(num_classes)[predicted_class_index].reshape(1, -1))[0][0]

    print(f"Predicted class: {predicted}")
    return predicted

def execute_gasol(params: OptimizationParams):
    global previous_gas
    global new_gas
    global previous_size
    global new_size
    global prev_n_instrs
    global new_n_instrs
    global split_block

    create_ml_models(params)

    split_block = params.split_block

    # If storage or partition flag are activated, the blocks are split using store instructions
    if params.split_storage:
        constants.append_store_instructions_to_split()

    # Set push0 global variable to the corresponding flag
    constants._set_push0(params.push0)

    modify_file_names(params)

    x = dtimer()
    if params.from_log is not None:
        with open(params.from_log) as path:
            log_dict = json.load(path)
            optimize_asm_from_log(params, log_dict)
            if not params.keep_files:
                shutil.rmtree(paths.gasol_path, ignore_errors=True)
            exit(0)

    if params.input_format == "plain":
        optimize_isolated_asm_block(params)
    elif params.input_format == "sfs":
        optimize_from_sfs(params)
    elif params.input_format == "single-asm":
        optimize_asm_from_asm_json(params)
    else:
        optimize_asm_in_asm_format(params)

    y = dtimer()

    print("")
    print("Total time: " + str(round(y - x, 2)) + " s")

    if params.keep_files:
        print("")
        print("Intermediate files stored at " + paths.gasol_path)
    else:
        shutil.rmtree(paths.gasol_path, ignore_errors=True)

    if params.optimization_enabled:
        print("")
        print("Optimized code stored in " + params.optimized_file)
        print("Optimality results stored in " + params.seqs_file)
        print("")
        print("Estimated initial gas: " + str(previous_gas))
        print("Estimated gas optimized: " + str(new_gas))
        print("")
        print("Estimated initial size in bytes: " + str(previous_size))
        print("Estimated size optimized in bytes: " + str(new_size))
        print("")
        print("Initial number of instructions: " + str(prev_n_instrs))
        print("Final number of instructions: " + str(new_n_instrs))

    else:
        print("")
        print("Estimated initial gas: " + str(previous_gas))
        print("")
        print("Estimated initial size in bytes: " + str(previous_size))
        print("")
        print("Initial number of instructions: " + str(new_n_instrs))


def main_gasol():
    # Initialize some global params
    init()
    # Parser used by GASOL
    ap = ArgumentParser(description='GASOL, the EVM super-optimizer')
    options_gasol(ap)
    parsed_args = parse_encoding_args(ap)

    # Optimization Params returns the correposponding variables
    params = OptimizationParams()
    # We need to parse the arguments
    params.parse_args(parsed_args)


    execute_gasol(params)


if __name__ == '__main__':
    main_gasol()
