import copy

import global_params.paths
from smt_encoding.complete_encoding.synthesis_full_encoding import SMS_T
from smt_encoding.instructions.instruction_factory import InstructionFactory, UninterpretedInstruction
from smt_encoding.instructions.instruction_bounds_with_dependencies import Id_T, InstructionSubset, \
    generate_lower_bound_dict, generate_first_position_instr_cannot_appear
from smt_encoding.instructions.instruction_dependencies import generate_dependency_graph_minimum, \
    generate_dependency_graph_only_instr, generate_dependency_graph_only_memory
from smt_encoding.count_sms_greedy import minsize_from_json
from typing import List, Tuple, Dict
from copy import deepcopy
import networkx as nx
from pathlib import Path


def bounds_from_instructions(instructions : List[UninterpretedInstruction], order_tuples : List[Tuple[Id_T, Id_T]],
                             final_stack : List[str], b0 : int) -> Tuple[Dict[str,int], Dict[str,int]]:
    stack_element_to_id_dict: Dict[str, Id_T] = {instruction.output_stack: instruction.id
                                                 for instruction in instructions if
                                                 instruction.output_stack is not None}

    instr_by_id_dict: Dict[Id_T, UninterpretedInstruction] = {instruction.id: instruction for instruction in
                                                              instructions}

    dependency_graph: Dict[Id_T, List[Id_T]] = generate_dependency_graph_minimum(instructions, order_tuples,
                                                                                 stack_element_to_id_dict)

    dependendent_mem_ids = set(tup[0] for tup in order_tuples)
    non_dependent_mem_ids: List[Id_T] = list(set(instruction.id for instruction in instructions
                                                 if
                                                 instruction.instruction_subset == InstructionSubset.store).difference(
        dependendent_mem_ids))

    lower_bound_by_id = generate_lower_bound_dict(dependency_graph, stack_element_to_id_dict, instr_by_id_dict)

    first_position_not_instr_by_id = generate_first_position_instr_cannot_appear(b0, stack_element_to_id_dict,
                                                                                 final_stack,
                                                                                 dependency_graph, non_dependent_mem_ids,
                                                                                 instr_by_id_dict)
    upper_bound_by_id = {k: (val-1) for k, val in first_position_not_instr_by_id.items()}
    return lower_bound_by_id, upper_bound_by_id


def determine_minlength_from_bounds(lower_bounds: Dict[str, int], upper_bounds: Dict[str, int], b0: int):
    # The min diff determines how many is needed to remove (or add) to the initial b0 to ensure
    # only one of the instructions can appear in an exact position in the sequence and the rest are feasible
    if len(lower_bounds) == 0:
        return 0
    min_diff = min([upper_bounds[key] - lower_bounds[key] for key in lower_bounds])
    return b0 - min_diff


def load_uninterpreted_instructions_from_sms(sms: SMS_T) -> List[UninterpretedInstruction]:
    instr_factory = InstructionFactory()
    uninterpreted_instructions = [instr_factory.create_instruction_json_format(instr_json)
                                  for instr_json in sms['user_instrs']]
    return uninterpreted_instructions


def load_needed_information_from_sms(sms: SMS_T) -> Tuple[List[UninterpretedInstruction], List[Tuple[Id_T, Id_T]], List[str], int]:
    uninterpreted_instructions = load_uninterpreted_instructions_from_sms(sms)
    mem_order = [*sms['storage_dependences'], *sms['memory_dependences']]
    final_stack = sms['tgt_ws']
    b0 = sms['init_progr_len']

    return uninterpreted_instructions, mem_order, final_stack, b0


def extended_json_with_instr_dep_and_bounds(sms: SMS_T) -> SMS_T:
    new_sms = deepcopy(sms)
    uninterpreted_instructions, order_tuples, final_stack, b0 = load_needed_information_from_sms(sms)

    stack_element_to_id_dict: Dict[str, Id_T] = {instruction.output_stack: instruction.id
                                                 for instruction in uninterpreted_instructions if
                                                 instruction.output_stack is not None}

    instr_dep = generate_dependency_graph_only_instr(uninterpreted_instructions, order_tuples, stack_element_to_id_dict)
    lb_dict, ub_dict = bounds_from_instructions(uninterpreted_instructions, order_tuples, final_stack, b0)

    new_sms['instr_dependencies'] = instr_dep
    new_sms['upper_bounds'] = ub_dict
    new_sms['lower_bounds'] = lb_dict

    return new_sms


def minlength_from_json(sms: SMS_T) -> Tuple[int, int]:
    uninterpreted_instructions, order_tuples, final_stack, b0 = load_needed_information_from_sms(sms)
    lb_dict, ub_dict = bounds_from_instructions(uninterpreted_instructions, order_tuples, final_stack, b0)
    return minsize_from_json(sms), determine_minlength_from_bounds(lb_dict, ub_dict, b0)

def extended_json_with_minlength(sms: SMS_T) -> SMS_T:
    new_sms = deepcopy(sms)
    min_instr, min_bounds = minlength_from_json(new_sms)
    new_sms['min_length_instrs'] = min_instr
    new_sms['min_length_bounds'] = min_bounds
    new_sms['min_length'] = max(min_instr, min_bounds)

    return new_sms


def digraph_from_deps(instr_deps, color: str = 'black'):
    """
    Generates a DiGraph considering the information from successors
    """
    graph = nx.DiGraph()
    for instr_id, next_instrs in instr_deps.items():
        graph.add_node(instr_id)
        for successor in next_instrs:
            graph.add_edge(instr_id, successor, color=color)
    return graph


def generate_dot_graph_from_sms(sms: SMS_T, block_name: str):
    """
    Dot graph from sms
    """
    uninterpreted_instructions, order_tuples, final_stack, b0 = load_needed_information_from_sms(sms)

    stack_element_to_id_dict: Dict[str, Id_T] = {instruction.output_stack: instruction.id
                                                 for instruction in uninterpreted_instructions if
                                                 instruction.output_stack is not None}
    for ini_stack_var in sms["src_ws"]:
        stack_element_to_id_dict[ini_stack_var] = ini_stack_var

    instr_dep = generate_dependency_graph_only_instr(uninterpreted_instructions, order_tuples, stack_element_to_id_dict)
    mem_dep = generate_dependency_graph_only_memory(uninterpreted_instructions, order_tuples)
    digraph = digraph_from_deps(instr_dep)

    # Add nodes from memory instructions
    for mem_id, next_mem_ids in mem_dep.items():
        for next_mem_id in next_mem_ids:
            digraph.add_edge(mem_id, next_mem_id, color='red')

    # Rename nodes so that they include both the name of the term and the instruction id that produces it
    renaming_dict = dict()
    for var_term, id_term in stack_element_to_id_dict.items():
        if var_term == id_term:
            renaming_dict[id_term] = f"{var_term}: initial stk"
        else:
            renaming_dict[id_term] = f"{var_term}: {id_term}"

    renamed_digraph = nx.relabel_nodes(digraph, renaming_dict)

    Path(global_params.paths.dot_path).mkdir(exist_ok=True, parents=True)
    nx.nx_agraph.write_dot(renamed_digraph, Path(global_params.paths.dot_path).joinpath(block_name + ".dot"))
