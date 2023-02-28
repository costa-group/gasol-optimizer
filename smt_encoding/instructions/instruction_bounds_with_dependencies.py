import copy
from collections import defaultdict
from smt_encoding.instructions.encoding_instruction import ThetaValue, InstructionSubset, Id_T
from smt_encoding.instructions.uninterpreted_instruction import UninterpretedInstruction
from typing import Tuple, Dict, List, Set
from smt_encoding.instructions.instruction_dependencies import generate_dependency_graph_minimum
from smt_encoding.instructions.instruction_bounds import InstructionBounds


def iterative_topological_sort(dependency_graph : Dict[Id_T, List[Id_T]], start:Id_T):
    seen = set()
    stack = []    # path variable is gone, stack and order are new
    order = []    # order will be in reverse order at first
    q = [start]
    while q:
        v = q.pop()
        if v not in seen:
            seen.add(v)
            q.extend(dependency_graph[v])

            while stack and v not in dependency_graph[stack[-1]]:
                order.append(stack.pop())
            stack.append(v)

    return stack + order[::-1]   # new return value!


def toposort_instr_dependencies(dependency_graph : Dict[Id_T, List[Id_T]]) -> List[Id_T]:
    maximal_elements = list(set(instr_id for instr_id in dependency_graph).difference(
        set(instr_id for id_list in dependency_graph.values() for instr_id in id_list)))
    extended_dependency_graph = copy.deepcopy(dependency_graph)

    # We add a "dummy element" to function as the initial value
    extended_dependency_graph['dummy'] = maximal_elements
    topo_order = iterative_topological_sort(extended_dependency_graph, 'dummy')
    topo_order.pop(0)
    return topo_order


def number_instr_needed(instr_id: Id_T, is_direct_dep: bool, number_of_instructions_to_execute: Dict[Id_T, int],
                        repeated_instructions: Dict[Id_T, bool],
                        instructions_dependent_prev_dict: Dict[Id_T, Dict[Id_T, bool]],
                        stack_elem_to_id: Dict[str, Id_T], dependency_graph: Dict[Id_T, List[Id_T]],
                        instr_by_id_dict: Dict[Id_T, UninterpretedInstruction]) -> int:

    def needed_instrs_from_id(other_instr_id: Id_T, is_direct: bool) -> int:
        # Empty intersection: hence, just add number of instructions to execute
        if len(set(repeated_instructions.keys()).intersection(instructions_dependent_prev_dict[other_instr_id].keys())) == 0:
            # Update dict with visited instructions
            repeated_instructions.update(instructions_dependent_prev_dict[other_instr_id])
            return number_of_instructions_to_execute[other_instr_id]
        else:
            return number_instr_needed(other_instr_id, is_direct, number_of_instructions_to_execute, repeated_instructions,
                                       instructions_dependent_prev_dict, stack_elem_to_id, dependency_graph,
                                       instr_by_id_dict)

    # Base case: it has been already analyzed, so we return the values associated.
    if instr_id in repeated_instructions:
        was_direct_dep = repeated_instructions[instr_id]

        # Update: if any it was already direct or now it has become direct, we store it
        repeated_instructions[instr_id] = was_direct_dep or is_direct_dep

        # We only add one if current occurrence of instr was already direct (i.e. occurred a subexpression)
        # and current one is too
        if was_direct_dep and is_direct_dep:
            return 1
        # All the other cases correspond to 0
        else:
            return 0

    repeated_instructions[instr_id] = is_direct_dep

    dependent_instr_ids = dependency_graph[instr_id]
    instr = instr_by_id_dict[instr_id]

    # The instruction itself counts as 1
    current_number_of_instructions = 1
    analyzed_instr_ids = set()

    # print(instr_id, repeated_instructions)
    # Recursive case: we obtain the output for each previous instruction and update the values
    for stack_elem in instr.input_stack:

        if stack_elem in stack_elem_to_id:
            previous_instr_id = stack_elem_to_id[stack_elem]
            # print('id',previous_instr_id, current_number_of_instructions, repeated_instructions)
            analyzed_instr_ids.add(previous_instr_id)
            current_number_of_instructions += needed_instrs_from_id(previous_instr_id, True)
        else:
            # print('ini', stack_elem, current_number_of_instructions, repeated_instructions)

            # If an initial stack element has already appeared (i.e. included to repeated instructions)
            # we add one because we need to duplicate it
            if stack_elem in repeated_instructions:
                current_number_of_instructions += 1
            # Even if this does not correspond to an instruction
            repeated_instructions[stack_elem] = True

    # Indirect dependencies are dealt similar, but being careful when repetitions occur
    for prev_instr_id in set(dependent_instr_ids).difference(analyzed_instr_ids):
        # print('mem', prev_instr_id, current_number_of_instructions, repeated_instructions)

        current_number_of_instructions += needed_instrs_from_id(prev_instr_id, False)

    # print('return', instr_id, current_number_of_instructions, repeated_instructions)
    return current_number_of_instructions


# Given the dict containing the dependency among different instructions, we generate
# another dict that links each instruction to the number of instructions that must be
# executed previously to be able to execute that instruction.
def generate_lower_bound_dict(dependency_graph: Dict[Id_T, List[Id_T]], stack_elem_to_id: Dict[str, Id_T],
                              instr_by_id_dict: Dict[Id_T, UninterpretedInstruction]) -> Dict[Id_T, int]:

    # If no instructions are considered, just return the empty dict
    if dependency_graph == []:
        return dict()

    # As the dependency relation among instructions is represented as a happens-before, we need to reverse the
    # toposort to start with the deepest elements
    topo_order = list(reversed(toposort_instr_dependencies(dependency_graph)))

    # Initialize all auxiliary data structures
    n_instrs_execute = dict()
    instructions_dependent_prev_dict = dict()

    # Traverse the topo order to generate the number of instructions needed
    for instr_id in topo_order:
        repeated_instrs = {}
        n_instrs_execute[instr_id] = number_instr_needed(instr_id, True, n_instrs_execute, repeated_instrs,
                                                         instructions_dependent_prev_dict, stack_elem_to_id,
                                                         dependency_graph, instr_by_id_dict)
        instructions_dependent_prev_dict[instr_id] = repeated_instrs

    # Finally, to obtain the first position instructions can appear in a sequence, we just need to substract one
    # to the number of instructions needed
    first_position_instr = {k: (v-1) for k,v in n_instrs_execute.items()}
    return first_position_instr


def update_current_index(instr_id: Id_T, bounds_positions: Dict[Id_T, List[int]], new_idx: int) -> None:
    # First value associated corresponds to the min so far, and the other to the max
    if instr_id not in bounds_positions:
        bounds_positions[instr_id] = [new_idx, new_idx]
    else:
        current_min, current_max = bounds_positions[instr_id]
        bounds_positions[instr_id] = [min(new_idx, current_min), max(new_idx, current_max)]


# First time an instruction cannot appear is b0-h, where h is the tree height. We recursively obtain this value,
# taking into account that we may have different trees and the final value is the min for all possible ones
def update_with_tree_level(stack_elem_to_id : Dict[str, Id_T], instr_by_id_dict : Dict[Id_T, UninterpretedInstruction],
                           dependency_graph: Dict[Id_T, List[Id_T]], topological_order: List[Id_T], bounds_positions: Dict[Id_T, List[int]]) -> None:

    for instr_id in topological_order:
        instr = instr_by_id_dict[instr_id]

        # If an instruction is not commutative, then only topmost previous element can be obtained
        # just before and the remaining ones need at least a SWAP to be placed in their position
        dependent_instr_ids = dependency_graph[instr_id]

        # Already analyzed instruction ids
        analyzed_instr_ids = set()
        min_index, max_index = bounds_positions[instr_id]
        index_l = [min_index - 1, max_index - 1]

        for prev_instr_stack_var in instr.input_stack:
            for possible_index in index_l:

                if prev_instr_stack_var in stack_elem_to_id:
                    prev_instr_id = stack_elem_to_id[prev_instr_stack_var]
                    analyzed_instr_ids.add(prev_instr_id)
                    update_current_index(prev_instr_id, bounds_positions, possible_index)

            # If an instruction is not commutative, then only topmost previous element can be obtained
            # just before and the remaining ones need at least a SWAP to be placed in their position
            if instr.instruction_subset != InstructionSubset.comm:
                index_l = [min_index - 2, max_index - 2]

        # There can be other related instructions that are not considered before (mem instructions). As we do not know
        # exactly where they can appear, we assume worst case (current_idx - 1)
        index_l = [min_index - 1, max_index - 1]

        for prev_instr_id in set(dependent_instr_ids).difference(analyzed_instr_ids):
            for possible_index in index_l:
                update_current_index(prev_instr_id, bounds_positions, possible_index)


def initialize_bound_positions_for_ub(b0: int, final_stack_ids: List[Id_T], maximal_mem_ids: List[Id_T],
                                      bounds_positions: Dict[Id_T, List[int]]):
    # If first instruction corresponds to top of the stack, we initialize the search with b0. Otherwise,
    # it means that another extra instruction must be performed after this, and thus, we start searching with b0 - 1.
    b0_aux = b0

    # We consider instructions in the final stack, as they determine which position is the last possible one (following
    # the dependencies to reach it). We are assuming each other instruction is related to these instructions. Otherwise,
    # it would mean that there exists some intermediate instructions that do not affect the final results and thus,
    # they must be omitted.
    for final_instr_id in final_stack_ids:

        # Only those stack elements tied to an instruction must be considered, not initial stack values
        if final_instr_id is not None:
            update_current_index(final_instr_id, bounds_positions, b0_aux)

        # If it isn't top of the stack, another instruction must go before it (SWAP or DUP). Only works once
        b0_aux = b0 - 1

    for mem_instr_id in maximal_mem_ids:
        update_current_index(mem_instr_id, bounds_positions, b0)


# Generates a dict that given b0, returns the first position in which a instruction cannot appear
# due to dependencies with other instructions.
def generate_first_position_instr_cannot_appear(b0 : int, stack_elem_to_id : Dict[str, Id_T],
                                                final_stack : List[str], dependency_graph : Dict[Id_T, List[Id_T]],
                                                maximal_mem_ids : List[Id_T],
                                                instr_by_id_dict : Dict[Id_T, UninterpretedInstruction]) -> Dict[Id_T, int]:
    # Assume there is always at least one element
    if dependency_graph == []:
        return dict()

    bound_positions = dict()

    final_stack_ids = [stack_elem_to_id[stack_var] if stack_var in stack_elem_to_id else None for stack_var in final_stack]
    initialize_bound_positions_for_ub(b0, final_stack_ids, maximal_mem_ids, bound_positions)

    topo_order = toposort_instr_dependencies(dependency_graph)

    update_with_tree_level(stack_elem_to_id, instr_by_id_dict, dependency_graph, topo_order, bound_positions)

    return {instr_id: (bounds[0] if instr_by_id_dict[instr_id].unique_ui else bounds[1])
            for instr_id, bounds in bound_positions.items()}


class InstructionBoundsWithDependencies(InstructionBounds):

    def __init__(self, instructions : List[UninterpretedInstruction], order_tuples : List[List[Id_T]],
                 final_stack : List[str], b0 : int, initial_idx: int = 0):

        stack_element_to_id_dict : Dict[str, Id_T] = {instruction.output_stack : instruction.id
                                                      for instruction in instructions if instruction.output_stack is not None}

        instr_by_id_dict : Dict[Id_T, UninterpretedInstruction] = {instruction.id : instruction for instruction in instructions}

        dependency_graph : Dict[Id_T, List[Id_T]] = generate_dependency_graph_minimum(instructions, order_tuples, stack_element_to_id_dict)

        # To obtain the upper bounds, we need to consider the maximal STORE's i.e. STORE instructions that don't have
        # to appear before another memory instruction
        dependendent_mem_ids = set(tup[0] for tup in order_tuples)
        non_dependent_mem_ids : List[Id_T] = list(set(instruction.id for instruction in instructions
                                                      if instruction.instruction_subset == InstructionSubset.store).difference(dependendent_mem_ids))

        self._b0 = b0
        self._initial_idx = initial_idx
        lower_bound_by_id = generate_lower_bound_dict(dependency_graph, stack_element_to_id_dict, instr_by_id_dict)

        self._lower_bound_by_theta_value = {instr_by_id_dict[instr_id].theta_value: lb
                                            for instr_id, lb in lower_bound_by_id.items() if instr_id != 'PUSH'}
        first_position_not_instr_by_id = generate_first_position_instr_cannot_appear(b0, stack_element_to_id_dict, final_stack,
                                                                                     dependency_graph, non_dependent_mem_ids, instr_by_id_dict)
        self._first_position_not_instr_by_theta_value =  {instr_by_id_dict[instr_id].theta_value : lb
                                                          for instr_id, lb in first_position_not_instr_by_id.items()
                                                          if instr_id != 'PUSH'}

    def lower_bound_theta_value(self, theta_value : ThetaValue) -> int:
        return self._lower_bound_by_theta_value.get(theta_value, self._initial_idx)

    def upper_bound_theta_value(self, theta_value : ThetaValue) -> int:
        return self._first_position_not_instr_by_theta_value.get(theta_value, self._b0) - 1 + self._initial_idx

    @property
    def first_position_sequence(self) -> int:
        return self._initial_idx

    @property
    def last_position_sequence(self) -> int:
        return self._b0 - 1 + self._initial_idx
