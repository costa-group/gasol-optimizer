import copy
from collections import defaultdict
from smt_encoding.instructions.encoding_instruction import ThetaValue, InstructionSubset, Id_T
from smt_encoding.instructions.uninterpreted_instruction import UninterpretedInstruction
from typing import Tuple, Dict, List, Set
from smt_encoding.instructions.instruction_dependencies import generate_dependency_graph_minimum
from smt_encoding.instructions.instruction_bounds import InstructionBounds

# Given an instruction, a dict that links each instruction to a lower bound to the number of instructions
# # needed to obtain the output from that dict, and another dict
# that links each instruction to the previous instructions needed to execute that instruction,
# updates both dicts for that instruction and returns the corresponding values associated to the instruction.
def generate_lower_bound_from_instr(instr : Id_T, number_of_instructions_to_execute : Dict[Id_T, int], previous_values : Dict[Id_T, set],
                                dependency_graph : Dict[Id_T, List[Id_T]]) -> Tuple[int, set]:

    # Base case: it has been already analyzed, so we return the values associated.
    if instr in previous_values:
        return number_of_instructions_to_execute[instr], previous_values[instr]

    number_of_instructions_needed = 0
    instructions_dependency = set()

    # Recursive case: we obtain the output for each previous instruction and update the values
    for previous_instr in dependency_graph[instr]:

        previous_number_of_instr_needed, previous_instructions_dependency = \
            generate_lower_bound_from_instr(previous_instr, number_of_instructions_to_execute,
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


def traverse_tree_until_repeated(instr : Id_T, dependency_graph : Dict[Id_T, List[Id_T]],
                                 repeated_instructions: Set[Id_T],
                                 number_of_instructions_to_execute : Dict[Id_T, int],
                                 instructions_dependent_prev_dict : Dict[Id_T, set]) -> int:
    if instr in repeated_instructions:
        # TODO: instead of assigning 0 to memory instrs, we should study the paths and determine whether it is
        # TODO: direct (no memory dependencies in between) o indirect
        if 'STORE' in instr or 'KECCAK' in instr or 'LOAD' in instr:
            return 0
        else:
            return 1

    # No matter the situation in which we find ourselves, current instruction will be considered
    repeated_instructions.update({instr})

    if len(dependency_graph[instr]) == 0:
        return 1

    previous_instructions = instructions_dependent_prev_dict[instr]

    # If the previous instructions contain no repetitions, there is no need to dup
    if len(repeated_instructions.intersection(instructions_dependent_prev_dict[instr])) == 0:
        repeated_instructions.update(previous_instructions)
        return number_of_instructions_to_execute[instr] + 1

    # Otherwise, we need to add the number of instructions from all children
    return sum(traverse_tree_until_repeated(prev_instr, dependency_graph, repeated_instructions,
                                            number_of_instructions_to_execute, instructions_dependent_prev_dict)
               for prev_instr in dependency_graph[instr]) + 1


def generate_prev_instr_from_instr(instr : Id_T, number_of_instructions_to_execute : Dict[Id_T, int],
                                   instructions_dependent_prev_dict : Dict[Id_T, set],
                                   dependency_graph : Dict[Id_T, List[Id_T]]) -> None:

    # Base case: it has been already analyzed, so we return the values associated.
    if instr in number_of_instructions_to_execute:
        return

    instructions_dependent_current = set()
    current_number_of_instructions = 0

    # Recursive case: we obtain the output for each previous instruction and update the values
    for previous_instr in dependency_graph[instr]:

        # Ensure the results have been generated for the previous instruction
        generate_prev_instr_from_instr(previous_instr, number_of_instructions_to_execute,
                                       instructions_dependent_prev_dict, dependency_graph)

        # The instructions that depend on the previous ones correspond to the keys of previous values
        instructions_dependent_prev = instructions_dependent_prev_dict[previous_instr] | {previous_instr}

        # See detailed explanation for more information to understand this step
        repeated_instructions = set(instructions_dependent_current).intersection(instructions_dependent_prev)

        # 0 elements means just add the previous number needed
        if len(repeated_instructions) == 0 or all((len(dependency_graph[rep]) == 0 for rep in repeated_instructions)):
            current_number_of_instructions += number_of_instructions_to_execute[previous_instr] + 1
        else:
            current_number_of_instructions += traverse_tree_until_repeated(previous_instr, dependency_graph,
                                                                           repeated_instructions,
                                                                           number_of_instructions_to_execute,
                                                                           instructions_dependent_prev_dict)
        # We update instructions_dependency
        instructions_dependent_current = instructions_dependent_current.union(instructions_dependent_prev)

    number_of_instructions_to_execute[instr] = current_number_of_instructions
    instructions_dependent_prev_dict[instr] = instructions_dependent_current


# Given the dict containing the dependency among different instructions, we generate
# another dict that links each instruction to the number of instructions that must be
# executed previously to be able to execute that instruction.
def generate_lower_bound_dict(dependency_graph : Dict[Id_T, List[Id_T]]) -> Dict[Id_T, int]:
    previous_values = {}
    number_of_instructions_to_execute = {}
    for instr in dependency_graph:
        generate_lower_bound_from_instr(instr, number_of_instructions_to_execute, previous_values, dependency_graph)

    return number_of_instructions_to_execute


def generate_lower_bound_from_instr_alternative(dependency_graph : Dict[Id_T, List[Id_T]]) -> Dict[Id_T, int]:
    previous_values = {}
    number_of_instructions_to_execute = {}
    for instr in dependency_graph:
        generate_prev_instr_from_instr(instr, number_of_instructions_to_execute, previous_values, dependency_graph)

    return number_of_instructions_to_execute


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

    maximal_elements = list(set(instr_id for instr_id in dependency_graph).difference(
        set(instr_id for id_list in dependency_graph.values() for instr_id in id_list)))
    extended_dependency_graph = copy.deepcopy(dependency_graph)

    # We add a "dummy element" to function as the initial value
    extended_dependency_graph['dummy'] = maximal_elements
    topo_order = iterative_topological_sort(extended_dependency_graph, 'dummy')
    topo_order.pop(0)

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
        lower_bound_by_id = generate_lower_bound_from_instr_alternative(dependency_graph)

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
