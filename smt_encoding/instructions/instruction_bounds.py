import itertools

from smt_encoding.instructions.encoding_instruction import ThetaValue, InstructionSubset, Id_T
from smt_encoding.instructions.uninterpreted_instruction import UninterpretedFunction
from typing import Tuple, Dict, List

# We generate a dict that given the id of an instruction, returns
# the id of instructions that must be executed to obtain its input and the corresponding
# aj. Note that aj must be only assigned when push, in other cases we just set aj value to -1.
def generate_dependency_graph(uninterpreted_instr : List[UninterpretedFunction], order_tuples : List[Tuple[Id_T, Id_T]],
                              stack_elem_to_id : Dict[str, Id_T]) -> Dict[Id_T, List[Id_T]]:
    dependency_graph = {}
    for instr in uninterpreted_instr:
        instr_id = instr.id
        dependency_graph[instr_id] = list()

        for stack_elem in instr.input_stack:

            # We search for another instruction that generates the
            # stack elem as an output and add it to the set
            if type(stack_elem) == str:

                # This means the stack element corresponds to another uninterpreted instruction
                if stack_elem in stack_elem_to_id:
                    dependency_graph[instr.id].append(stack_elem_to_id[stack_elem])

            # If we have an int, then we must perform a PUSHx to obtain that value
            else:
                dependency_graph[instr_id].append('PUSH')
                if 'PUSH' not in dependency_graph:
                    dependency_graph['PUSH'] = []

    # We need to consider also the order given by the tuples
    for id1, id2 in order_tuples:
        # Check it has not been added yet
        if id1 not in dependency_graph.get(id2, []):
            dependency_graph[id2].append(id1)

    return dependency_graph


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


# Given the dict containing the dependency among different instructions, we generate
# another dict that links each instruction to the number of instructions that must be
# executed previously to be able to execute that instruction.
def generate_lower_bound_dict(dependency_graph : Dict[Id_T, List[Id_T]]) -> Dict[Id_T, int]:
    previous_values = {}
    number_of_instructions_to_execute = {}
    for instr in dependency_graph:
        generate_lower_bound_from_instr(instr, number_of_instructions_to_execute, previous_values, dependency_graph)

    return number_of_instructions_to_execute


# First time an instruction cannot appear is b0-h, where h is the tree height. We recursively obtain this value,
# taking into account that we may have different trees and the final value is the min for all possible ones
def update_with_tree_level(instr : UninterpretedFunction, current_idx : int, stack_elem_to_id : Dict[str, Id_T],
                           instr_by_id_dict : Dict[Id_T, UninterpretedFunction], dependency_graph: Dict[Id_T, List[Id_T]],
                           first_position_instr_cannot_appear : Dict[Id_T, int]) -> None:

    instr_id = instr.id

    # Neither we consider push instructions nor instructions that already have appeared and appear before the best
    # result so far. On the other hand, if current index <= already considered index, we need to traverse the tree in order to
    # update the values, as we neet to consider the biggest position in which the instruction cannot appear
    if instr_id in first_position_instr_cannot_appear and current_idx > first_position_instr_cannot_appear[instr_id]:
        return

    first_position_instr_cannot_appear[instr_id] = current_idx

    # If an instruction is not commutative, then only topmost previous element can be obtained
    # just before and the remaining ones need at least a SWAP to be placed in their position
    dependent_instr_ids = set(dependency_graph[instr_id])

    # Already analyzed instruction ids
    analyzed_instr_ids = set()
    previous_idx = current_idx - 1
    for prev_instr_stack_var in instr.input_stack:

        if prev_instr_stack_var in stack_elem_to_id:
            prev_instr_id = stack_elem_to_id[prev_instr_stack_var]
            analyzed_instr_ids.add(prev_instr_id)
            update_with_tree_level(instr_by_id_dict[prev_instr_id], previous_idx, stack_elem_to_id, instr_by_id_dict,
                                   dependency_graph, first_position_instr_cannot_appear)

        # If an instruction is not commutative, then only topmost previous element can be obtained
        # just before and the remaining ones need at least a SWAP to be placed in their position
        if instr.instruction_subset != InstructionSubset.comm:
            previous_idx = current_idx - 2

    # There can be other related instructions that are not considered before (mem instructions). As we do not know exactly
    # where they can appear, we assume worst case (current_idx - 1)
    for prev_instr_id in dependent_instr_ids.difference(set(analyzed_instr_ids)):

        # Special case: PUSH basic opcode is just omitted
        if prev_instr_id == "PUSH":
            continue
        update_with_tree_level(instr_by_id_dict[prev_instr_id], current_idx - 1, stack_elem_to_id, instr_by_id_dict,
                               dependency_graph, first_position_instr_cannot_appear)


# Generates a dict that given b0, returns the first position in which a instruction cannot appear
# due to dependencies with other instructions.
def generate_first_position_instr_cannot_appear(b0 : int, stack_elem_to_id : Dict[str, Id_T],
                                                final_stack : List[str], dependency_graph : Dict[Id_T, List[Id_T]],
                                                mem_ids : List[Id_T], instr_by_id_dict : Dict[Id_T, UninterpretedFunction]) -> Dict[Id_T, int]:
    if 'PUSH' in dependency_graph:
        first_position_instr_cannot_appear = {'PUSH' : b0}
    else:
        first_position_instr_cannot_appear = {}

    # We consider instructions in the final stack, as they determine which position is the last possible one (following
    # the dependencies to reach it). We are assuming each other instruction is related to these instructions. Otherwise,
    # it would mean that there exists some intermediate instructions that do not affect the final results and thus,
    # they must be omitted.
    final_stack_with_ids = [stack_elem_to_id[stack_var] if stack_var in stack_elem_to_id else None for stack_var in final_stack]

    # If first instruction corresponds to top of the stack, we initialize the search with b0. Otherwise,
    # it means that another extra instruction must be performed after this, and thus, we start searching with b0 - 1.
    b0_aux = b0

    for final_instr_id in final_stack_with_ids:

        # Only those stack elements tied to an instruction must be considered, not initial stack values
        if final_instr_id is not None:
            update_with_tree_level(instr_by_id_dict[final_instr_id], b0_aux, stack_elem_to_id, instr_by_id_dict,
                               dependency_graph, first_position_instr_cannot_appear)

        # If it isn't top of the stack, another instruction must go before it (SWAP or DUP). Only works once
        b0_aux = b0 - 1

    for final_instr_id in mem_ids:
        update_with_tree_level(instr_by_id_dict[final_instr_id], b0, stack_elem_to_id, instr_by_id_dict,
                               dependency_graph, first_position_instr_cannot_appear)

    return first_position_instr_cannot_appear


class InstructionBounds:

    def __init__(self, instructions : List[UninterpretedFunction], order_tuples : List[Tuple[Id_T, Id_T]], final_stack : List[str], b0 : int):
        stack_element_to_id_dict : Dict[str, Id_T] = {instruction.output_stack : instruction.id
                                                      for instruction in instructions if instruction.output_stack is not None}

        instr_by_id_dict : Dict[Id_T, UninterpretedFunction] = {instruction.id : instruction for instruction in instructions}

        dependency_graph : Dict[Id_T, List[Id_T]] = generate_dependency_graph(instructions, order_tuples, stack_element_to_id_dict)

        id_dict_to_theta_value: Dict[Id_T, ThetaValue] = {instruction.id: instruction.theta_value for instruction in instructions}

        # Dependent instructions according to their Theta Value
        self._dependency_instructions : Dict[ThetaValue, List[ThetaValue]] = \
            {id_dict_to_theta_value[instr_id] : [id_dict_to_theta_value[instr_dep_id] for instr_dep_id in instr_dep_ids]
             for instr_id, instr_dep_ids in dependency_graph.items()}

        mem_ids : List[Id_T] = [instruction.id for instruction in instructions if instruction.instruction_subset == InstructionSubset.store]

        self._b0 = b0
        lower_bound_by_id = generate_lower_bound_dict(dependency_graph)
        self._lower_bound_by_theta_value = {instr_by_id_dict[instr_id].theta_value : lb for instr_id, lb in lower_bound_by_id.items()}
        first_position_not_instr_by_id = generate_first_position_instr_cannot_appear(b0, stack_element_to_id_dict, final_stack,
                                                                                     dependency_graph, mem_ids, instr_by_id_dict)
        self._first_position_not_instr_by_theta_value =  {instr_by_id_dict[instr_id].theta_value : lb
                                                          for instr_id, lb in first_position_not_instr_by_id.items()}


    def lower_bound_theta_value(self, theta_value : ThetaValue) -> int:
        return self._lower_bound_by_theta_value.get(theta_value, 0)


    def upper_bound_theta_value(self, theta_value : ThetaValue) -> int:
        return self._first_position_not_instr_by_theta_value.get(theta_value, self._b0) - 1


    def dependent_instructions_theta_value(self, theta_value : ThetaValue) -> List[ThetaValue]:
        return self._dependency_instructions.get(theta_value, [])
