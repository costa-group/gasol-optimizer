from smt_encoding.instructions.encoding_instruction import Id_T
from smt_encoding.instructions.uninterpreted_instruction import UninterpretedInstruction
from typing import Tuple, Dict, List


# We generate a dict that given the id of an instruction, returns
# the id of instructions that must be executed to obtain its input and the corresponding
# aj. Note that aj must be only assigned when push, in other cases we just set aj value to -1.
def generate_dependency_graph_minimum(uninterpreted_instr : List[UninterpretedInstruction], order_tuples : List[Tuple[Id_T, Id_T]],
                                      stack_elem_to_id : Dict[str, Id_T]) -> Dict[Id_T, List[Id_T]]:
    dependency_graph = {}
    for instr in uninterpreted_instr:
        instr_id = instr.id
        dependency_graph[instr_id] = []

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
        # Stronger check: if id1 happens before id2 at some point, then we don't consider it in the graph.
        # See test_lb_tight_dependencies in tests/test_instruction_bounds_with_dependencies
        dependency_graph[id2].append(id1)

    return dependency_graph


def generate_dependency_graph_only_memory(uninterpreted_instr: List[UninterpretedInstruction],
                                          order_tuples: List[Tuple[Id_T, Id_T]]) -> Dict[Id_T, List[Id_T]]:
    dependency_graph = {instr.id: [] for instr in uninterpreted_instr}
    # We need to consider also the order given by the tuples
    for id1, id2 in order_tuples:
        # Stronger check: if id1 happens before id2 at some point, then we don't consider it in the graph.
        # See test_lb_tight_dependencies in tests/test_instruction_bounds_with_dependencies
        if not happens_before(id2, id1, dependency_graph):
            dependency_graph[id2].append(id1)
    return dependency_graph


def generate_dependency_graph_transitive_closure(uninterpreted_instr : List[UninterpretedInstruction], order_tuples : List[Tuple[Id_T, Id_T]],
                                                 stack_elem_to_id : Dict[str, Id_T]) -> Dict[Id_T, List[Id_T]]:
    """
    Generates a dict that given an element f2, returns ALL the elements f1 such that f1 sqsubset f2
    :param uninterpreted_instr:
    :param order_tuples:
    :param stack_elem_to_id:
    :return:
    """
    previous_dependency_graph = generate_dependency_graph_minimum(uninterpreted_instr, order_tuples, stack_elem_to_id)
    is_fixed_point = False
    while not is_fixed_point:
        is_fixed_point = True
        current_dependency_graph = dict()

        for current_id, dependent_ids in previous_dependency_graph.items():
            new_dependent_ids = {previous_dependency_graph[previous_id] for previous_id in dependent_ids}
            current_dependency_graph[current_id] = new_dependent_ids.union(dependent_ids)

            if is_fixed_point:
                # Check if some new element has been added. If so, then it is not a fixed point
                is_fixed_point = new_dependent_ids.intersection(dependent_ids) == set()

        previous_dependency_graph = current_dependency_graph

    return previous_dependency_graph