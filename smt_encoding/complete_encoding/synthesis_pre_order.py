from smt_encoding.complete_encoding.synthesis_variables import SynthesisVariables
from smt_encoding.constraints.connector_factory import add_eq, add_lt
from smt_encoding.constraints.assertions import AssertHard
from typing import List, Dict, Set
from smt_encoding.instructions.encoding_instruction import ThetaValue, Id_T
from smt_encoding.instructions.instruction_bounds import InstructionBounds
from smt_encoding.instructions.encoding_instruction import EncodingInstruction

# Methods for generating the constraints for both memory and storage (Ls)


def mem_variable_equivalence_constraint(j : int, theta_uninterpreted : ThetaValue, sv : SynthesisVariables) -> AssertHard:
    left_term = add_eq(sv.t(j), theta_uninterpreted)
    right_term = add_eq(sv.l(theta_uninterpreted), j)
    return AssertHard(add_eq(left_term, right_term))


# Note that the instructions must verify store1 < store2
def l_variable_order_constraint(theta_uninterpreted_1 : ThetaValue, theta_uninterpreted_2 : ThetaValue, sv : SynthesisVariables) -> AssertHard:
    return AssertHard(add_lt(sv.l(theta_uninterpreted_1), sv.l(theta_uninterpreted_2)))


def l_conflicting_constraints_from_theta_values(l_theta_values : List[ThetaValue], bounds : InstructionBounds,
                                                dependency_graph_set_theta: Dict[ThetaValue, Set[ThetaValue]],
                                                sv : SynthesisVariables) -> List[AssertHard]:
    constraints = []

    for theta_value in l_theta_values:
        for pos in range(bounds.lower_bound_theta_value(theta_value), bounds.upper_bound_theta_value(theta_value) + 1):
            constraints.append(mem_variable_equivalence_constraint(pos, theta_value, sv))
            constraints.extend([l_variable_order_constraint(conflicting_theta_value, theta_value, sv)
                                for conflicting_theta_value in dependency_graph_set_theta[theta_value]])
    return constraints

def l_conflicting_theta_values(instructions : List[EncodingInstruction]) -> List[ThetaValue]:
    """
    Filter those instructions that have a l instruction tied to them. These instructions correspond to the ones
    that appear exactly once in the sequence, and hence, they are only tied to one position.

    :param instructions: list of instructions
    :return: list of theta values
    """
    return [instruction.theta_value for instruction in instructions if instruction.unique_ui]


def l_conflicting_constraints(instructions : List[EncodingInstruction], bounds : InstructionBounds,
                              dependency_graph : Dict[Id_T, List[Id_T]], sv : SynthesisVariables) -> List[AssertHard]:
    l_theta_values = l_conflicting_theta_values(instructions)
    theta_value_by_id_dict: Dict[Id_T, ThetaValue] = {instruction.id: instruction.theta_value for instruction in instructions}
    dependency_graph_set_theta = {theta_value_by_id_dict[instr_id] : {theta_value_by_id_dict[dependent_id] for dependent_id in dependency_ids}
                              for instr_id, dependency_ids in dependency_graph}
    return l_conflicting_constraints_from_theta_values(l_theta_values, bounds, dependency_graph_set_theta, sv)