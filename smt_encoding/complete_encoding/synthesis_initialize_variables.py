from smt_encoding.constraints.function import ExpressionReference
from typing import List, Union
from smt_encoding.constraints.assertions import AssertHard
from smt_encoding.constraints.connector_factory import add_and, add_eq, add_not, add_distinct, add_or
from smt_encoding.complete_encoding.synthesis_functions import SynthesisFunctions
from smt_encoding.instructions.encoding_instruction import Stack_Var_T, ThetaValue
from smt_encoding.instructions.instruction_bounds import InstructionBounds
from smt_encoding.complete_encoding.synthesis_utils import select_instructions_position

# Methods for defining the state of the stack in the encoding at a given position


def stack_encoding_for_position(j: int, sf: SynthesisFunctions, stack_state: List[Stack_Var_T],
                                bs: int) -> List[AssertHard]:
    """
    Methods for defining the state of the stack in the encoding at a given position

    :param j: position in the sequence represented
    :param sf: factory for creating the corresponding terms
    :param stack_state: list of terms representing the elements in the stack, from top to bottom
    :param bs: maximum stack size
    :return: a list of hard constraints with the corresponding representation
    """

    # Constraints for asserting the state of the stack
    constraints = [AssertHard(add_and(sf.u(alpha, j), add_eq(sf.x(alpha, j), sf.stack_var(stack_var))))
                   for alpha, stack_var in enumerate(stack_state)]

    # Constraints for asserting the remaining positions have no elements
    constraints.extend([AssertHard(add_not(sf.u(beta, j))) for beta in range(len(stack_state), bs)])

    return constraints

# Methods related to the initialization of certain variables


def restrict_t_domain(sf: SynthesisFunctions, bounds: InstructionBounds,
                      theta_values: List[ThetaValue]) -> List[AssertHard]:
    return [AssertHard(add_or(*(add_eq(sf.t(j), sf.theta_value(theta_value))
                                for theta_value in select_instructions_position(j, theta_values, bounds))))
            for j in range(bounds.first_position_sequence, bounds.last_position_sequence + 1)]


def expressions_are_distinct(*expressions: ExpressionReference) -> List[AssertHard]:
    return [AssertHard(add_distinct(*expressions))]


def initialize_stack_variables(sf: SynthesisFunctions, initial_index: int) -> List[AssertHard]:
    return [AssertHard(add_eq(stack_var, initial_index + i)) for i, stack_var in enumerate(sf.created_stack_vars())]
