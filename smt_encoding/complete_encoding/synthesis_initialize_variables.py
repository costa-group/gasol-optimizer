from smt_encoding.constraints.function import ExpressionReference
from typing import List, Generator
from smt_encoding.constraints.assertions import AssertHard
from smt_encoding.constraints.connector_factory import add_and, add_eq, add_not, add_distinct, add_or
from smt_encoding.complete_encoding.synthesis_functions import SynthesisFunctions
from smt_encoding.instructions.encoding_instruction import Stack_Var_T, ThetaValue
from smt_encoding.instructions.instruction_bounds import InstructionBounds
from smt_encoding.complete_encoding.synthesis_utils import select_instructions_position

# Methods for defining the state of the stack in the encoding at a given position


def stack_encoding_for_position(j: int, sf: SynthesisFunctions, stack_state: List[Stack_Var_T],
                                bs: int) -> Generator:
    """
    Methods for defining the state of the stack in the encoding at a given position

    :param j: position in the sequence represented
    :param sf: factory for creating the corresponding terms
    :param stack_state: list of terms representing the elements in the stack, from top to bottom
    :param bs: maximum stack size
    :return: a list of hard constraints with the corresponding representation
    """

    # Constraints for asserting the state of the stack
    yield from (AssertHard(add_and(sf.u(alpha, j), add_eq(sf.x(alpha, j), sf.stack_var(stack_var))))
                for alpha, stack_var in enumerate(stack_state))

    # Constraints for asserting the remaining positions have no elements
    yield from (AssertHard(add_not(sf.u(beta, j))) for beta in range(len(stack_state), bs))


def stack_encoding_for_position_empty(j: int, sf: SynthesisFunctions, stack_state: List[Stack_Var_T],
                                      bs: int) -> Generator:
    """
    Methods for defining the state of the stack in the encoding at a given position

    :param j: position in the sequence represented
    :param sf: factory for creating the corresponding terms
    :param stack_state: list of terms representing the elements in the stack, from top to bottom
    :param bs: maximum stack size
    :return: a list of hard constraints with the corresponding representation
    """

    # Constraints for asserting the state of the stack
    yield from (AssertHard(add_eq(sf.x(alpha, j), sf.stack_var(stack_var))) for alpha, stack_var in enumerate(stack_state))

    # Constraints for asserting the remaining positions have no elements
    yield from (AssertHard(add_eq(sf.x(beta, j), sf.empty())) for beta in range(len(stack_state), bs))


def stack_encoding_for_terminal(j: int, sf: SynthesisFunctions, stack_state: List[Stack_Var_T]) -> Generator:
    """
    Methods for defining the state of the stack before RETURN or REVERT

    :param j: position in the sequence represented
    :param sf: factory for creating the corresponding terms
    :param stack_state: list of terms representing the elements in the stack, from top to bottom
    :param bs: maximum stack size
    :return: a list of hard constraints with the corresponding representation
    """

    # Constraints for asserting the state of the stack
    yield AssertHard(add_and(sf.u(0, j), add_eq(sf.x(0, j), sf.stack_var(stack_state[0]))))
    yield AssertHard(add_and(sf.u(1, j), add_eq(sf.x(1, j), sf.stack_var(stack_state[1]))))

# Methods related to the initialization of certain variables


def restrict_t_domain(sf: SynthesisFunctions, bounds: InstructionBounds,
                      theta_values: List[ThetaValue]) -> Generator:
    yield from (AssertHard(add_or(*(add_eq(sf.t(j), sf.theta_value(theta_value))
                                    for theta_value in select_instructions_position(j, theta_values, bounds))))
                for j in range(bounds.first_position_sequence, bounds.last_position_sequence + 1))


def expressions_are_distinct(*expressions: ExpressionReference) -> Generator:
    if len(expressions) > 1:
        yield AssertHard(add_distinct(*expressions))


def initialize_stack_variables(sf: SynthesisFunctions, initial_index: int) -> Generator:
    yield from (AssertHard(add_eq(stack_var, initial_index + i)) for i, stack_var in enumerate(sf.created_stack_vars()))
