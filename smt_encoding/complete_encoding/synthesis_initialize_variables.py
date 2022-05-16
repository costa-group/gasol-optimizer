from smt_encoding.constraints.function import ExpressionReference
from typing import List, Union
from smt_encoding.constraints.assertions import AssertHard
from smt_encoding.constraints.connector_factory import add_and, add_eq, add_not
from smt_encoding.complete_encoding.synthesis_functions import SynthesisFunctions

# Methods for defining the state of the stack in the encoding at a given position


def stack_encoding_for_position(j: int, sf: SynthesisFunctions, stack_state: List[Union[ExpressionReference, int, bool]],
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
    constraints = [AssertHard(add_and(sf.u(alpha, j), add_eq(sf.x(alpha, j), variable)))
                   for alpha, variable in enumerate(stack_state)]

    # Constraints for asserting the remaining positions have no elements
    constraints.extend([AssertHard(add_not(sf.u(beta, j))) for beta in range(len(stack_state), bs)])

    return constraints
