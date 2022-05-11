from smt_encoding.complete_encoding.synthesis_functions import SynthesisFunctions
from smt_encoding.constraints.assertions import AssertHard
from typing import List, Callable
from smt_encoding.instructions.encoding_instruction import ThetaValue
from smt_encoding.instructions.instruction_bounds import InstructionBounds
from smt_encoding.instructions.encoding_instruction import EncodingInstruction


def stack_constraints_with_bounds(func: Callable[..., AssertHard], theta_val: ThetaValue,
                                  bounds: InstructionBounds, sf: SynthesisFunctions, bs: int,
                                  *args, **kwargs) -> List[AssertHard]:
    """
    Given a function that generates a hard constraint for a position in the sequence and the corresponding bounds,
    generates a list of hard constraints for each position within the bounds.

    :param func: Function that generates the encoding. First positional argument is the current position in the sequence
    to represent, and the second one the corresponding theta value.
    :param theta_val: theta value
    :param bounds: bound object containing the necessary info
    :param sf: SynthesisFunctions object that creates the corresponding variables of the encoding
    :param bs: max stack size
    :param args: args params passed to func
    :param kwargs: kwargs params passed to func
    :return: a list with a hard constraint for each position within the bounds
    """
    return [func(pos, theta_val, sf, bs, *args, **kwargs) for pos in range(bounds.lower_bound_theta_value(theta_val),
                                                                           bounds.upper_bound_theta_value(
                                                                               theta_val) + 1)]


class EncodingForStack:

    def __init__(self):
        self._instructions_registered = set()
        self._encoding_function = dict()
        self._args = dict()
        self._kwargs = dict()

    def register_function_for_encoding(self, instruction: EncodingInstruction,
                                       encoding_function: Callable[..., AssertHard], *args, **kwargs) -> None:
        instruction_id = instruction.id
        self._instructions_registered.add(instruction_id)
        self._encoding_function[instruction_id] = encoding_function
        self._args[instruction_id] = args
        self._kwargs[instruction_id] = kwargs

    def encode_instruction(self, instruction: EncodingInstruction, bounds: InstructionBounds,
                           sf: SynthesisFunctions, bs: int) -> List[AssertHard]:
        instruction_id = instruction.id
        if instruction_id not in self._instructions_registered:
            raise ValueError(instruction_id + " has no encoding function linked")
        return stack_constraints_with_bounds(self._encoding_function[instruction_id],
                                             instruction.theta_value, bounds, sf, bs,
                                             *self._args[instruction_id], **self._kwargs[instruction_id])
