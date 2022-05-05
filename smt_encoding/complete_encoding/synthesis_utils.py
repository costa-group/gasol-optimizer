from smt_encoding.instructions.encoding_instruction import ThetaValue
from smt_encoding.instructions.instruction_bounds import InstructionBounds

# Given a concrete position in the sequence and a set of instructions, returns the instructions that can happen
# at that position
def select_intructions_position(j : int, instructions : [ThetaValue], bounds : InstructionBounds) -> [ThetaValue]:
    return list(filter(lambda theta_value: bounds.lower_bound_theta_value(theta_value) <= j <= bounds.upper_bound_theta_value(theta_value), instructions))
