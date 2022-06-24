from smt_encoding.complete_encoding.synthesis_functions import SynthesisFunctions
from smt_encoding.constraints.connector_factory import add_eq, add_and, add_implies, add_or, add_distinct
from smt_encoding.constraints.assertions import AssertHard
from smt_encoding.instructions.instruction_bounds import InstructionBounds
from typing import List
from smt_encoding.instructions.encoding_instruction import ThetaValue
from smt_encoding.complete_encoding.synthesis_utils import select_instructions_position
from smt_encoding.constraints.function import ExpressionReference


# After a nop instruction has been applied, the remaining instructions must be also nop. This way, we prune
# the search space
def fromnop_encoding(sf: SynthesisFunctions, bounds: InstructionBounds, theta_nop: ThetaValue) -> List[AssertHard]:
    constraints = []
    for j in range(bounds.lower_bound_theta_value(theta_nop), bounds.upper_bound_theta_value(theta_nop)):
        left_term = add_eq(sf.t(j), sf.theta_value(theta_nop))
        right_term = add_eq(sf.t(j+1), sf.theta_value(theta_nop))
        constraints.append(AssertHard(add_implies(left_term, right_term)))
    return constraints


# Only a pop can be performed if no instruction introducing a value in the stack was performed just before.
# At this point, this means only pop, swap and storage instructions are valid before a pop.
def no_output_before_pop(sf: SynthesisFunctions, bounds: InstructionBounds, theta_swaps: List[ThetaValue],
                         theta_mems: List[ThetaValue], theta_pops: List[ThetaValue]) -> List[AssertHard]:
    constraints = []
    no_output_instr_theta = [*theta_swaps, *theta_mems, *theta_pops]

    for theta_pop in theta_pops:
        for j in range(bounds.lower_bound_theta_value(theta_pop) - 1, bounds.upper_bound_theta_value(theta_pop)):
            selected_theta_values = select_instructions_position(j, no_output_instr_theta, bounds)
            if selected_theta_values:
                constraints.append(AssertHard(add_implies(add_eq(sf.t(j+1), sf.theta_value(theta_pop)),
                                                          add_or(*(add_eq(sf.t(j), sf.theta_value(theta_val))
                                                                   for theta_val in selected_theta_values)))))
    return constraints


def each_instruction_is_used_at_least_once(sf: SynthesisFunctions, bounds: InstructionBounds,
                                           theta_values: List[ThetaValue]) -> List[AssertHard]:
    return [AssertHard(add_or(*[add_eq(sf.t(j), sf.theta_value(theta_value))
                                for j in range(bounds.lower_bound_theta_value(theta_value),
                                               bounds.upper_bound_theta_value(theta_value) + 1)]))
            for theta_value in theta_values]


# As we assume that each value that appears in the ops is needed, then we need to
# push each value at least once. Only valid if push basic is in the encoding
def push_each_element_basic(sf: SynthesisFunctions, bounds: InstructionBounds, theta_push_basic: ThetaValue,
                            pushed_elements: List[int]) -> List[AssertHard]:
    return [AssertHard(add_or(*[add_and(add_eq(sf.t(j), sf.theta_value(theta_push_basic)), add_eq(sf.a(j), val))
                                for j in range(bounds.lower_bound_theta_value(theta_push_basic),
                                               bounds.upper_bound_theta_value(theta_push_basic) + 1)])) 
            for val in pushed_elements]


def each_function_is_used_at_most_once(sf: SynthesisFunctions, bounds: InstructionBounds,
                                       theta_value: ThetaValue) -> List[AssertHard]:
    # We need at least two elements to be a valid restriction
    if bounds.upper_bound_theta_value(theta_value) == bounds.lower_bound_theta_value(theta_value):
        return []

    constraints = []
    positions = set(range(bounds.lower_bound_theta_value(theta_value), bounds.upper_bound_theta_value(theta_value) + 1))

    for j in range(bounds.lower_bound_theta_value(theta_value), bounds.upper_bound_theta_value(theta_value) + 1):
        positions.remove(j)
        constraints.append(AssertHard(add_implies(add_eq(sf.t(j), sf.theta_value(theta_value)),
                                                  add_and(*(add_distinct(sf.t(k), sf.theta_value(theta_value)) for k in positions)))))
        positions.add(j)

    return constraints
