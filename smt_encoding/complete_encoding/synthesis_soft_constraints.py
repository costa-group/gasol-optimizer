from typing import Dict, List
from smt_encoding.instructions.encoding_instruction import ThetaValue
from collections import OrderedDict
from smt_encoding.constraints.assertions import AssertSoft
from smt_encoding.instructions.instruction_bounds import InstructionBounds
from smt_encoding.complete_encoding.synthesis_functions import SynthesisFunctions
from smt_encoding.constraints.connector_factory import add_eq, add_or
from smt_encoding.complete_encoding.synthesis_utils import select_instructions_position


def soft_constraints_direct(sf: SynthesisFunctions, weight_dict: Dict[ThetaValue, int],
                            bounds: InstructionBounds, label_name: str) -> List[AssertSoft]:
    soft_constraints = [AssertSoft(add_eq(sf.t(j), sf.theta_value(theta_value)), weight, label_name)
                        for theta_value, weight in weight_dict.items()
                        for j in range(bounds.lower_bound_theta_value(theta_value),
                                       bounds.upper_bound_theta_value(theta_value) + 1)
                        if weight > 0]

    return soft_constraints


# Generates an ordered dict that contains all instructions
# as keys, and their gas cost as values. Ordered by increasing costs
def _generate_costs_ordered_dict(weight_dict: Dict[ThetaValue, int]) -> OrderedDict:
    instr_costs = {instr: weight for instr, weight in weight_dict.items()}
    return OrderedDict(sorted(instr_costs.items(), key=lambda elem: elem[1]))


# Generates an ordered dict that has the cost of Wp sets as keys
# and the theta value of opcodes with that cost as values.
# Ordered by increasing costs
def _generate_disjoint_sets_from_cost(ordered_costs: OrderedDict) -> OrderedDict:
    disjoint_set = {}
    for instr_id in ordered_costs:
        gas_cost = ordered_costs[instr_id]
        if gas_cost in disjoint_set:
            disjoint_set[gas_cost].append(instr_id)
        else:
            disjoint_set[gas_cost] = [instr_id]
    return OrderedDict([(k, v) for k, v in sorted(disjoint_set.items(), key=lambda elem: elem[0])])


# Generates the soft constraints given the set of instructions and its corresponding weights, considering an or
# clause of multiple instructions with the same weight
def soft_constraints_grouped_by_weight(sf: SynthesisFunctions, b0: int, weight_dict: Dict[ThetaValue, int],
                                       bounds: InstructionBounds, label_name: str) -> List[AssertSoft]:
    instr_costs = _generate_costs_ordered_dict(weight_dict)
    disjoint_sets = _generate_disjoint_sets_from_cost(instr_costs)
    previous_cost = 0
    theta_or_variables = []
    soft_constraints = []

    for cost in disjoint_sets:
        # We skip the first set of instructions, as they have
        # no soft constraint associated. Nevertheless, we add
        # opcodes with cost 0 to the set of variables till p
        if cost == 0:
            for instr in disjoint_sets[cost]:
                theta_or_variables.append(instr)
            continue

        wi = cost - previous_cost

        # Before adding current associated opcodes, we generate
        # the constraints for each tj.
        for j in range(b0):

            theta_in_range = select_instructions_position(j, theta_or_variables, bounds)

            # Only add a constraint if any instruction satisfies the condition
            if theta_in_range:
                soft_constraints.append(AssertSoft(add_or(*(add_eq(sf.t(j), sf.theta_value(theta_val))
                                                            for theta_val in theta_in_range)),
                                                   wi, label_name))

        for instr in disjoint_sets[cost]:
            theta_or_variables.append(instr)

        # We update previous_cost
        previous_cost = cost

    return soft_constraints
