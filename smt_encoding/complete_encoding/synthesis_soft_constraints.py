from typing import Dict
from smt_encoding.instructions.encoding_instruction import ThetaValue
from collections import OrderedDict
from smt_encoding.constraints.assertions import AssertSoft
from smt_encoding.complete_encoding.instruction_bounds import InstructionBounds
from smt_encoding.complete_encoding.synthesis_variables import SynthesisVariables
from smt_encoding.constraints.connector_factory import add_eq, add_or

def _soft_constraints_direct(sv : SynthesisVariables, weight_dict : Dict[ThetaValue, int],
                             bounds : InstructionBounds, label_name: str) -> [AssertSoft]:
    soft_constraints = [AssertSoft(add_eq(sv.t(j), theta_value), weight, label_name)
                        for theta_value, weight in weight_dict.items()
                        for j in range(bounds.lower_bound(theta_value), bounds.upper_bound(theta_value) + 1)]
    return soft_constraints


# Generates an ordered dict that contains all instructions
# as keys, and their gas cost as values. Ordered by increasing costs
def _generate_costs_ordered_dict(weight_dict : Dict[ThetaValue, int]) -> OrderedDict[int, int]:
    instr_costs = {instr : weight for instr, weight in weight_dict.items()}
    return OrderedDict(sorted(instr_costs.items(), key=lambda elem: elem[1]))


# Generates an ordered dict that has the cost of Wp sets as keys
# and the theta value of opcodes with that cost as values.
# Ordered by increasing costs
def _generate_disjoint_sets_from_cost(ordered_costs : OrderedDict[ThetaValue, int]) -> OrderedDict[int, [int]]:
    disjoint_set = {}
    for id in ordered_costs:
        gas_cost = ordered_costs[id]
        if gas_cost in disjoint_set:
            disjoint_set[gas_cost].append(id)
        else:
            disjoint_set[gas_cost] = [id]
    return OrderedDict([(k,v) for k,v in sorted(disjoint_set.items(), key=lambda elem: elem[0])])

# Given a concrete position in the sequence and a set of instructions, returns the instructions that can happen
# at that position
def _select_intructions_position(j : int, instructions : [ThetaValue], bounds : InstructionBounds) -> [ThetaValue]:
    return list(filter(lambda theta_value: bounds.lower_bound(theta_value) <= j <= bounds.upper_bound(theta_value), instructions))


# Generates the soft constraints given the set of instructions and its corresponding weights, considering an or
# clause of multiple instructions with the same weight
def _soft_constraints_grouped_by_weight(sv : SynthesisVariables, b0 : int, weight_dict : Dict[ThetaValue, int],
                                        bounds : InstructionBounds, label_name: str) -> [AssertSoft]:
    instr_costs = _generate_costs_ordered_dict(weight_dict)
    disjoin_sets = _generate_disjoint_sets_from_cost(instr_costs)
    previous_cost = 0
    theta_or_variables = []
    soft_constraints = []


    for cost in disjoin_sets:
        # We skip the first set of instructions, as they have
        # no soft constraint associated. Nevertheless, we add
        # opcodes with cost 0 to the set of variables till p
        if cost == 0:
            for instr in disjoin_sets[cost]:
                theta_or_variables.append(instr)
            continue

        wi = cost - previous_cost

        # Before adding current associated opcodes, we generate
        # the constraints for each tj.
        for j in range(b0):

            # Not so efficient... But easier to understand
            variables_in_range = _select_intructions_position(j, theta_or_variables, bounds)

            # Only add a constraint if any instruction satisfies the condition
            if variables_in_range:
                soft_constraints.append(AssertSoft(add_or(map(lambda var: add_eq(sv.t(j), var), variables_in_range)), wi, label_name))

        for instr in disjoin_sets[cost]:
            theta_or_variables.append(instr)

        # We update previous_cost
        previous_cost = cost

    return soft_constraints
