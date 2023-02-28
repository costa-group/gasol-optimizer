from smt_encoding.complete_encoding.synthesis_functions import SynthesisFunctions
from smt_encoding.constraints.connector_factory import add_eq, add_lt, add_or, add_implies, add_distinct, add_and
from smt_encoding.constraints.assertions import AssertHard
from typing import List, Dict, Set, Generator, Optional
from smt_encoding.instructions.encoding_instruction import ThetaValue, Id_T, EncodingInstruction
from smt_encoding.instructions.instruction_bounds import InstructionBounds
from smt_encoding.instructions.uninterpreted_instruction import UninterpretedInstruction


# Methods for generating the constraints for both memory and storage (Ls)


def restrict_l_domain(sf: SynthesisFunctions, bounds: InstructionBounds, theta_value: ThetaValue) -> AssertHard:
    return AssertHard(add_or(*(add_eq(sf.l(theta_value), j)
                               for j in range(bounds.lower_bound_theta_value(theta_value),
                                              bounds.upper_bound_theta_value(theta_value) + 1))))


def mem_variable_equivalence_constraint(j: int, theta_uninterpreted: ThetaValue, sf: SynthesisFunctions) -> AssertHard:
    left_term = add_eq(sf.t(j), sf.theta_value(theta_uninterpreted))
    right_term = add_eq(sf.l(theta_uninterpreted), j)
    return AssertHard(add_eq(left_term, right_term))


# Note that the instructions must verify store1 < store2
def l_variable_order_constraint(theta_uninterpreted_1: ThetaValue, theta_uninterpreted_2: ThetaValue,
                                sf: SynthesisFunctions) -> AssertHard:
    return AssertHard(add_lt(sf.l(theta_uninterpreted_1), sf.l(theta_uninterpreted_2)))


def l_conflicting_constraints_from_theta_values(l_theta_values: List[ThetaValue], bounds: InstructionBounds,
                                                dependency_graph_set_theta: Dict[ThetaValue, Set[ThetaValue]],
                                                sf: SynthesisFunctions) -> Generator:
    for theta_value in l_theta_values:

        yield restrict_l_domain(sf, bounds, theta_value)

        for pos in range(bounds.lower_bound_theta_value(theta_value), bounds.upper_bound_theta_value(theta_value) + 1):
            yield mem_variable_equivalence_constraint(pos, theta_value, sf)

        # Only consider the order among instructions with instructions also in l_theta_values
        yield from (l_variable_order_constraint(conflicting_theta_value, theta_value, sf)
                    for conflicting_theta_value in dependency_graph_set_theta.get(theta_value, [])
                    if conflicting_theta_value in l_theta_values)


def l_conflicting_theta_values(instructions: List[EncodingInstruction]) -> List[ThetaValue]:
    """
    Filter those instructions that have a l variable tied to them. These instructions correspond to the ones
    that appear exactly once in the sequence, and hence, they are only tied to one position.

    :param instructions: list of instructions
    :return: list of theta values
    """
    return [instruction.theta_value for instruction in instructions if instruction.unique_ui]


def l_conflicting_constraints(instructions: List[EncodingInstruction], bounds: InstructionBounds,
                              dependency_graph: Dict[Id_T, List[Id_T]], sf: SynthesisFunctions) -> Generator:
    l_theta_values = l_conflicting_theta_values(instructions)
    theta_value_by_id_dict: Dict[Id_T, ThetaValue] = {instruction.id: instruction.theta_value
                                                      for instruction in instructions}
    dependency_graph_set_theta = {theta_value_by_id_dict[instr_id]:
                                      {theta_value_by_id_dict[dependent_id] for dependent_id in dependency_ids}
                                  for instr_id, dependency_ids in dependency_graph.items()}
    yield from l_conflicting_constraints_from_theta_values(l_theta_values, bounds, dependency_graph_set_theta, sf)


# Alternative encoding using direct constraints instead of l variables

# Given two conflicting instructions, returns a general constraint that avoids an incorrect order between them
def happens_before_direct(j: int, sf: SynthesisFunctions, bounds: InstructionBounds,
                          theta_conflicting1: ThetaValue, theta_conflicting2: ThetaValue) -> Optional[AssertHard]:
    left_term = add_eq(sf.t(j), sf.theta_value(theta_conflicting2))
    positions_restricted = [add_eq(sf.t(i), sf.theta_value(theta_conflicting1))
                            for i in range(bounds.lower_bound_theta_value(theta_conflicting1), j)]

    # If no position is restricted, we just return None. It can happen with not-so-accurate bounds
    if positions_restricted == []:
        return None
        # raise ValueError("Empty conflict order direct")

    right_term = add_or(*positions_restricted)
    return AssertHard(add_implies(left_term, right_term))


# St - Ld dependencies : Ld instruction cannot appear before store
def sto_ld_dependency(j: int, sf: SynthesisFunctions, bounds: InstructionBounds,
                      theta_sto: ThetaValue, theta_ld: ThetaValue) -> Optional[AssertHard]:
    left_term = add_eq(sf.t(j), sf.theta_value(theta_sto))
    positions_restricted = [add_distinct(sf.t(i), sf.theta_value(theta_ld))
                            for i in range(bounds.lower_bound_theta_value(theta_ld), j)]

    if positions_restricted == []:
        return None
        # raise ValueError("Empty conflict order direct")

    right_term = add_and(*positions_restricted)
    return AssertHard(add_implies(left_term, right_term))


# Ld - St dependencies : Ld instruction cannot appear after store
def ld_sto_dependency(j: int, sf: SynthesisFunctions, bounds: InstructionBounds,
                      theta_ld: ThetaValue, theta_sto: ThetaValue) -> Optional[AssertHard]:
    left_term = add_eq(sf.t(j), sf.theta_value(theta_sto))
    positions_restricted = [add_distinct(sf.t(i), sf.theta_value(theta_ld))
                            for i in range(j + 1, bounds.upper_bound_theta_value(theta_ld) + 1)]

    if positions_restricted == []:
        return None
        # raise ValueError("Empty conflict order direct")

    right_term = add_and(*positions_restricted)
    return AssertHard(add_implies(left_term, right_term))


def dependent_pre_order(uninterpreted_instr: List[UninterpretedInstruction], order_tuples: List[List[Id_T]],
                        b0: int, stack_elem_to_id: Dict[str, Id_T], instr_dep: bool,
                        theta_value_by_id_dict: Dict[Id_T, ThetaValue],
                        bounds: InstructionBounds, sf: SynthesisFunctions) -> Generator:
    if instr_dep:
        for instr in uninterpreted_instr:
            instr_theta = theta_value_by_id_dict[instr.id]

            for stack_elem in instr.input_stack:

                # We search for another instruction that generates the
                # stack elem as an output and add it to the set
                if type(stack_elem) == str:

                    prev_instr_id = stack_elem_to_id.get(stack_elem, None)
                    # This means the stack element corresponds to another uninterpreted instruction
                    if prev_instr_id is not None:
                        prev_instr_theta = theta_value_by_id_dict[prev_instr_id]

                        for j in range(max(1, bounds.lower_bound_theta_value(instr_theta),
                                           bounds.lower_bound_theta_value(prev_instr_theta)),
                                       bounds.upper_bound_theta_value(instr_theta) + 1):
                            hard_constraint = happens_before_direct(j, sf, bounds, prev_instr_theta, instr_theta)
                            if hard_constraint is not None:
                                yield hard_constraint

    # We need to consider also the order given by the tuples
    for id1, id2 in order_tuples:

        bef_instr_theta, aft_instr_theta = theta_value_by_id_dict[id1], theta_value_by_id_dict[id2]
        if 'STORE' in id1 and 'STORE' in id2:
            # As store instructions can only appear once, this can be represented directly using a happens
            # before relation
            for j in range(max(1, bounds.lower_bound_theta_value(aft_instr_theta),
                               bounds.lower_bound_theta_value(bef_instr_theta)),
                           bounds.upper_bound_theta_value(aft_instr_theta) + 1):
                hard_constraint = happens_before_direct(j, sf, bounds, bef_instr_theta, aft_instr_theta)
                if hard_constraint is not None:
                    yield hard_constraint

        # St - Ld dependencies : Ld instruction cannot appear before store
        elif 'STORE' in id1:
            for j in range(max(1, bounds.lower_bound_theta_value(aft_instr_theta) + 1,
                               bounds.lower_bound_theta_value(bef_instr_theta)),
                           bounds.upper_bound_theta_value(bef_instr_theta) + 1):
                hard_constraint = sto_ld_dependency(j, sf, bounds, bef_instr_theta, aft_instr_theta)
                if hard_constraint is not None:
                    yield hard_constraint

        # Ld - St dependencies : Ld instruction cannot appear after store
        else:
            for j in range(bounds.lower_bound_theta_value(aft_instr_theta),
                           min(b0 - 1, bounds.upper_bound_theta_value(bef_instr_theta),
                               bounds.upper_bound_theta_value(aft_instr_theta) + 1)):
                hard_constraint = ld_sto_dependency(j, sf, bounds, bef_instr_theta, aft_instr_theta)
                if hard_constraint is not None:
                    yield hard_constraint


def happens_before_from_dependency_graph(dependency_graph_set_theta: Dict[ThetaValue, Set[ThetaValue]],
                                         bounds: InstructionBounds, sf: SynthesisFunctions) -> Generator:
    # We consider max(1, lb(theta_confl1), lb(theta_confl2)) to start either by the first position in which
    # theta_confl2 can appear and has a previous theta_confl1. In general, you could assume
    # lb(theta_confl2) > lb(theta_confl1), but in the case of no bounds, both are equal.
    for theta_confl2 in dependency_graph_set_theta:
        for theta_confl1 in dependency_graph_set_theta[theta_confl2]:
            for j in range(max(1, bounds.lower_bound_theta_value(theta_confl2),
                               bounds.lower_bound_theta_value(theta_confl1)),
                           bounds.upper_bound_theta_value(theta_confl2)):
                hard_constraint = happens_before_direct(j, sf, bounds, theta_confl1, theta_confl2)
                if hard_constraint is not None:
                    yield hard_constraint


def direct_conflict_constraints(instructions: List[UninterpretedInstruction], order_tuples: List[List[Id_T]],
                                b0: int, bounds: InstructionBounds, sf: SynthesisFunctions,
                                instr_dep: bool) -> Generator:
    theta_value_by_id_dict: Dict[Id_T, ThetaValue] = {instruction.id: instruction.theta_value
                                                      for instruction in instructions}
    stack_elem_to_id: Dict[str, Id_T] = {instruction.output_stack: instruction.id
                                         for instruction in instructions if instruction.output_stack is not None}

    yield from dependent_pre_order(instructions, order_tuples, b0, stack_elem_to_id, instr_dep, theta_value_by_id_dict,
                                   bounds, sf)
