from smt_encoding.encoding_files import write_encoding
from smt_encoding.encoding_utils import l, t
from smt_encoding.smtlib_utils import (add_and, add_assert, add_eq,
                                       add_implies, add_leq, add_lt, add_not)

# Methods for generating the constraints for both memory and storage (Ls)

def mem_variable_equivalence_constraint(j, theta_uninterpreted):
    left_term = add_eq(t(j), theta_uninterpreted)
    right_term = add_eq(l(theta_uninterpreted), j)
    return add_assert(add_eq(left_term, right_term))


# Note that the instructions must verify store1 < store2
def l_variable_order_constraint(theta_uninterpreted_1, theta_uninterpreted_2):
    return add_assert(add_lt(l(theta_uninterpreted_1), l(theta_uninterpreted_2)))


# Given two conflicting instructions, returns a general constraint that avoids an incorrect order between them
def direct_order_constraint(j, theta_conflicting1, theta_conflicting2, final_idx):
    left_term = add_eq(t(j), theta_conflicting2)
    right_term = add_and(*[add_not(add_eq(t(i), theta_conflicting1)) for i in range(j+1, final_idx)])
    return add_assert(add_implies(left_term, right_term))


def memory_model_constraints_l_conflicting(b0, order_tuples, theta_dict, theta_mem, first_position_instr_appears_dict,
                               first_position_instr_cannot_appear_dict, initial_idx=0):
    write_encoding("; Memory constraints using l variables for conflicting operation")

    for id, theta_uninterpreted in theta_mem.items():
        initial_possible_idx = first_position_instr_appears_dict.get(id, 0) + initial_idx
        final_possible_idx = first_position_instr_cannot_appear_dict.get(id, b0) + initial_idx

        write_encoding(add_assert(add_and(add_leq(initial_possible_idx, l(theta_uninterpreted)), add_lt(l(theta_uninterpreted), final_possible_idx))))
        for j in range(initial_possible_idx, final_possible_idx):
            write_encoding(mem_variable_equivalence_constraint(j, theta_uninterpreted))

    # Order tuples contains those elements that are related
    for el1, el2 in order_tuples:

        theta_val_1 = theta_dict[el1]
        theta_val_2 = theta_dict[el2]

        # The constraints for l conflicting matches the store store clauses
        write_encoding(l_variable_order_constraint(theta_val_1, theta_val_2))


def memory_model_constraints_direct(b0, order_tuples, theta_dict, first_position_instr_appears_dict,
                                    first_position_instr_cannot_appear_dict, initial_idx=0):

    write_encoding("; Memory constraints directly")
    # Order tuples contains those elements that are related
    for el1, el2 in order_tuples:

        theta_val_1 = theta_dict[el1]
        theta_val_2 = theta_dict[el2]

        initial_possible_idx_el1 = first_position_instr_appears_dict.get(el1, 0) + initial_idx
        final_possible_idx_el1 = first_position_instr_cannot_appear_dict.get(el1, b0) + initial_idx

        final_possible_idx_el2 = first_position_instr_cannot_appear_dict.get(el1, b0) + initial_idx


        for j in range(initial_possible_idx_el1, final_possible_idx_el1):
            write_encoding(direct_order_constraint(j, theta_val_1, theta_val_2, final_possible_idx_el2))
