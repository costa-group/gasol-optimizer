import global_params.constants as constants
from smt_encoding.encoding_files import write_encoding
from smt_encoding.encoding_utils import a, move, t, u, x
from smt_encoding.smtlib_utils import (add_and, add_assert, add_eq,
                                       add_implies, add_leq, add_lt, add_not,
                                       add_or)

# Methods for generating the constraints for stack (Cs)

def push_encoding(j, bs, theta_push):
    left_term = add_eq(t(j), theta_push)
    right_term = add_and(add_leq(0, a(j)), add_lt(a(j), constants.int_limit), add_not(u(bs - 1, j)), u(0, j + 1),
                         add_eq(x(0, j+1), a(j)), move(j, 0, bs-2, 1))
    return add_assert(add_implies(left_term, right_term))


def dupk_encoding(k, j, bs, theta_dupk):
    left_term = add_eq(t(j), theta_dupk)
    right_term = add_and(add_not(u(bs-1, j)), u(k-1, j), u(0, j+1),
                          add_eq(x(0, j+1), x(k-1, j)), move(j, 0, bs-2, 1))
    return add_assert(add_implies(left_term, right_term))


def swapk_encoding(k, j, bs, theta_swapk):
    left_term = add_eq(t(j), theta_swapk)
    right_term = add_and(u(k,j), u(0, j+1), add_eq(x(0, j+1), x(k,j)) ,
                          u(k, j+1), add_eq(x(k, j+1), x(0,j)),
                          move(j, 1, k-1, 0), move(j, k+1, bs-1, 0))
    return add_assert(add_implies(left_term, right_term))


def pop_encoding(j, bs, theta_pop):
    left_term = add_eq(t(j), theta_pop)
    right_term = add_and(u(0,j), add_not(u(bs-1, j+1)), move(j,1,bs-1,-1))
    return add_assert(add_implies(left_term, right_term))


def pop_uninterpreted_encoding(j, bs, o, theta_pop):
    left_term = add_eq(t(j), theta_pop)
    right_term = add_and(u(0,j), add_eq(x(0,j), o), add_not(u(bs-1, j+1)), move(j,1,bs-1,-1))
    return add_assert(add_implies(left_term, right_term))


def nop_encoding(j, bs, theta_nop):
    left_term = add_eq(t(j), theta_nop)
    right_term = move(j,0,bs-1,0)
    return add_assert(add_implies(left_term, right_term))


def fromnop_encoding(b0, theta_nop, initial_idx):
    constraints = []
    for j in range(initial_idx, b0-1+initial_idx):
        left_term = add_eq(t(j), theta_nop)
        right_term = add_eq(t(j+1), theta_nop)
        constraints.append(add_assert(add_implies(left_term, right_term)))
    return constraints


def _stack_constraints(b0, bs, theta, initial_idx=0):
    write_encoding("; Stack contraints")
    write_encoding(*fromnop_encoding(b0, theta["NOP"], initial_idx))
    for j in range(initial_idx, b0 + initial_idx):
        write_encoding(push_encoding(j, bs, theta["PUSH"]))
        write_encoding(pop_encoding(j, bs, theta["POP"]))
        write_encoding(nop_encoding(j, bs, theta["NOP"]))

        for k in range(1, min(bs, constants.max_k_dup + 1)):
            write_encoding(dupk_encoding(k, j, bs, theta["DUP" + str(k)]))

        for k in range(1, min(bs, constants.max_k_swap + 1)):
            write_encoding(swapk_encoding(k, j, bs, theta["SWAP" + str(k)]))


# Methods for generating constraints for non-commutative uninterpreted functions (Cu)


def non_comm_function_encoding(j, bs, o, r, theta_f):
    n = len(o)
    left_term = add_eq(t(j), theta_f)
    right_term_first_and = ["true"]
    # Second and can be empty, so we initialize terms to true value
    right_term_second_and = ["true"]
    right_term_third_and = ["true"]
    for i in range(0, n):
        right_term_first_and.append(add_and(u(i,j), add_eq(x(i,j), o[i])))
    for i in range(bs-n+1, bs):
        right_term_second_and.append(add_not(u(i, j+1)))
    for i in range(bs+n-1, bs):
        right_term_third_and.append(add_not(u(i, j)))
    right_term = add_and(add_and(*right_term_first_and), u(0, j+1) , add_eq(x(0,j+1), r),
                          move(j, n, min(bs-2+n, bs-1), 1-n) , add_and(*right_term_second_and),
                         add_and(*right_term_third_and))
    return add_assert(add_implies(left_term, right_term))


def _non_comm_function_constraints(b0, bs, non_comm_user_instr, theta_non_comm, first_position_instr_appears_dict,
                                   first_position_instr_cannot_appear_dict, initial_idx):
    write_encoding("; Non-commutative constraints")
    for instr in non_comm_user_instr:
        o = instr['inpt_sk']
        theta_f = theta_non_comm[instr['id']]

        # We assume every function has only one output
        r = instr['outpt_sk'][0]

        # Only add the encoding for those positions that are possible. These
        # dicts can be empty, so we use get method to ensure that a correct value is taken.
        initial_possible_idx = first_position_instr_appears_dict.get(instr['id'], 0) + initial_idx
        final_possible_idx = first_position_instr_cannot_appear_dict.get(instr['id'], b0) + initial_idx

        # Instructions cannot appear in [0, first_position), so we add a statement to consider this situation.
        for j in range(initial_idx, initial_possible_idx):
            write_encoding(add_assert(add_not(add_eq(t(j), theta_f))))

        # Instructions can appear in [initial_idx, final_idx), as initial_idx refers to the first position
        # a instruction can appear and final_idx refers to the first position that instruction cannot appear.
        # Note that last value can be b0 if it can appear at any point.
        for j in range(initial_possible_idx, final_possible_idx):
            write_encoding(non_comm_function_encoding(j, bs, o, r, theta_f))

        # Instructions cannot appear in [final_idx, b0), so we add a statement to consider this situation.
        for j in range(final_possible_idx, b0+initial_idx):
            write_encoding(add_assert(add_not(add_eq(t(j), theta_f))))

# Methods for generating constraints for commutative uninterpreted functions (Cc)

def comm_function_encoding(j, bs, o0, o1, r, theta_f):
    left_term = add_eq(t(j), theta_f)
    right_term = add_and(u(0,j), u(1,j), add_or(add_and(add_eq(x(0,j), o0), add_eq(x(1,j), o1)),
                                                  add_and(add_eq(x(0,j), o1), add_eq(x(1,j), o0))),
                          u(0,j+1), add_eq(x(0,j+1), r), move(j, 2, bs-1, -1), add_not(u(bs-1, j+1)))
    return add_assert(add_implies(left_term, right_term))


def _comm_function_constraints(b0, bs, comm_user_instr, theta_comm, first_position_instr_appears_dict,
                               first_position_instr_cannot_appear_dict, initial_idx=0):
    write_encoding("; Commutative constraints")
    for instr in comm_user_instr:
        o0 = instr['inpt_sk'][0]
        o1 = instr['inpt_sk'][1]
        theta_f = theta_comm[instr['id']]

        # We assume every function has only one output
        r = instr['outpt_sk'][0]

        # Only add the encoding for those positions that are possible. These
        # dicts can be empty, so we use get method to ensure that a correct value is taken.
        initial_possible_idx = first_position_instr_appears_dict.get(instr['id'], 0) + initial_idx
        final_possible_idx = first_position_instr_cannot_appear_dict.get(instr['id'], b0) + initial_idx

        # Instructions cannot appear in [0, first_position), so we add a statement to consider this situation.
        for j in range(initial_idx, initial_possible_idx):
            write_encoding(add_assert(add_not(add_eq(t(j), theta_f))))

        # Instructions can appear in [initial_idx, final_idx), as initial_idx refers to the first position
        # a instruction can appear and final_idx refers to the first position that instruction cannot appear.
        # Note that last value can be b0 if it can appear at any point.
        for j in range(initial_possible_idx, final_possible_idx):
            write_encoding(comm_function_encoding(j, bs, o0, o1, r, theta_f))

        # Instructions cannot appear in [final_idx, b0), so we add a statement to consider this situation.
        for j in range(final_possible_idx, b0+initial_idx):
            write_encoding(add_assert(add_not(add_eq(t(j), theta_f))))


def store_stack_function_encoding(j, bs, o0, o1, theta_f):
    left_term = add_eq(t(j), theta_f)
    right_term = add_and(u(0,j), u(1,j), add_and(add_eq(x(0,j), o0), add_eq(x(1,j), o1)),
                         move(j, 2, bs-1, -2), add_not(u(bs-1, j+1)), add_not(u(bs-2, j+1)))
    return add_assert(add_implies(left_term, right_term))


def _store_stack_constraints(b0, bs, mem_instr, theta_mem, first_position_instr_appears_dict,
                               first_position_instr_cannot_appear_dict, initial_idx=0):
    write_encoding("; Store constraints")
    for instr in mem_instr:
        o0 = instr['inpt_sk'][0]
        o1 = instr['inpt_sk'][1]
        theta_f = theta_mem[instr['id']]

        # Only add the encoding for those positions that are possible. These
        # dicts can be empty, so we use get method to ensure that a correct value is taken.
        initial_possible_idx = first_position_instr_appears_dict.get(instr['id'], 0) + initial_idx
        final_possible_idx = first_position_instr_cannot_appear_dict.get(instr['id'], b0) + initial_idx

        # Instructions cannot appear in [0, first_position), so we add a statement to consider this situation.
        for j in range(initial_idx, initial_possible_idx):
            write_encoding(add_assert(add_not(add_eq(t(j), theta_f))))

        # Instructions can appear in [initial_idx, final_idx), as initial_idx refers to the first position
        # a instruction can appear and final_idx refers to the first position that instruction cannot appear.
        # Note that last value can be b0 if it can appear at any point.
        for j in range(initial_possible_idx, final_possible_idx):
            write_encoding(store_stack_function_encoding(j, bs, o0, o1, theta_f))

        # Instructions cannot appear in [final_idx, b0), so we add a statement to consider this situation.
        for j in range(final_possible_idx, b0+initial_idx):
            write_encoding(add_assert(add_not(add_eq(t(j), theta_f))))

# Methods for generating constraints for finding the target program

def stack_constraints(b0, bs, comm_instr, non_comm_instr, mem_instr, theta_stack, theta_comm, theta_non_comm, theta_mem,
                      first_position_instr_appears_dict, first_position_instr_cannot_appear_dict, initial_idx=0):
    mi = len(theta_stack) + len(theta_comm) + len(theta_non_comm) + len(theta_mem)
    write_encoding("; Instructions constraints")

    for j in range(initial_idx, b0+initial_idx):
        write_encoding(add_assert(add_and(add_leq(0, t(j)), add_lt(t(j), mi))))

    _stack_constraints(b0, bs, theta_stack, initial_idx)
    _comm_function_constraints(b0, bs, comm_instr, theta_comm, first_position_instr_appears_dict,
                               first_position_instr_cannot_appear_dict, initial_idx)
    _non_comm_function_constraints(b0, bs, non_comm_instr, theta_non_comm, first_position_instr_appears_dict,
                                   first_position_instr_cannot_appear_dict, initial_idx)
    _store_stack_constraints(b0, bs, mem_instr, theta_mem, first_position_instr_appears_dict,
                             first_position_instr_cannot_appear_dict, initial_idx)
