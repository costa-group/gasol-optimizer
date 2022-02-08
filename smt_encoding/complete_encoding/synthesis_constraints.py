from smt_encoding.complete_encoding.synthesis_variables import x, u, t, a
from smt_encoding.complete_encoding.synthesis_predicates import move
from smt_encoding.constraints.connector_factory import add_eq, add_and, add_not, add_implies, add_leq, add_lt, add_or
import global_params.constants as constants
from smt_encoding.constraints.assertions import Assert
from typing import List

def push_encoding(j : int, bs : int, theta_push : int) -> Assert:
    left_term = add_eq(t(j), theta_push)
    right_term = add_and(add_leq(0, a(j)), add_lt(a(j), constants.int_limit), add_not(u(bs - 1, j)), u(0, j + 1),
                         add_eq(x(0, j+1), a(j)), move(j, 0, bs-2, 1))
    return Assert(add_implies(left_term, right_term))


def dupk_encoding(k : int, j : int, bs : int, theta_dupk : int) -> Assert:
    left_term = add_eq(t(j), theta_dupk)
    right_term = add_and(add_not(u(bs-1, j)), u(k-1, j), u(0, j+1),
                          add_eq(x(0, j+1), x(k-1, j)), move(j, 0, bs-2, 1))
    return Assert(add_implies(left_term, right_term))


def swapk_encoding(k : int, j : int, bs : int, theta_swapk : int) -> Assert:
    left_term = add_eq(t(j), theta_swapk)
    right_term = add_and(u(k,j), u(0, j+1), add_eq(x(0, j+1), x(k,j)) ,
                          u(k, j+1), add_eq(x(k, j+1), x(0,j)),
                          move(j, 1, k-1, 0), move(j, k+1, bs-1, 0))
    return Assert(add_implies(left_term, right_term))


def pop_encoding(j : int, bs : int, theta_pop : int) -> Assert:
    left_term = add_eq(t(j), theta_pop)
    right_term = add_and(u(0,j), add_not(u(bs-1, j+1)), move(j,1,bs-1,-1))
    return Assert(add_implies(left_term, right_term))


def pop_uninterpreted_encoding(j : int, bs : int, o : int, theta_pop : int) -> Assert:
    left_term = add_eq(t(j), theta_pop)
    right_term = add_and(u(0,j), add_eq(x(0,j), o), add_not(u(bs-1, j+1)), move(j,1,bs-1,-1))
    return Assert(add_implies(left_term, right_term))


def nop_encoding(j : int, bs : int, theta_nop : int) -> Assert:
    left_term = add_eq(t(j), theta_nop)
    right_term = move(j,0,bs-1,0)
    return Assert(add_implies(left_term, right_term))


def fromnop_encoding(b0, theta_nop, initial_idx) -> List[Assert]:
    constraints = []
    for j in range(initial_idx, b0-1+initial_idx):
        left_term = add_eq(t(j), theta_nop)
        right_term = add_eq(t(j+1), theta_nop)
        constraints.append(Assert(add_implies(left_term, right_term)))
    return constraints