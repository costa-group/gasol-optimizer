from smt_encoding.complete_encoding.synthesis_variables import SynthesisVariables
from smt_encoding.complete_encoding.synthesis_predicates import move
from smt_encoding.constraints.connector_factory import add_eq, add_and, add_not, add_implies, add_leq, add_lt, add_or
import global_params.constants as constants
from smt_encoding.constraints.assertions import Assert
from typing import List
from smt_encoding.instructions.encoding_instruction import ThetaValue


def push_basic_encoding(sv : SynthesisVariables, j : int, bs : int, theta_push : ThetaValue) -> Assert:
    left_term = add_eq(sv.t(j), theta_push)
    right_term = add_and(add_leq(0, sv.a(j)), add_lt(sv.a(j), constants.int_limit), add_not(sv.u(bs - 1, j)), sv.u(0, j + 1),
                         add_eq(sv.x(0, j+1), sv.a(j)), move(sv, j, 0, bs-2, 1))
    return Assert(add_implies(left_term, right_term))


def dupk_encoding(sv : SynthesisVariables, k : int, j : int, bs : int, theta_dupk : ThetaValue) -> Assert:
    left_term = add_eq(sv.t(j), theta_dupk)
    right_term = add_and(add_not(sv.u(bs-1, j)), sv.u(k-1, j), sv.u(0, j+1),
                          add_eq(sv.x(0, j+1), sv.x(k-1, j)), move(sv, j, 0, bs-2, 1))
    return Assert(add_implies(left_term, right_term))


def swapk_encoding(sv : SynthesisVariables, k : int, j : int, bs : int, theta_swapk : ThetaValue) -> Assert:
    left_term = add_eq(sv.t(j), theta_swapk)
    right_term = add_and(sv.u(k,j), sv.u(0, j+1), add_eq(sv.x(0, j+1), sv.x(k,j)) ,
                          sv.u(k, j+1), add_eq(sv.x(k, j+1), sv.x(0,j)),
                          move(sv, j, 1, k-1, 0), move(sv, j, k+1, bs-1, 0))
    return Assert(add_implies(left_term, right_term))


def pop_encoding(sv : SynthesisVariables, j : int, bs : int, theta_pop : ThetaValue) -> Assert:
    left_term = add_eq(sv.t(j), theta_pop)
    right_term = add_and(sv.u(0,j), add_not(sv.u(bs-1, j+1)), move(sv, j,1,bs-1,-1))
    return Assert(add_implies(left_term, right_term))


def pop_uninterpreted_encoding(sv : SynthesisVariables, j : int, bs : int, o : int, theta_pop : ThetaValue) -> Assert:
    left_term = add_eq(sv.t(j), theta_pop)
    right_term = add_and(sv.u(0,j), add_eq(sv.x(0,j), o), add_not(sv.u(bs-1, j+1)), move(sv, j,1,bs-1,-1))
    return Assert(add_implies(left_term, right_term))


def nop_encoding(sv : SynthesisVariables, j : int, bs : int, theta_nop : ThetaValue) -> Assert:
    left_term = add_eq(sv.t(j), theta_nop)
    right_term = move(sv, j,0,bs-1,0)
    return Assert(add_implies(left_term, right_term))


def fromnop_encoding(sv : SynthesisVariables, b0 : int, initial_idx : int, theta_nop: ThetaValue) -> List[Assert]:
    constraints = []
    for j in range(initial_idx, b0-1+initial_idx):
        left_term = add_eq(sv.t(j), theta_nop)
        right_term = add_eq(sv.t(j+1), theta_nop)
        constraints.append(Assert(add_implies(left_term, right_term)))
    return constraints