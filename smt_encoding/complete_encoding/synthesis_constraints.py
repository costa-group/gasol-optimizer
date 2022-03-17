from smt_encoding.complete_encoding.synthesis_variables import SynthesisVariables
from smt_encoding.complete_encoding.synthesis_predicates import move
from smt_encoding.constraints.connector_factory import add_eq, add_and, add_not, add_implies, add_leq, add_lt, add_or
import global_params.constants as constants
from smt_encoding.constraints.assertions import AssertHard
from typing import List, Callable
from smt_encoding.instructions.encoding_instruction import ThetaValue
from smt_encoding.instructions.instruction_bounds import InstructionBounds
from smt_encoding.constraints.formula import Formula_T


def push_basic_encoding(j : int, theta_push : ThetaValue, sv : SynthesisVariables, bs : int) -> AssertHard:
    left_term = add_eq(sv.t(j), theta_push)
    right_term = add_and(add_leq(0, sv.a(j)), add_lt(sv.a(j), constants.int_limit), add_not(sv.u(bs - 1, j)), sv.u(0, j + 1),
                         add_eq(sv.x(0, j+1), sv.a(j)), move(sv, j, 0, bs-2, 1))
    return AssertHard(add_implies(left_term, right_term))


def dupk_encoding(j : int, theta_dupk : ThetaValue, sv : SynthesisVariables, k : int, bs : int) -> AssertHard:
    left_term = add_eq(sv.t(j), theta_dupk)
    right_term = add_and(add_not(sv.u(bs-1, j)), sv.u(k-1, j), sv.u(0, j+1),
                          add_eq(sv.x(0, j+1), sv.x(k-1, j)), move(sv, j, 0, bs-2, 1))
    return AssertHard(add_implies(left_term, right_term))


def swapk_encoding(j : int, theta_swapk : ThetaValue, sv : SynthesisVariables, k : int, bs : int) -> AssertHard:
    left_term = add_eq(sv.t(j), theta_swapk)
    right_term = add_and(sv.u(k,j), sv.u(0, j+1), add_eq(sv.x(0, j+1), sv.x(k,j)) ,
                          sv.u(k, j+1), add_eq(sv.x(k, j+1), sv.x(0,j)),
                          move(sv, j, 1, k-1, 0), move(sv, j, k+1, bs-1, 0))
    return AssertHard(add_implies(left_term, right_term))


def pop_encoding(j : int, theta_pop : ThetaValue, sv : SynthesisVariables, bs : int) -> AssertHard:
    left_term = add_eq(sv.t(j), theta_pop)
    right_term = add_and(sv.u(0,j), add_not(sv.u(bs-1, j+1)), move(sv, j,1,bs-1,-1))
    return AssertHard(add_implies(left_term, right_term))


def pop_uninterpreted_encoding(j : int, theta_pop : ThetaValue, sv : SynthesisVariables, bs : int, o : Formula_T) -> AssertHard:
    left_term = add_eq(sv.t(j), theta_pop)
    right_term = add_and(sv.u(0,j), add_eq(sv.x(0,j), o), add_not(sv.u(bs-1, j+1)), move(sv, j,1,bs-1,-1))
    return AssertHard(add_implies(left_term, right_term))


def nop_encoding(j : int, theta_nop : ThetaValue, sv : SynthesisVariables, bs : int) -> AssertHard:
    left_term = add_eq(sv.t(j), theta_nop)
    right_term = move(sv, j,0,bs-1,0)
    return AssertHard(add_implies(left_term, right_term))


def non_comm_function_encoding(j : int, theta_f : ThetaValue, sv : SynthesisVariables, bs : int, o : List[Formula_T],
                               r: Formula_T) -> AssertHard:
    n = len(o)
    left_term = add_eq(sv.t(j), theta_f)
    right_term_first_and = [True]
    # Second and can be empty, so we initialize terms to true value
    right_term_second_and = [True]
    right_term_third_and = [True]
    for i in range(0, n):
        right_term_first_and.append(add_and(sv.u(i,j), add_eq(sv.x(i,j), o[i])))
    for i in range(bs-n+1, bs):
        right_term_second_and.append(add_not(sv.u(i, j+1)))
    for i in range(bs+n-1, bs):
        right_term_third_and.append(add_not(sv.u(i, j)))
    right_term = add_and(add_and(*right_term_first_and), sv.u(0, j+1) , add_eq(sv.x(0,j+1), r),
                          move(sv, j, n, min(bs-2+n, bs-1), 1-n) , add_and(*right_term_second_and),
                         add_and(*right_term_third_and))
    return AssertHard(add_implies(left_term, right_term))


def comm_function_encoding(j : int, theta_f : ThetaValue, sv : SynthesisVariables, bs : int, o0 : Formula_T, o1: Formula_T, r:Formula_T) -> AssertHard:
    left_term = add_eq(sv.t(j), theta_f)
    right_term = add_and(sv.u(0,j), sv.u(1,j),
                         add_or(add_and(add_eq(sv.x(0,j), o0), add_eq(sv.x(1,j), o1)), add_and(add_eq(sv.x(0,j), o1), add_eq(sv.x(1,j), o0))),
                         sv.u(0,j+1), add_eq(sv.x(0,j+1), r), move(sv, j, 2, bs-1, -1), add_not(sv.u(bs-1, j+1)))
    return AssertHard(add_implies(left_term, right_term))


def store_stack_function_encoding(j : int, theta_f : ThetaValue, sv : SynthesisVariables, bs : int, o0 : Formula_T, o1 : Formula_T) -> AssertHard:
    left_term = add_eq(sv.t(j), theta_f)
    right_term = add_and(sv.u(0,j), sv.u(1,j), add_and(add_eq(sv.x(0,j), o0), add_eq(sv.x(1,j), o1)),
                         move(sv, j, 2, bs-1, -2), add_not(sv.u(bs-1, j+1)), add_not(sv.u(bs-2, j+1)))
    return AssertHard(add_implies(left_term, right_term))


def stack_constraints_for_every_position(func: Callable[..., AssertHard], theta_val : ThetaValue,
                                         bounds : InstructionBounds , *args, **kwargs) -> List[AssertHard]:
    """
    Given a function that generates a hard constraint for a position in the sequence and the corresponding bounds, generates
    a list of hard constraints for each position within the bounds.

    :param func: Function that generates the encoding. First positional argument is the current position in the sequence
    to represent, and the second one the corresponding theta value.
    :param theta_val: theta value
    :param bounds: bound object containing the necessary info
    :param args: args params passed to func
    :param kwargs: kwards params passed to func
    :return: a list with a hard constraint for each position within the bounds
    """
    return [func(pos, theta_val, *args, **kwargs) for pos in range(bounds.lower_bound_theta_value(theta_val),
                                                                   bounds.upper_bound_theta_value(theta_val) + 1)]