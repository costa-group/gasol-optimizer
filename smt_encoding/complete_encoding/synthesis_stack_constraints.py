from smt_encoding.complete_encoding.synthesis_functions import SynthesisFunctions
from smt_encoding.complete_encoding.synthesis_predicates import move
from smt_encoding.constraints.connector_factory import add_eq, add_and, add_not, add_implies, add_leq, add_lt, add_or, Formula_T
import global_params.constants as constants
from smt_encoding.constraints.assertions import AssertHard
from typing import List
from smt_encoding.instructions.encoding_instruction import ThetaValue


def push_basic_encoding(j: int, theta_push: ThetaValue, sf: SynthesisFunctions, bs: int) -> AssertHard:
    left_term = add_eq(sf.t(j), theta_push)
    right_term = add_and(add_leq(0, sf.a(j)), add_lt(sf.a(j), constants.int_limit), add_not(sf.u(bs - 1, j)),
                         sf.u(0, j + 1),
                         add_eq(sf.x(0, j + 1), sf.a(j)), move(sf, j, 0, bs - 2, 1))
    return AssertHard(add_implies(left_term, right_term))


def dupk_encoding(j: int, theta_dupk: ThetaValue, sf: SynthesisFunctions, k: int, bs: int) -> AssertHard:
    left_term = add_eq(sf.t(j), theta_dupk)
    right_term = add_and(add_not(sf.u(bs - 1, j)), sf.u(k - 1, j), sf.u(0, j + 1),
                         add_eq(sf.x(0, j + 1), sf.x(k - 1, j)), move(sf, j, 0, bs - 2, 1))
    return AssertHard(add_implies(left_term, right_term))


def swapk_encoding(j: int, theta_swapk: ThetaValue, sf: SynthesisFunctions, k: int, bs: int) -> AssertHard:
    left_term = add_eq(sf.t(j), theta_swapk)
    right_term = add_and(sf.u(k, j), sf.u(0, j + 1), add_eq(sf.x(0, j + 1), sf.x(k, j)),
                         sf.u(k, j + 1), add_eq(sf.x(k, j + 1), sf.x(0, j)),
                         move(sf, j, 1, k - 1, 0), move(sf, j, k + 1, bs - 1, 0))
    return AssertHard(add_implies(left_term, right_term))


def pop_encoding(j: int, theta_pop: ThetaValue, sf: SynthesisFunctions, bs: int) -> AssertHard:
    left_term = add_eq(sf.t(j), theta_pop)
    right_term = add_and(sf.u(0, j), add_not(sf.u(bs - 1, j + 1)), move(sf, j, 1, bs - 1, -1))
    return AssertHard(add_implies(left_term, right_term))


def pop_uninterpreted_encoding(j: int, theta_pop: ThetaValue, sf: SynthesisFunctions,
                               bs: int, o: Formula_T) -> AssertHard:
    left_term = add_eq(sf.t(j), theta_pop)
    right_term = add_and(sf.u(0, j), add_eq(sf.x(0, j), o), add_not(sf.u(bs - 1, j + 1)), move(sf, j, 1, bs - 1, -1))
    return AssertHard(add_implies(left_term, right_term))


def nop_encoding(j: int, theta_nop: ThetaValue, sf: SynthesisFunctions, bs: int) -> AssertHard:
    left_term = add_eq(sf.t(j), theta_nop)
    right_term = move(sf, j, 0, bs - 1, 0)
    return AssertHard(add_implies(left_term, right_term))


def non_comm_function_encoding(j: int, theta_f: ThetaValue, sf: SynthesisFunctions, bs: int, o: List[Formula_T],
                               r: Formula_T) -> AssertHard:
    n = len(o)
    left_term = add_eq(sf.t(j), theta_f)
    right_term_first_and = [add_and(sf.u(i, j), add_eq(sf.x(i, j), o[i])) for i in range(0, n)]
    # Second and can be empty, so we initialize terms to true value
    right_term_second_and = [add_not(sf.u(i, j + 1)) for i in range(bs - n + 1, bs)]
    right_term_third_and = [add_not(sf.u(i, j)) for i in range(bs + n - 1, bs)]

    combined_and = add_and(*right_term_first_and, *right_term_second_and, *right_term_third_and) \
        if right_term_first_and != [] or right_term_second_and != [] or right_term_third_and != [] else True

    right_term = add_and(combined_and, sf.u(0, j + 1), add_eq(sf.x(0, j + 1), r),
                         move(sf, j, n, min(bs - 2 + n, bs - 1), 1 - n))

    return AssertHard(add_implies(left_term, right_term))


def comm_function_encoding(j: int, theta_f: ThetaValue, sf: SynthesisFunctions, bs: int, o0: Formula_T, o1: Formula_T,
                           r: Formula_T) -> AssertHard:
    left_term = add_eq(sf.t(j), theta_f)
    right_term = add_and(sf.u(0, j), sf.u(1, j),
                         add_or(add_and(add_eq(sf.x(0, j), o0), add_eq(sf.x(1, j), o1)),
                                add_and(add_eq(sf.x(0, j), o1), add_eq(sf.x(1, j), o0))),
                         sf.u(0, j + 1), add_eq(sf.x(0, j + 1), r), move(sf, j, 2, bs - 1, -1),
                         add_not(sf.u(bs - 1, j + 1)))
    return AssertHard(add_implies(left_term, right_term))


def store_stack_function_encoding(j: int, theta_f: ThetaValue, sf: SynthesisFunctions, bs: int, o0: Formula_T,
                                  o1: Formula_T) -> AssertHard:
    left_term = add_eq(sf.t(j), theta_f)
    right_term = add_and(sf.u(0, j), sf.u(1, j), add_and(add_eq(sf.x(0, j), o0), add_eq(sf.x(1, j), o1)),
                         move(sf, j, 2, bs - 1, -2), add_not(sf.u(bs - 1, j + 1)), add_not(sf.u(bs - 2, j + 1)))
    return AssertHard(add_implies(left_term, right_term))