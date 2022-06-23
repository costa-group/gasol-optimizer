from smt_encoding.constraints.connector_factory import add_eq, add_and, Formula_T
from smt_encoding.complete_encoding.synthesis_functions import SynthesisFunctions


def move(sf: SynthesisFunctions, j: int, alpha: int, beta: int, delta: int) -> Formula_T:
    and_variables = []

    # Move can be empty
    if alpha > beta:
        return True
    for i in range(alpha, beta+1):
        first_and = add_eq(sf.u(i+delta, j+1), sf.u(i, j))
        second_and = add_eq(sf.x(i+delta, j+1), sf.x(i, j))
        and_variables.append(add_and(first_and, second_and))
    return add_and(*and_variables)


def move_only_x_j_i(sf: SynthesisFunctions, j: int, alpha: int, beta: int, delta: int) -> Formula_T:
    # Move can be empty
    if alpha > beta:
        return True
    return add_and(*(add_eq(sf.x(i+delta, j+1), sf.x(i, j)) for i in range(alpha, beta+1)))
