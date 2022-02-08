from smt_encoding.constraints.connector_factory import add_eq, add_and
from smt_encoding.complete_encoding.synthesis_variables import u, x
from smt_encoding.constraints.formula import Formula_T


def move(j : int, alpha : int, beta : int, delta : int) -> Formula_T:
    and_variables = []

    # Move can be empty
    if alpha > beta:
        return True
    for i in range(alpha, beta+1):
        first_and = add_eq(u(i+delta, j+1), u(i,j))
        second_and = add_eq(x(i+delta, j+1), x(i,j))
        and_variables.append(add_and(first_and, second_and))
    return add_and(*and_variables)
