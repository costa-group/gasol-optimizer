from smt_encoding.constraints.variable import Variable, VariableType, VariableFactory
from smt_encoding.instructions.encoding_instruction import ThetaValue
from typing import List


def _sub_idx_rep(var_name: str, *indexes: int | ThetaValue) -> str:
    return "_".join([var_name, *[str(index) for index in indexes]])


class SynthesisVariables:
    """
    Class that generates the necessary Variables for the encoding.
    """

    def __init__(self):
        self._var_factory = VariableFactory()

    def u(self, i : int,j : int) -> Variable:
        str_rep = _sub_idx_rep("u", i, j)
        return self._var_factory.create_variable(str_rep, VariableType.boolean)

    def x(self, i : int,j : int) -> Variable:
        str_rep = _sub_idx_rep("x", i, j)
        return self._var_factory.create_variable(str_rep, VariableType.integer)

    def t(self, i : int) -> Variable:
        str_rep = _sub_idx_rep("t", i)
        return self._var_factory.create_variable(str_rep, VariableType.integer)

    def a(self, i : int) -> Variable:
        str_rep = _sub_idx_rep("a", i)
        return self._var_factory.create_variable(str_rep, VariableType.integer)

    def l(self, i : ThetaValue) -> Variable:
        str_rep = _sub_idx_rep("l", i)
        return self._var_factory.create_variable(str_rep, VariableType.integer)

    def s(self, i : int) -> Variable:
        str_rep = _sub_idx_rep("s", i)
        return self._var_factory.create_variable(str_rep, VariableType.integer)

    def created_variables(self) -> List[Variable]:
        return self._var_factory.variables_created()