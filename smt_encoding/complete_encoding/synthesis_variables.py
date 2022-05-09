from smt_encoding.constraints.function import Function, Sort, VariableFactory
from smt_encoding.instructions.encoding_instruction import ThetaValue
from typing import List, Union


def _sub_idx_rep(var_name: str, *indexes: Union[int, ThetaValue]) -> str:
    return "_".join([var_name, *[str(index) for index in indexes]])


class SynthesisVariables:
    """
    Class that generates the necessary Variables for the encoding.
    """

    def __init__(self):
        self._var_factory = VariableFactory()

    def u(self, i : int,j : int) -> Function:
        str_rep = _sub_idx_rep("u", i, j)
        return self._var_factory.create_variable(str_rep, Sort.boolean)

    def x(self, i : int,j : int) -> Function:
        str_rep = _sub_idx_rep("x", i, j)
        return self._var_factory.create_variable(str_rep, Sort.integer)

    def t(self, i : int) -> Function:
        str_rep = _sub_idx_rep("t", i)
        return self._var_factory.create_variable(str_rep, Sort.integer)

    def a(self, i : int) -> Function:
        str_rep = _sub_idx_rep("a", i)
        return self._var_factory.create_variable(str_rep, Sort.integer)

    def l(self, i : ThetaValue) -> Function:
        str_rep = _sub_idx_rep("l", i)
        return self._var_factory.create_variable(str_rep, Sort.integer)

    def s(self, i : int) -> Function:
        str_rep = _sub_idx_rep("s", i)
        return self._var_factory.create_variable(str_rep, Sort.integer)

    def created_variables(self) -> List[Function]:
        return self._var_factory.variables_created()