from smt_encoding.constraints.variable import Variable, VariableFactory, VariableType

def _sub_idx_rep(var_name: str, *indexes: int) -> str:
    return "_".join([var_name, *[str(index) for index in indexes]])

class SynthesisVariables:

    def __init__(self, var_factory : VariableFactory):
        self._var_factory = var_factory

    def u(self, i : int,j : int) -> Variable:
        str_rep = _sub_idx_rep("u", i, j)
        return self._var_factory.create_variable(str_rep, VariableType.integer)

    def x(self, i : int,j : int) -> Variable:
        str_rep = _sub_idx_rep("x", i, j)
        return self._var_factory.create_variable(str_rep, VariableType.integer)

    def t(self, i : int) -> Variable:
        str_rep = _sub_idx_rep("t", i)
        return self._var_factory.create_variable(str_rep, VariableType.integer)

    def a(self, i : int) -> Variable:
        str_rep = _sub_idx_rep("a", i)
        return self._var_factory.create_variable(str_rep, VariableType.integer)

    def l(self, i : int) -> Variable:
        str_rep = _sub_idx_rep("l", i)
        return self._var_factory.create_variable(str_rep, VariableType.integer)

    def s(self, i : int) -> Variable:
        str_rep = _sub_idx_rep("s", i)
        return self._var_factory.create_variable(str_rep, VariableType.integer)
