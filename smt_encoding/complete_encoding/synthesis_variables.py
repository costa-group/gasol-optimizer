from smt_encoding.constraints.variable import Variable, VariableType
from smt_encoding.instructions.encoding_instruction import ThetaValue

def _sub_idx_rep(var_name: str, *indexes: int | ThetaValue) -> str:
    return "_".join([var_name, *[str(index) for index in indexes]])


def u(i : int,j : int) -> Variable:
    str_rep = _sub_idx_rep("u", i, j)
    return Variable(str_rep, VariableType.integer)

def x(i : int,j : int) -> Variable:
    str_rep = _sub_idx_rep("x", i, j)
    return Variable(str_rep, VariableType.integer)

def t(i : int) -> Variable:
    str_rep = _sub_idx_rep("t", i)
    return Variable(str_rep, VariableType.integer)

def a(i : int) -> Variable:
    str_rep = _sub_idx_rep("a", i)
    return Variable(str_rep, VariableType.integer)

def l(i : ThetaValue) -> Variable:
    str_rep = _sub_idx_rep("l", i)
    return Variable(str_rep, VariableType.integer)

def s(i : int) -> Variable:
    str_rep = _sub_idx_rep("s", i)
    return Variable(str_rep, VariableType.integer)
