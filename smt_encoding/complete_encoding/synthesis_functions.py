from smt_encoding.constraints.function import Function, Sort, ExpressionReference
from smt_encoding.instructions.encoding_instruction import ThetaValue
from typing import List, Union, Tuple, Dict


def _sub_idx_rep(var_name: str, *indexes: Union[int, ThetaValue]) -> str:
    return "_".join([var_name, *[str(index) for index in indexes]])


class SynthesisFunctions:
    """
    Class that generates the necessary functions and terms for the GASOL encoding
    """

    def __init__(self, evm_repr_sort: Sort = Sort.integer):
        """

        :param evm_repr_sort: sort used for representing evm words in the stack. By default, they are represented
        as integers (but could be modelled using other sorts). This affects "x" variables, "a" variables and "s" variables,
        as well as the uninterpreted functions that represent EVM opcodes
        """
        self._func_instances: Dict[str, Function] = {}
        self._types = {}
        self._evm_repr_sort = evm_repr_sort

    def _create_func(self, name: str, var_type: Tuple[Sort]) -> Function:
        if name in self._func_instances:
            if self._types[name] == var_type:
                return self._func_instances[name]
            else:
                raise ValueError("Function " + name + " was already created using type " + self._types[name])
        created_var = Function(name, *var_type)
        self._func_instances[name] = created_var
        self._types[name] = var_type
        return created_var

    def _create_term(self, func_name: str, var_type: Tuple[Sort],
                     arguments: Tuple[ExpressionReference]) -> ExpressionReference:
        func = self._create_func(func_name, var_type)
        return func(*arguments)

    def u(self, i: int, j: int) -> ExpressionReference:
        str_rep = _sub_idx_rep("u", i, j)
        return self._create_term(str_rep, (Sort.boolean, ), tuple())

    def x(self, i: int, j: int) -> ExpressionReference:
        str_rep = _sub_idx_rep("x", i, j)
        return self._create_term(str_rep, (self._evm_repr_sort,), tuple())

    def t(self, i: int) -> ExpressionReference:
        str_rep = _sub_idx_rep("t", i)
        return self._create_term(str_rep, (Sort.integer,), tuple())

    def a(self, i: int) -> ExpressionReference:
        str_rep = _sub_idx_rep("a", i)
        return self._create_term(str_rep, (self._evm_repr_sort,), tuple())

    def l(self, i: ThetaValue) -> ExpressionReference:
        str_rep = _sub_idx_rep("l", i)
        return self._create_term(str_rep, (Sort.integer,), tuple())

    def s(self, i: int) -> ExpressionReference:
        str_rep = _sub_idx_rep("s", i)
        return self._create_term(str_rep, (self._evm_repr_sort,), tuple())

    def func(self, func_name: str, is_comm_assoc: bool):
        pass

    def created_functions(self) -> List[Function]:
        return [func for func in self._func_instances.values()]
