import copy

from smt_encoding.constraints.function import Function, Sort, ExpressionReference
from smt_encoding.instructions.encoding_instruction import ThetaValue, Stack_Var_T
from smt_encoding.constraints.connector import Formula_T
from typing import List, Union, Tuple, Dict


def _sub_idx_rep(var_name: str, *indexes: Union[int, ThetaValue]) -> str:
    return "_".join([var_name, *[str(index) for index in indexes]])


class SynthesisFunctions:
    """
    Class that generates the necessary functions and terms for the GASOL encoding
    """

    def __init__(self, term_to_formula: Dict[str, Formula_T], evm_repr_sort: Sort = Sort.integer,
                 theta_repr_sort=Sort.integer):
        """

        :param evm_repr_sort: sort used for representing evm words in the stack. By default, they are represented
        as integers (but could be modelled using other sorts). This affects "x" variables, "a" variables and "s" variables,
        as well as the uninterpreted functions that represent EVM opcodes
        """
        # Func instances is directly initialize with the dict term to formula
        self._func_instances: Dict[str, Function] = {stack_var: term_to_formula[stack_var].func for stack_var in
                                                     term_to_formula
                                                     if type(term_to_formula[stack_var]) == ExpressionReference}
        self._expression_instances: Dict[str, Formula_T] = copy.deepcopy(term_to_formula)
        self._theta_expressions = {}
        self._evm_repr_sort = evm_repr_sort
        self._theta_repr_sort = theta_repr_sort

    def _create_func(self, name: str, var_type: Tuple[Sort]) -> Function:
        if name in self._func_instances:
            return self._func_instances[name]

        created_var = Function(name, *var_type)
        self._func_instances[name] = created_var
        return created_var

    def _create_term(self, func_name: str, var_type: Tuple[Sort],
                     arguments: Tuple[ExpressionReference], func_id: str) -> ExpressionReference:
        # Func id serves as a primary key for representing terms. For those terms that are constant, the func_id should
        # match the func_name. For stack variables, it corresponds to the name assigned to the output in the instruction
        if func_id in self._expression_instances:
            return self._expression_instances[func_id]

        func = self._create_func(func_name, var_type)
        return func(*arguments)

    def u(self, i: int, j: int) -> ExpressionReference:
        str_rep = _sub_idx_rep("u", i, j)
        return self._create_term(str_rep, (Sort.boolean,), tuple(), str_rep)

    def x(self, i: int, j: int) -> ExpressionReference:
        str_rep = _sub_idx_rep("x", i, j)
        return self._create_term(str_rep, (self._evm_repr_sort,), tuple(), str_rep)

    def t(self, i: int) -> ExpressionReference:
        str_rep = _sub_idx_rep("t", i)
        return self._create_term(str_rep, (self._theta_repr_sort,), tuple(), str_rep)

    def a(self, i: int) -> ExpressionReference:
        str_rep = _sub_idx_rep("a", i)
        return self._create_term(str_rep, (self._evm_repr_sort,), tuple(), str_rep)

    def l(self, i: ThetaValue) -> ExpressionReference:
        str_rep = _sub_idx_rep("l", i)
        return self._create_term(str_rep, (Sort.integer,), tuple(), str_rep)

    def stack_var(self, stack_var: Stack_Var_T) -> Formula_T:
        # If the stack corresponds to an integer, then we return the same value as a formula
        if type(stack_var) == int:
            return stack_var
        elif stack_var in self._expression_instances:
            return self._expression_instances[stack_var]
        else:
            raise ValueError(f"Stack var {stack_var} has no formula tied to it")

    def theta_value(self, theta_value: ThetaValue) -> Formula_T:
        if self._theta_repr_sort == Sort.integer:
            return theta_value
        else:
            str_rep = _sub_idx_rep("theta", theta_value)
            if str_rep in self._theta_expressions:
                return self._theta_expressions[str_rep]
            term = self._create_term(str_rep, (self._theta_repr_sort, ), tuple(), str_rep)
            self._theta_expressions[str_rep] = term
            return term

    def created_functions(self) -> List[Function]:
        return [func for func in self._func_instances.values()]

    def created_stack_vars(self) -> List[ExpressionReference]:
        return [expr for expr in self._expression_instances.values() if type(expr) == ExpressionReference]

    def created_theta_values(self) -> List[ExpressionReference]:
        return [expr for expr in self._theta_expressions.values() if type(expr) == ExpressionReference]
