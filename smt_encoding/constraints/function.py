from enum import Enum, unique
from typing import List, Tuple, Union


@unique
class Sort(Enum):
    boolean = 0
    integer = 1
    uninterpreted = 2
    uninterpreted_theta = 3


class Function:
    """
    Class that represents a function in the encoding (including constants)
    """

    def __init__(self, name: str, *var_type: Sort, **kwargs):
        if not len(var_type) > 0:
            raise ValueError(name + " needs at least one argument")
        self._name = name
        self._type = var_type
        self._comm_assoc = kwargs.get('comm_assoc', False)

    @property
    def name(self) -> str:
        return self._name

    @property
    def type(self) -> Tuple[Sort]:
        return self._type

    @property
    def arity(self) -> int:
        return len(self._type) - 1

    @property
    def domain(self) -> Tuple[Sort]:
        return self._type[:-1]

    @property
    def range(self) -> Sort:
        return self._type[-1]

    @property
    def comm_assoc(self) -> bool:
        return self._comm_assoc

    def __str__(self):
        return self._name

    def __repr__(self):
        return repr(self._name)

    def __eq__(self, other):
        return type(self) == type(other) and self.name == other.name and self.type == other.type

    def __call__(self, *args: Union['ExpressionReference', int, bool]):
        if len(args) != self.arity:
            raise ValueError(' '.join((self.name, "function has arity", str(self.arity))))
        for i, (arg, t) in enumerate(zip(args, self.domain)):
            if type(arg) == int:
                if t != Sort.integer:
                    raise ValueError(' '.join(("Sort mismatch in argument", str(i), ': Expected int and got ', str(t))))
            elif type(arg) == bool:
                if t != Sort.boolean:
                    raise ValueError(' '.join(("Sort mismatch in argument", str(i), ': Expected bool and got ', str(t))))
            elif arg.type != t:
                raise ValueError(' '.join(("Sort mismatch in argument", str(i), ':', str(arg.type), '!=', str(t))))
        return ExpressionReference(self, *args)


class ExpressionReference:
    """
    Class that represents an expression in the encoding
    """

    def __init__(self, func: Function, *args: Union['ExpressionReference', int, bool]):
        self._func = func
        self._args = args

    @property
    def func(self) -> Function:
        return self._func

    @property
    def type(self) -> Sort:
        return self._func.range

    @property
    def arguments(self) -> List[Union['ExpressionReference', int, bool]]:
        return [*self._args]

    def __str__(self):
        arguments_expression = "(" + ','.join([str(arg) for arg in self._args]) + ")" if len(self._args) > 0 else ' '
        return str(self._func) + arguments_expression

    def __repr__(self):
        arguments_expression = "(" + ','.join([str(arg) for arg in self._args]) + ")" if len(self._args) > 0 else ' '
        return str(self._func) + arguments_expression

    def __eq__(self, other):
        return type(self) == type(other) and self.func == other.func and self.type == other.type and \
               len(self.arguments) == len(other.arguments) and \
               all((self_arg1 == other_arg1 for self_arg1, other_arg1 in zip(self.arguments, other.arguments)))


def Const(name: str, sort: Sort) -> ExpressionReference:
    """
    Shortcut to initialize constant expressions directly, without declaring explicitly the corresponding function and
    then calling
    :param name: name of the constant
    :param sort: sort of the constant
    :return: an expression that represents the constant
    """
    return Function(name, sort)()
