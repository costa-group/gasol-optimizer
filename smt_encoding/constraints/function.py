from smt_encoding.singleton import Singleton
from enum import Enum, unique
from typing import List, Tuple


@unique
class Sort(Enum):
    boolean = 0
    integer = 1


class Function:
    """
    Class that represents a function in the encoding (including constants)
    """

    def __init__(self, name: str, *var_type: Sort):
        if not len(var_type) > 0:
            raise ValueError(name + " needs at least one argument")
        self._name = name
        self._type = var_type

    @property
    def name(self) -> str:
        return self._name

    @property
    def type(self) -> Tuple[Sort]:
        return self._type

    @property
    def arity(self) -> int:
        return len(self._type) - 1

    def __str__(self):
        return self._name

    def __repr__(self):
        return repr(self._name)

    def __eq__(self, other):
        return type(self) == type(other) and self.name == other.name and self.type == other.type


class VariableFactory:

    def __init__(self):
        self._instances = {}
        self._types = {}

    def create_variable(self, name: str, var_type: Sort) -> Function:
        if name in self._instances:
            if self._types[name] == var_type:
                return self._instances[name]
            else:
                raise ValueError("Variable " + name + " was already created using type " + self._types[name])
        created_var = Function(name, var_type)
        self._instances[name] = created_var
        self._types[name] = var_type
        return created_var

    def variables_created(self) -> List[Function]:
        return [self._instances[name] for name in self._instances]
