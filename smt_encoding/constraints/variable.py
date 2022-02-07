from smt_encoding.singleton import Singleton
from enum import Enum, unique
from typing import List, Tuple

@unique
class VariableType(Enum):
    boolean = 0
    integer = 1

class Variable:
    """
    Class that represents a variable in the encoding
    """

    def __init__(self, name : str, var_type : VariableType):
        self._name = name
        self._type = var_type

    @property
    def name(self):
        return self.name

    @property
    def type(self):
        return self.type

    def __str__(self):
        return self._name

    def __repr__(self):
        return repr(self._name)


class VariableFactory:

    def __init__(self):
        self._instances = {}
        self._types = {}

    def create_variable(self, name : str, var_type : VariableType) -> Variable:
        if name in self._instances:
            if self._types[name] == var_type:
                return self._instances[name]
            else:
                raise ValueError("Variable " + name + " was already created using type " + self._types[name])
        created_var = Variable(name, var_type)
        self._instances[name] = created_var
        self._types[name] = var_type
        return created_var


    def variables_created(self) -> List[Tuple[str, VariableType]]:
        return [(val, self._types[key]) for key, val in self._instances.items()]