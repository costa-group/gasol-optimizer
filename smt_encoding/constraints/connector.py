from typing import List
from smt_encoding.constraints.formula import Formula_T

class Connector:

    def __init__(self, name, *args):
        self._name = name
        self._args = list(args)

    @property
    def connector(self) -> str:
        return self._name

    @property
    def arguments(self) -> List[Formula_T]:
        return self._args

    def __str__(self):
        return self._name + "(" + ','.join([str(arg) for arg in self._args])  + ")"


    def __repr__(self):
        return repr(self._name + "(" + ','.join([str(arg) for arg in self._args])  + ")")
