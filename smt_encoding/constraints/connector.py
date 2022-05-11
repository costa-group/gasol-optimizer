from typing import List
from smt_encoding.constraints.formula import Formula_T
import itertools


class Connector:

    def __init__(self, name: str, is_commutative: bool, *args):
        self._name = name
        self._is_commutative = is_commutative
        self._args = list(args)

    @property
    def connector_name(self) -> str:
        return self._name

    @property
    def arguments(self) -> List[Formula_T]:
        return self._args

    @property
    def is_commutative(self) -> bool:
        return self._is_commutative

    def __str__(self):
        return self._name + "(" + ','.join([str(arg) for arg in self._args]) + ")"

    def __repr__(self):
        return repr(self._name + "(" + ','.join([str(arg) for arg in self._args]) + ")")

    # Allows comparing commutative connectors as well
    def __eq__(self, other):
        if type(self) != type(other) or self.is_commutative != other.is_commutative:
            return False
        if self.is_commutative:
            if len(self.arguments) == len(other.arguments):
                exists_correct = False
                for permutation in itertools.permutations(self.arguments):
                    correct_permutation = all(arg1 == arg2 for arg1, arg2 in zip(permutation, other.arguments))

                    if correct_permutation:
                        exists_correct = True
                        break
                return self.connector_name == other.connector_name and exists_correct
            else:
                return False
        return self.connector_name == other.connector_name and len(self.arguments) == len(other.arguments) and \
               all(arg1 == arg2 for arg1, arg2 in zip(self.arguments, other.arguments))
