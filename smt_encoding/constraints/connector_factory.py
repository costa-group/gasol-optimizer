from smt_encoding.constraints.connector import Connector
from smt_encoding.constraints.formula import Formula_T
from smt_encoding.singleton import Singleton


class Connectors(metaclass=Singleton):

    def __init__(self):
        self._connectors = set()
        self._arity = dict()
        self._commutative = dict()

    def register_connector(self, name: str, arity: int, is_commutative: bool) -> None:
        if name not in self._connectors:
            self._connectors.add(name)
            self._arity[name] = arity
            self._commutative[name] = is_commutative

    def create_connector(self, name: str, *args: Formula_T) -> Connector:
        if name not in self._connectors:
            raise ValueError(name + " is not a valid connector")
        arity = self._arity[name]
        is_commutative = self._commutative[name]
        if arity != -1:
            assert arity == len(args)
            return Connector(name, is_commutative, *args)
        else:
            assert len(args) > 0
            return Connector(name, is_commutative, *args)


_connectors = Connectors()
_connectors.register_connector("implies", 2, False)
_connectors.register_connector("and", -1, True)
_connectors.register_connector("or", -1, True)
_connectors.register_connector("not", 1, True)
_connectors.register_connector("equal", 2, True)
_connectors.register_connector("lt", 2, False)
_connectors.register_connector("leq", 2, False)

# Methods to generate logical connective asserts.


def add_implies(form1 : Formula_T, form2 : Formula_T) -> Connector:
    return _connectors.create_connector("implies", form1, form2)


def add_and(*formulas : Formula_T) -> Connector:
    return _connectors.create_connector("and", *formulas)


def add_or(*formulas : Formula_T) -> Connector:
    return _connectors.create_connector("or", *formulas)


def add_not(form : Formula_T) -> Connector:
    return _connectors.create_connector("not", form)


def add_eq(form1 : Formula_T, form2 : Formula_T) -> Connector:
    return _connectors.create_connector("equal", form1, form2)


def add_lt(form1 : Formula_T, form2 : Formula_T) -> Connector:
    return _connectors.create_connector("lt", form1, form2)


def add_leq(form1 : Formula_T, form2 : Formula_T) -> Connector:
    return _connectors.create_connector("leq", form1, form2)
