from smt_encoding.constraints.connector import Connector
from smt_encoding.constraints.formula import Formula_T
from smt_encoding.singleton import Singleton
from typing import Callable, Dict


class Connectors(metaclass=Singleton):

    def __init__(self):
        self._connectors = set()
        self._arity = dict()
        self._commutative = dict()
        self._simplify_function = dict()

    def register_connector(self, name: str, arity: int, is_commutative: bool,
                           simplify_function: Callable[[Connector], Formula_T]) -> None:
        if name not in self._connectors:
            self._connectors.add(name)
            self._arity[name] = arity
            self._commutative[name] = is_commutative
            self._simplify_function[name] = simplify_function

    def create_connector(self, name: str, *args: Formula_T) -> Connector:
        if name not in self._connectors:
            raise ValueError(name + " is not a valid connector")
        arity = self._arity[name]
        is_commutative = self._commutative[name]
        if arity != -1:
            assert arity == len(args)
        else:
            assert len(args) > 0
        return Connector(name, is_commutative, *args)

    def simplify_function(self, connector: Connector) -> Formula_T:
        if connector.connector_name not in self._connectors:
            raise ValueError(connector.connector_name + " is not a valid connector")
        return self._simplify_function[connector.connector_name](connector)

    # Invariant: the created connector is simplified at the ground level. If this method is called when declaring
    # a function, we can ensure the whole composed expression is simplified
    def create_connector_and_simplify(self, name: str, *args: Formula_T):
        connector = self.create_connector(name, *args)
        return self.simplify_function(connector)


_connectors = Connectors()


def _simplify_implies(simplify_connector: Connector) -> Formula_T:
    lhs, rhs = simplify_connector.arguments
    if type(lhs) == bool:
        # not lhs makes the implication trivially true
        if not lhs:
            return True
        # this branch assumes lhs is true, so we just return rhs
        else:
            return rhs
    elif type(rhs) == bool:
        # rhs makes the implication trivially true
        if rhs:
            return True
        else:
            return _connectors.create_connector_and_simplify("not", lhs)
    else:
        return simplify_connector


_connectors.register_connector("implies", 2, False, _simplify_implies)


def _simplify_and(and_connector: Connector) -> Formula_T:
    and_arguments = and_connector.arguments
    if any(type(argument) == bool and not argument for argument in and_arguments):
        return False
    new_arguments = []
    for argument in and_arguments:
        # True arguments are skipped
        if type(argument) != bool:
            # Nested and are flattened
            if type(argument) == Connector and argument.connector_name == "and":
                new_arguments.extend(argument.arguments)
            # Otherwise, just add the argument
            else:
                new_arguments.append(argument)

    # Final case: remove "and" if only one argument remains
    if len(new_arguments) == 1:
        return list(new_arguments)[0]

    return _connectors.create_connector("and", *new_arguments)


_connectors.register_connector("and", -1, True, _simplify_and)


def _simplify_or(or_connector: Connector) -> Formula_T:
    and_arguments = or_connector.arguments
    if any(type(argument) == bool and argument for argument in and_arguments):
        return True
    new_arguments = []
    for argument in and_arguments:
        # False arguments are skipped
        if type(argument) != bool:
            # Nested or are flattened
            if type(argument) == Connector and argument.connector_name == "or":
                new_arguments.extend(argument.arguments)
            # Otherwise, just add the argument
            else:
                new_arguments.append(argument)

    # Final case: remove "or" if only one argument
    if len(new_arguments) == 1:
        return new_arguments[0]

    return _connectors.create_connector("or", *new_arguments)


_connectors.register_connector("or", -1, True, _simplify_or)


def _simplify_not(not_connector: Connector) -> Formula_T:
    not_argument = not_connector.arguments[0]
    if type(not_argument) == Connector and not_argument.connector_name == "not":
        return not_argument.arguments[0]
    elif type(not_argument) == bool:
        return not not_argument
    else:
        return not_connector


_connectors.register_connector("not", 1, True, _simplify_not)


def _simplify_equal(equal_connector: Connector) -> Formula_T:
    lhs, rhs = equal_connector.arguments
    if (type(lhs) == bool or type(lhs) == int) and (type(rhs) == bool or type(rhs) == int):
        return lhs == rhs
    # Represents the possibility two terms are syntactically the same
    elif lhs == rhs:
        return True
    else:
        return equal_connector


_connectors.register_connector("equal", 2, True, _simplify_equal)

_connectors.register_connector("lt", 2, False, lambda x: x)

_connectors.register_connector("leq", 2, False, lambda x: x)

# Methods to generate logical connective asserts.


def add_implies(form1: Formula_T, form2: Formula_T) -> Connector:
    return _connectors.create_connector_and_simplify("implies", form1, form2)


def add_and(*formulas: Formula_T) -> Connector:
    return _connectors.create_connector_and_simplify("and", *formulas)


def add_or(*formulas: Formula_T) -> Connector:
    return _connectors.create_connector_and_simplify("or", *formulas)


def add_not(form: Formula_T) -> Connector:
    return _connectors.create_connector_and_simplify("not", form)


def add_eq(form1: Formula_T, form2: Formula_T) -> Connector:
    return _connectors.create_connector_and_simplify("equal", form1, form2)


def add_lt(form1: Formula_T, form2: Formula_T) -> Connector:
    return _connectors.create_connector_and_simplify("lt", form1, form2)


def add_leq(form1: Formula_T, form2: Formula_T) -> Connector:
    return _connectors.create_connector_and_simplify("leq", form1, form2)
