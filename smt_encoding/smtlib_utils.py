# Module containing all necessary functions to generate
# a SMT-Lib script. All methods return a string with
# the corresponding statement.

# Methods to generate logical connective asserts.

# Given a logical connective symbol and its operands,
# returns the corresponding statement
def _add_connective(connective_name, *formulas):
    string = "(" + connective_name
    for formula in formulas:
        string += " " + str(formula)
    string += ")"
    return string


def add_implies(form1, form2):
    return _add_connective("=>", form1, form2)


def add_and(*formulas):
    return _add_connective("and", *formulas)


def add_or(*formulas):
    return _add_connective("or", *formulas)


def add_not(formula):
    return _add_connective("not", formula)


def add_eq(form1, form2):
    return _add_connective("=", form1, form2)


def add_leq(form1, form2):
    return _add_connective("<=", form1, form2)


def add_lt(form1, form2):
    return _add_connective("<", form1, form2)

# Methods to declare variables

# Given a variable prefix and the indexes,
# returns the corresponding string
def var2str(var_name, *indexes):
    string = str(var_name)
    for index in indexes:
        string += "_" + str(index)
    return string

def _declare_variable(var_name, var_type):
    return "(declare-fun " + str(var_name) + " () " + str(var_type) + ")"


def declare_boolvar(var_name):
    return _declare_variable(var_name, "Bool")


def declare_intvar(var_name):
    return _declare_variable(var_name, "Int")


# Methods to add asserts

def add_assert(statement):
    return "(assert "+ statement +")"


def add_assert_soft(statement, weight, id=None, exclamation=False):
    if id is None:
        if not exclamation:
            return "(assert-soft " + statement + " :weight " + str(weight) + ")"
        else:
            return "(assert-soft (! " + statement + " :weight " + str(weight) + "))"
    else:
        if not exclamation:
            return "(assert-soft " + statement + " :weight " + str(weight) + " :id " + str(id) + ")"
        else:
            return "(assert-soft (! " + statement + " :weight " + str(weight) + " :id " + str(id) + "))"

# Methods to generate auxiliary statements for
# SMT-Lib

def set_logic(mode):
    return "(set-logic " + mode + ")"


def check_sat():
    return "(check-sat)"


def get_objectives():
    return "(get-objectives)"


def get_model():
    return "(get-model)"


def get_value(variable):
    return "(get-value (" + str(variable) + "))"


def set_timeout(time_in_ms):
    return "(set-option :timeout " + str(time_in_ms) + ")"


# For OMS: flag to allow to generate a model
def set_model_true():
    return "(set-option :produce-models true)"


# Extension in OMS and Z3 to minimize a certain term
def set_minimize_function(id):
    return "(minimize " + id + ")"


# Allows to generate model when the optimal solution hasn't been
# found in OptiMathSat
def load_objective_model():
    return "(load-objective-model -1)"
