from smt_encoding.constraints.formula import Formula_T

class AssertHard:

    def __init__(self, formula : Formula_T):
        self.formula = formula

    def __str__(self):
        return str(self.formula)

    def __repr__(self):
        return str(self.formula)

class AssertSoft:

    def __init__(self, formula : Formula_T, weight : int, group : str):
        self.formula = formula
        self.weight = weight
        self.group = group

    def __str__(self):
        return ' '.join([str(self.formula), "weight:", self.weight, "group:", self.group])

    def __repr__(self):
        return ' '.join([str(self.formula), "weight:", self.weight, "group:", self.group])