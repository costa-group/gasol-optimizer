from smt_encoding.constraints.formula import Formula_T

class AssertHard:

    def __init__(self, formula : Formula_T):
        self.formula = formula

    def __str__(self):
        return str(self.formula)

    def __repr__(self):
        return str(self.formula)

    def __eq__(self, other):
        return self.formula == other.formula

class AssertSoft:

    def __init__(self, formula: Formula_T, weight: int = 1, group: str = "default"):
        self.formula = formula
        self.weight = weight
        self.group = group

    def __str__(self):
        return ' '.join([str(self.formula), "weight:", self.weight, "group:", self.group])

    def __repr__(self):
        return ' '.join([str(self.formula), "weight:", self.weight, "group:", self.group])

    def __eq__(self, other):
        return self.formula == other.formula and self.weight == other.weight and self.group == other.group
