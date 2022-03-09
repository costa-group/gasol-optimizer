from smt_encoding.constraints.formula import Formula_T

class Assert:

    def __init__(self, formula : Formula_T):
        self.formula = formula

class AssertSoft:

    def __init__(self, formula : Formula_T, weight : int, group : str):
        self.formula = formula
        self.weight = weight
        self.group = group