from typing import Union
from smt_encoding.constraints.variable import Variable

Formula_T = Union['Connector', Variable, bool, int]
