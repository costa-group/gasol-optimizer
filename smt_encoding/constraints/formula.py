from typing import Union
from smt_encoding.constraints.function import Function

Formula_T = Union['Connector', Function, bool, int]
