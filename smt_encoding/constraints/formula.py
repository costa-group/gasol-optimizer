from typing import Union
from smt_encoding.constraints.function import Function
from smt_encoding.constraints.connector import Connector

Formula_T = Union[Connector, Function, bool, int]
