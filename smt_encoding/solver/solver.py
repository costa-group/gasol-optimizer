from abc import abstractmethod
from typing import Any
from smt_encoding.constraints.variable import Variable


class Solver:
    """
    Interface that encapsulates the necessary functions a solver must perform
    """

    @abstractmethod
    def set_logic(self, logic : str) -> None:
        pass


    @abstractmethod
    def set_option(self, option : str, value : str) -> None:
        pass


    @abstractmethod
    def solve(self) -> None:
        """
        Execute the SMT solver

        :param kwargs: arguments needed for the execution
        :return: no value is returned as a result
        """
        pass

    @abstractmethod
    def get_value(self, variable : Variable) -> Any:
        """
        Returns the model generated by the SMT solver. Note that it is assumed that method execute was called
        beforehand. If not an empty model must be returned

        :return: the stored model by the smt solver
        """
        pass