from abc import ABC, abstractmethod
from .solver import Solver

class SolverFromExecutable(Solver, ABC):

    def __init__(self, solver_path : str):
        self._solver_path = solver_path


    @abstractmethod
    def execute_command(self, solver_path, **kwargs) -> str:
        """

        :param kwargs: args needed to execute the program
        :return: a string that stores the results from the model
        """
        raise NotImplementedError


    def execute(self, **kwargs):
        solver_output = execute_command