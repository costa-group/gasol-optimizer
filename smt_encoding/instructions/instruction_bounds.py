from smt_encoding.instructions.encoding_instruction import ThetaValue
from abc import ABC, abstractmethod

class InstructionBounds(ABC):
    """
    Interface for representing the necessary methods for encoding the bounds from the instructions
    """

    # Theta value associated to the instruction
    @abstractmethod
    def lower_bound_theta_value(self, theta_value : ThetaValue) -> int:
        raise NotImplementedError

    # Unique id that identifies the instruction. For instance, ADD_0, POP, PUSH_2...
    @abstractmethod
    def upper_bound_theta_value(self, theta_value : ThetaValue) -> int:
        raise NotImplementedError

    # Initial possible position
    @property
    @abstractmethod
    def first_position_sequence(self) -> int:
        pass

    # Initial possible position
    @property
    @abstractmethod
    def last_position_sequence(self) -> int:
        pass
