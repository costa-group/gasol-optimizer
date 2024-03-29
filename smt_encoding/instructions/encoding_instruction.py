from abc import ABC, abstractmethod
from enum import Enum, unique
from typing import Union, Optional

@unique
class InstructionSubset(Enum):
    basic = 0
    store = 1
    comm = 2
    non_comm = 3
    pop = 4

ThetaValue = int
Id_T = str
Stack_Var_T = Union[str, int]

# Interface for representing the necessary methods for encoding an instruction
class EncodingInstruction(ABC):

    # Theta value associated to the instruction
    @property
    @abstractmethod
    def theta_value(self) -> ThetaValue:
        raise NotImplementedError

    # Unique id that identifies the instruction. For instance, ADD_0, POP, PUSH_2...
    @property
    @abstractmethod
    def id(self) -> Id_T:
        raise NotImplementedError

    # Generic name that identifies the instruction. For instance, ADD, POP, PUSH...
    @property
    @abstractmethod
    def opcode_name(self) -> str:
        raise NotImplementedError

    # Weight associated for size related constraints. For instance, ADD : 1, PUSHx: x, NOP: 0
    @property
    @abstractmethod
    def size_cost(self) -> int:
        raise NotImplementedError

    # Weight associated for gas related constraints. For instance, ADD : 3, PUSHx: 3, NOP: 0
    @property
    @abstractmethod
    def gas_cost(self) -> int:
        raise NotImplementedError

    # Whether this instruction can appear only once in a sequence or multiple times
    @property
    @abstractmethod
    def unique_ui(self) -> bool:
        raise NotImplementedError

    # Which subset the instruction belongs to. Every instruction must belong to a subset
    @property
    @abstractmethod
    def instruction_subset(self) -> InstructionSubset:
        raise NotImplementedError

    # If it has an additional value tied. Useful for some special PUSH pseudo-instructions
    @property
    @abstractmethod
    def value(self) -> Optional[int]:
        raise NotImplementedError
