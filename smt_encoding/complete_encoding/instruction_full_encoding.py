

class InstructionFullEncoding:
    """
    Class that manages the general encoding of the sms problem, without considering flags.
    This class includes all declarations for redundant constraints, memory constraints, soft constraints and the
    overall generation of hard constraints
    """

    def __init__(self, instructions):
        self.instructions = instructions

    # Returns the set of instructions that are not uninterpreted (\I_S)
    def basic_instructions(self):
        pass