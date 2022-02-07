from smt_encoding.encoding_stack_instructions import push_encoding
from smt_encoding.instructions.basic_instruction import BasicInstruction


class PushBasic(BasicInstruction):

    def __init__(self, theta_value, initial_idx=0):
        self._theta_value = theta_value
        self.initial_idx = initial_idx

    def encoding_instruction(self, **kwargs):
        constraints = []

        bs = kwargs["bs"]
        initial_pos_seq = kwargs['initial_pos_seq']
        final_pos_seq = kwargs['final_pos_seq']

        for j in range(initial_pos_seq, final_pos_seq):
            constraints.append(push_encoding(j, bs, self.theta_value))

        return constraints

    @property
    def theta_value(self):
        return self._theta_value

    @property
    def id(self):
        return "PUSH"

    @property
    def opcode_name(self):
        return "PUSH"

    @property
    def size_cost(self):
        return 5

    @property
    def gas_cost(self):
        return 3
