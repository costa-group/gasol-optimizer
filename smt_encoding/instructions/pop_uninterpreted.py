from smt_encoding.encoding_stack_instructions import pop_uninterpreted_encoding
from smt_encoding.instructions.uninterpreted_instruction import UninterpretedFunction


class PopUninterpreted(UninterpretedFunction):

    def __init__(self, sfs_instr, theta_value, var_initial_idx=0):
        super().__init__(sfs_instr, theta_value, var_initial_idx)
        self.commutative = False


    def encoding_instruction(self, **kwargs):
        o = self.input_stack[0]

        bs = kwargs["bs"]

        encoding_method = lambda j: pop_uninterpreted_encoding(j, bs, o, self.theta_value)

        return super().encoding_instruction(encoding_function=encoding_method, **kwargs)
