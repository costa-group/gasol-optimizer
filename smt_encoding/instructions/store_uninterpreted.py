from smt_encoding.encoding_stack_instructions import \
    store_stack_function_encoding
from smt_encoding.instructions.uninterpreted_instruction import UninterpretedFunction


class StoreUninterpreted(UninterpretedFunction):

    def __init__(self, sfs_instr, theta_value, var_initial_idx=0):
        super().__init__(sfs_instr, theta_value, var_initial_idx)


    def encoding_instruction(self, **kwargs):
        o0 = self.input_stack[0]
        o1 = self.input_stack[1]

        bs = kwargs["bs"]

        encoding_method = lambda j: store_stack_function_encoding(j, bs, o0, o1, self.theta_value)

        return super().encoding_instruction(encoding_function=encoding_method, **kwargs)
