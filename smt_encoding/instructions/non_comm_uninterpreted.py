from smt_encoding.instructions.uninterpreted_instruction import UninterpretedFunction

def non_comm_function_encoding(j : int, bs : int, o : str, r : str, theta_f : int):
    n = len(o)
    left_term = add_eq(t(j), theta_f)
    right_term_first_and = ["true"]
    # Second and can be empty, so we initialize terms to true value
    right_term_second_and = ["true"]
    right_term_third_and = ["true"]
    for i in range(0, n):
        right_term_first_and.append(add_and(u(i,j), add_eq(x(i,j), o[i])))
    for i in range(bs-n+1, bs):
        right_term_second_and.append(add_not(u(i, j+1)))
    for i in range(bs+n-1, bs):
        right_term_third_and.append(add_not(u(i, j)))
    right_term = add_and(add_and(*right_term_first_and), u(0, j+1) , add_eq(x(0,j+1), r),
                          move(j, n, min(bs-2+n, bs-1), 1-n) , add_and(*right_term_second_and),
                         add_and(*right_term_third_and))
    return add_assert(add_implies(left_term, right_term))

class NonCommutativeUninterpreted(UninterpretedFunction):

    def __init__(self, sfs_instr, theta_value, var_initial_idx=0):
        super().__init__(sfs_instr, theta_value, var_initial_idx)


    def encoding_instruction(self, **kwargs):
        o = self.input_stack
        r = self.output_stack[0]

        bs = kwargs["bs"]
        j = kwargs["j"]

        return non_comm_function_encoding(j, bs, o, r, self.theta_value)


    # Statement it belongs to basic instructions
    @property
    def instruction_subset(self):
        return "Non-Commutative"
