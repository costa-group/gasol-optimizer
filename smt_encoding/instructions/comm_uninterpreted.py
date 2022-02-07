from smt_encoding.instructions.uninterpreted_instruction import UninterpretedFunction, SMS_T
from smt_encoding.constraints.assertions import Assert
from smt_encoding.constraints.connector_factory import add_eq, add_and, add_implies, add_not, add_or
from smt_encoding.complete_encoding.synthesis_variables import u, x, t
from smt_encoding.complete_encoding.synthesis_predicates import move
from smt_encoding.instructions.encoding_instruction import InstructionSubset


def comm_function_encoding(j : int, bs : int, o0 : str, o1 : str, r : str, theta_f : int):
    left_term = add_eq(t(j), theta_f)
    right_term = add_and(u(0,j), u(1,j), add_or(add_and(add_eq(x(0,j), o0), add_eq(x(1,j), o1)),
                                                  add_and(add_eq(x(0,j), o1), add_eq(x(1,j), o0))),
                          u(0,j+1), add_eq(x(0,j+1), r), move(j, 2, bs-1, -1), add_not(u(bs-1, j+1)))
    return Assert(add_implies(left_term, right_term))


class CommutativeUninterpreted(UninterpretedFunction):

    def __init__(self, sfs_instr : SMS_T, theta_value : int, var_initial_idx : int = 0):
        super().__init__(sfs_instr, theta_value, var_initial_idx)
        self.commutative = True


    def encoding_instruction(self, **kwargs):

        o0 = self.input_stack[0]
        o1 = self.input_stack[1]
        r = self.output_stack[0]
        bs = kwargs["bs"]
        j = kwargs["j"]

        return comm_function_encoding(j, bs, o0, o1, r, self.theta_value)

    # Statement it belongs to basic instructions
    @property
    def instruction_subset(self) -> InstructionSubset:
        return InstructionSubset.comm
