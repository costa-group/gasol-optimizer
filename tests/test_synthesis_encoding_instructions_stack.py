import unittest
from smt_encoding.complete_encoding.synthesis_encoding_instructions_stack import EncodingForStack
from smt_encoding.complete_encoding.synthesis_stack_constraints import push_basic_encoding, pop_uninterpreted_encoding, \
    non_comm_function_encoding
from smt_encoding.instructions.push_basic import PushBasic
from smt_encoding.instructions.pop_uninterpreted import PopUninterpreted
from smt_encoding.complete_encoding.synthesis_functions import SynthesisFunctions
from smt_encoding.instructions.instruction_bounds_simple import DumbInstructionBounds
from smt_encoding.constraints.connector_factory import add_eq, add_and, add_implies, add_leq, add_lt, add_not
from smt_encoding.complete_encoding.synthesis_predicates import move
from smt_encoding.constraints.assertions import AssertHard
from smt_encoding.instructions.non_comm_uninterpreted import NonCommutativeUninterpreted
from smt_encoding.constraints.function import Function, Sort


class TestSynthesisConstraints(unittest.TestCase):

    def test_number_of_hard_constraints(self):
        push_basic = PushBasic(0)

        encoding_factory = EncodingForStack()
        encoding_factory.register_function_for_encoding(push_basic, push_basic_encoding)

        bounds = DumbInstructionBounds(5, 9)
        sf = SynthesisFunctions(dict())
        hard_constraints = encoding_factory.encode_instruction(push_basic, bounds, sf, 2)
        self.assertEqual(len(hard_constraints), 5)

    def test_push_basic_encoding(self):
        push_basic = PushBasic(0)

        encoding_factory = EncodingForStack()
        encoding_factory.register_function_for_encoding(push_basic, push_basic_encoding)

        bounds = DumbInstructionBounds(1, 2)
        sf = SynthesisFunctions(dict())
        hard_constraints = encoding_factory.encode_instruction(push_basic, bounds, sf, 2)

        other_sf = SynthesisFunctions(dict())
        expected_hard_constraints = [AssertHard(add_implies(add_eq(other_sf.t(1), 0),
                                                            add_and(add_leq(0, other_sf.a(1)),
                                                                    add_lt(other_sf.a(1), 2 ** 256),
                                                                    add_not(other_sf.u(1, 1)), other_sf.u(0, 2),
                                                                    add_eq(other_sf.x(0, 2), other_sf.a(1)),
                                                                    move(other_sf, 1, 0, 0, 1)))),
                                     AssertHard(add_implies(add_eq(other_sf.t(2), 0),
                                                            add_and(add_leq(0, other_sf.a(2)),
                                                                    add_lt(other_sf.a(2), 2 ** 256),
                                                                    add_not(other_sf.u(1, 2)), other_sf.u(0, 3),
                                                                    add_eq(other_sf.x(0, 3), other_sf.a(2)),
                                                                    move(other_sf, 2, 0, 0, 1))))]
        self.assertListEqual(hard_constraints, expected_hard_constraints)

    def test_pop_uninterpreted_encoding(self):
        pop_sms = {'outpt_sk': [], 'inpt_sk': ["s_1"], 'gas': 2, 'disasm': "POP",
                   'opcode': "50", 'id': "POP_0", 'size': 1}
        theta_value = 4
        pop_function = PopUninterpreted(pop_sms, theta_value)

        encoding_factory = EncodingForStack()
        encoding_factory.register_function_for_encoding(pop_function, pop_uninterpreted_encoding)

        bounds = DumbInstructionBounds(4, 4)
        sf = SynthesisFunctions({"s_1": Function('ex', Sort.integer)()})

        hard_constraints = encoding_factory.encode_instruction(pop_function, bounds, sf, 5, o0=pop_function.input_stack[0])
        other_sf = SynthesisFunctions({"s_1": Function('ex', Sort.integer)()})

        expected_hard_constraints = [AssertHard(add_implies(add_eq(other_sf.t(4), theta_value),
                                                            add_and(other_sf.u(0, 4), add_eq(other_sf.x(0, 4),
                                                                                             other_sf.stack_var("s_1")),
                                                                    add_not(other_sf.u(4, 5)),
                                                                    move(other_sf, 4, 1, 4, -1))))]
        self.assertListEqual(hard_constraints, expected_hard_constraints)
        self.assertListEqual(sf.created_expressions(), other_sf.created_expressions())
        self.assertListEqual(sf.created_functions(), other_sf.created_functions())

    def test_push_uninterpreted_encoding(self):
        push_sms = {'outpt_sk': ["s_2"], 'inpt_sk': [], 'gas': 3, 'disasm': "PUSH",
                    'opcode': "60", 'id': "PUSH_4", 'size': 1}
        theta_value = 7
        push_uninterpreted = NonCommutativeUninterpreted(push_sms, theta_value)

        encoding_factory = EncodingForStack()
        encoding_factory.register_function_for_encoding(push_uninterpreted, non_comm_function_encoding)

        bounds = DumbInstructionBounds(5, 5)
        sf = SynthesisFunctions({"s_2": 0})

        hard_constraints = encoding_factory.encode_instruction(push_uninterpreted, bounds, sf, 1,
                                                               o=push_uninterpreted.input_stack,
                                                               r=push_uninterpreted.output_stack)

        other_sf = SynthesisFunctions({"s_2": 0})
        expected_hard_constraints = [AssertHard(add_implies(add_eq(other_sf.t(5), theta_value),
                                                            add_and(add_not(other_sf.u(0, 5)),
                                                                    other_sf.u(0, 6),
                                                                    add_eq(other_sf.x(0, 6), other_sf.stack_var('s_2')),
                                                                    move(other_sf, 5, 0, -1, 1))))]

        self.assertListEqual(hard_constraints, expected_hard_constraints)
        self.assertListEqual(sf.created_expressions(), other_sf.created_expressions())
        self.assertListEqual(sf.created_functions(), other_sf.created_functions())



if __name__ == '__main__':
    unittest.main()
