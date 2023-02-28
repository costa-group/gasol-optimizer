import unittest
from smt_encoding.complete_encoding.synthesis_initialize_variables import stack_encoding_for_position
from smt_encoding.complete_encoding.synthesis_opcode_term_creation import UninterpretedOpcodeTermCreation
from smt_encoding.instructions.instruction_factory import InstructionFactory
from smt_encoding.constraints.function import Function, Sort
from smt_encoding.complete_encoding.synthesis_functions import SynthesisFunctions
from smt_encoding.constraints.connector_factory import add_eq, add_and, add_implies, add_leq, add_lt, add_not
from smt_encoding.constraints.assertions import AssertHard


class TestStackEncodingInPosition(unittest.TestCase):

    def test_full_example_with_int(self):
        instruction_jsons = [
            {"id": 'INSTR_0', 'outpt_sk': ["s(0)"], 'inpt_sk': [5, 6], 'gas': 0, 'disasm': "ADD", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_1', 'outpt_sk': ["s(1)"], 'inpt_sk': [], 'gas': 0, 'disasm': "PUSH [$]", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': True},
            {"id": 'INSTR_2', 'outpt_sk': ["s(2)"], 'inpt_sk': ["s(0)", 7, "s(1)"], 'gas': 0, 'disasm': "PUSH #[$]",
             'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_3', 'outpt_sk': ["s(3)"], 'inpt_sk': ["s(2)", 8, "s(2)"], 'gas': 0, 'disasm': "SUB",
             'opcode': "a",
             'size': 0, 'storage': False, 'commutative': True},
            {"id": 'INSTR_4', 'outpt_sk': ["s(4)"], 'inpt_sk': ["s(3)", "s(1)", "s(2)"], 'gas': 0, 'disasm': "ADDMOD",
             'opcode': "a", 'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_5', 'outpt_sk': [], 'inpt_sk': ["s(0)", "s(2)"], 'gas': 0, 'disasm': "a",
             'opcode': "a", 'size': 0, 'storage': True, 'commutative': False},
            {"id": 'INSTR_6', 'outpt_sk': [], 'inpt_sk': ["s(2)", "s(3)"], 'gas': 0, 'disasm': "a",
             'opcode': "a", 'size': 0, 'storage': True, 'commutative': False},
            {"id": 'INSTR_7', 'outpt_sk': [], 'inpt_sk': ["s(4)", "s(1)"], 'gas': 0, 'disasm': "a",
             'opcode': "a", 'size': 0, 'storage': True, 'commutative': False},
        ]

        factory = InstructionFactory()
        instructions = []
        for instr_json in instruction_jsons:
            instructions.append(factory.create_instruction_json_format(instr_json))

        initial_stack = ["s(8)", "s(10)"]
        final_stack = ["s(10)", "s(2)", 50, 10, "s(4)", "s(2)"]

        uop_creation = UninterpretedOpcodeTermCreation(instructions, initial_stack, Sort.integer)
        term_to_function, _ = uop_creation.opcode_rep_with_uf()
        sf = SynthesisFunctions(term_to_function, Sort.integer)

        stack_var_to_term, _ = uop_creation.opcode_rep_with_stack_vars()

        add_f = Function('add', Sort.integer, Sort.integer, Sort.integer)
        push_1_f = Function('push[$]', Sort.integer)
        push_2_f = Function('push#[$]', Sort.integer, Sort.integer, Sort.integer, Sort.integer)
        sub_f = Function('sub', Sort.integer, Sort.integer, Sort.integer, Sort.integer)
        addmod_f = Function('addmod', Sort.integer, Sort.integer, Sort.integer, Sort.integer)

        instr_0 = add_f(5, 6)
        instr_1 = push_1_f()
        instr_2 = push_2_f(instr_0, 7, instr_1)
        instr_3 = sub_f(instr_2, 8, instr_2)
        instr_4 = addmod_f(instr_3, instr_1, instr_2)
        # s_8_expr = Function('s_0', Sort.integer)()
        s_10_expr = Function('s_1', Sort.integer)()

        generated_constraints = stack_encoding_for_position(7, sf, final_stack, 7)

        obtained_constraints = [AssertHard(add_and(Function('u_0_7', Sort.boolean)(),
                                                   add_eq(Function('x_0_7', Sort.integer)(), s_10_expr))),
                                AssertHard(add_and(Function('u_1_7', Sort.boolean)(),
                                                   add_eq(Function('x_1_7', Sort.integer)(), instr_2))),
                                AssertHard(add_and(Function('u_2_7', Sort.boolean)(),
                                                   add_eq(Function('x_2_7', Sort.integer)(), 50))),
                                AssertHard(add_and(Function('u_3_7', Sort.boolean)(),
                                                   add_eq(Function('x_3_7', Sort.integer)(), 10))),
                                AssertHard(add_and(Function('u_4_7', Sort.boolean)(),
                                                   add_eq(Function('x_4_7', Sort.integer)(), instr_4))),
                                AssertHard(add_and(Function('u_5_7', Sort.boolean)(),
                                                   add_eq(Function('x_5_7', Sort.integer)(), instr_2))),
                                AssertHard(add_not(Function('u_6_7', Sort.boolean)()))]

        self.assertListEqual(generated_constraints, obtained_constraints)

    def test_full_example_with_uf(self):
        instruction_jsons = [
            {"id": 'INSTR_0', 'outpt_sk': ["s(0)"], 'inpt_sk': ["s(1)", "s(1)"], 'gas': 0, 'disasm': "ADD", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_1', 'outpt_sk': ["s(1)"], 'inpt_sk': [], 'gas': 0, 'disasm': "PUSH [$]", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': True},
            {"id": 'INSTR_2', 'outpt_sk': ["s(2)"], 'inpt_sk': ["s(0)", "s(0)", "s(1)"], 'gas': 0, 'disasm': "PUSH #[$]",
             'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_3', 'outpt_sk': ["s(3)"], 'inpt_sk': ["s(2)", "s(1)", "s(2)"], 'gas': 0, 'disasm': "SUB",
             'opcode': "a",
             'size': 0, 'storage': False, 'commutative': True},
            {"id": 'INSTR_4', 'outpt_sk': ["s(4)"], 'inpt_sk': ["s(3)", "s(1)", "s(2)"], 'gas': 0, 'disasm': "ADDMOD",
             'opcode': "a", 'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_5', 'outpt_sk': [], 'inpt_sk': ["s(0)", "s(2)"], 'gas': 0, 'disasm': "a",
             'opcode': "a", 'size': 0, 'storage': True, 'commutative': False},
            {"id": 'INSTR_6', 'outpt_sk': [], 'inpt_sk': ["s(2)", "s(3)"], 'gas': 0, 'disasm': "a",
             'opcode': "a", 'size': 0, 'storage': True, 'commutative': False},
            {"id": 'INSTR_7', 'outpt_sk': [], 'inpt_sk': ["s(4)", "s(1)"], 'gas': 0, 'disasm': "a",
             'opcode': "a", 'size': 0, 'storage': True, 'commutative': False},
        ]

        factory = InstructionFactory()
        instructions = []
        for instr_json in instruction_jsons:
            instructions.append(factory.create_instruction_json_format(instr_json))

        initial_stack = ["s(8)", "s(10)"]
        final_stack = ["s(10)", "s(2)", "s(10)", "s(8)", "s(4)", "s(2)"]

        uop_creation = UninterpretedOpcodeTermCreation(instructions, initial_stack, Sort.uninterpreted)
        term_to_function, _ = uop_creation.opcode_rep_with_uf()
        sf = SynthesisFunctions(term_to_function, Sort.uninterpreted)

        stack_var_to_term, _ = uop_creation.opcode_rep_with_stack_vars()

        add_f = Function('add', Sort.uninterpreted, Sort.uninterpreted, Sort.uninterpreted)
        push_1_f = Function('push[$]', Sort.uninterpreted)
        push_2_f = Function('push#[$]', Sort.uninterpreted, Sort.uninterpreted, Sort.uninterpreted, Sort.uninterpreted)
        sub_f = Function('sub', Sort.uninterpreted, Sort.uninterpreted, Sort.uninterpreted, Sort.uninterpreted)
        addmod_f = Function('addmod', Sort.uninterpreted, Sort.uninterpreted, Sort.uninterpreted, Sort.uninterpreted)

        instr_1 = push_1_f()
        instr_0 = add_f(instr_1, instr_1)
        instr_2 = push_2_f(instr_0, instr_0, instr_1)
        instr_3 = sub_f(instr_2, instr_1, instr_2)
        instr_4 = addmod_f(instr_3, instr_1, instr_2)
        s_8_expr = Function('s_0', Sort.uninterpreted)()
        s_10_expr = Function('s_1', Sort.uninterpreted)()

        generated_constraints = stack_encoding_for_position(7, sf, final_stack, 7)

        obtained_constraints = [AssertHard(add_and(Function('u_0_7', Sort.boolean)(),
                                                   add_eq(Function('x_0_7', Sort.uninterpreted)(), s_10_expr))),
                                AssertHard(add_and(Function('u_1_7', Sort.boolean)(),
                                                   add_eq(Function('x_1_7', Sort.uninterpreted)(), instr_2))),
                                AssertHard(add_and(Function('u_2_7', Sort.boolean)(),
                                                   add_eq(Function('x_2_7', Sort.uninterpreted)(), s_10_expr))),
                                AssertHard(add_and(Function('u_3_7', Sort.boolean)(),
                                                   add_eq(Function('x_3_7', Sort.uninterpreted)(), s_8_expr))),
                                AssertHard(add_and(Function('u_4_7', Sort.boolean)(),
                                                   add_eq(Function('x_4_7', Sort.uninterpreted)(), instr_4))),
                                AssertHard(add_and(Function('u_5_7', Sort.boolean)(),
                                                   add_eq(Function('x_5_7', Sort.uninterpreted)(), instr_2))),
                                AssertHard(add_not(Function('u_6_7', Sort.boolean)()))]

        self.assertListEqual(generated_constraints, obtained_constraints)


if __name__ == '__main__':
    unittest.main()
