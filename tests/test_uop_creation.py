import unittest
from smt_encoding.complete_encoding.synthesis_opcode_term_creation import UninterpretedOpcodeTermCreation
from smt_encoding.instructions.instruction_factory import InstructionFactory
from smt_encoding.constraints.function import Function, Sort


class MyTestCase(unittest.TestCase):

    def test_empty_instructions_creation(self):
        uop_creation = UninterpretedOpcodeTermCreation([], [])
        self.assertTupleEqual(uop_creation.opcode_rep_with_int(), (dict(), []))
        self.assertTupleEqual(uop_creation.opcode_rep_with_uf(), (dict(), []))
        self.assertTupleEqual(uop_creation.opcode_rep_with_stack_vars(), (dict(), []))

    def test_uop_creation_with_int_zero(self):
        instruction_jsons = [
            {"id": 'INSTR_0', 'outpt_sk': ["s(0)"], 'inpt_sk': [5, 6], 'gas': 0, 'disasm': "a", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_1', 'outpt_sk': ["s(1)"], 'inpt_sk': [], 'gas': 0, 'disasm': "a", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_2', 'outpt_sk': ["s(2)"], 'inpt_sk': ["s(0)", 7, "s(1)"], 'gas': 0, 'disasm': "a",
             'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_3', 'outpt_sk': ["s(3)"], 'inpt_sk': ["s(2)", 8, "s(2)"], 'gas': 0, 'disasm': "a",
             'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_4', 'outpt_sk': ["s(4)"], 'inpt_sk': ["s(3)", "s(1)", "s(2)"], 'gas': 0, 'disasm': "a",
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
        uop_creation = UninterpretedOpcodeTermCreation(instructions, [])
        created_dict, created_functions = uop_creation.opcode_rep_with_int()

        expected_dict = {'s(0)': 0, 's(1)': 1, 's(2)': 2, 's(3)': 3, 's(4)': 4}

        expected_functions = []
        self.assertDictEqual(created_dict, expected_dict)
        self.assertListEqual(created_functions, expected_functions)

    def test_uop_creation_with_uf_empty(self):
        instruction_jsons = [
            {"id": 'INSTR_0', 'outpt_sk': ["s(0)"], 'inpt_sk': [5, 6], 'gas': 0, 'disasm': "ADD", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_1', 'outpt_sk': ["s(1)"], 'inpt_sk': [], 'gas': 0, 'disasm': "PUSH [$]", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': True},
            {"id": 'INSTR_2', 'outpt_sk': ["s(2)"], 'inpt_sk': ["s(0)", 7, "s(1)"], 'gas': 0, 'disasm': "triple",
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
        uop_creation = UninterpretedOpcodeTermCreation(instructions, [], True, Sort.integer)
        created_dict, created_functions = uop_creation.opcode_rep_with_uf()

        empty = Function('empty', Sort.integer)
        add_f = Function('ADD', Sort.integer, Sort.integer, Sort.integer)
        push_1_f = Function('INSTR_1', Sort.integer)
        push_2_f = Function('TRIPLE', Sort.integer, Sort.integer, Sort.integer, Sort.integer)
        sub_f = Function('SUB', Sort.integer, Sort.integer, Sort.integer, Sort.integer)
        addmod_f = Function('ADDMOD', Sort.integer, Sort.integer, Sort.integer, Sort.integer)

        instr_0 = add_f(5, 6)
        instr_1 = push_1_f()
        instr_2 = push_2_f(instr_0, 7, instr_1)
        instr_3 = sub_f(instr_2, 8, instr_2)
        instr_4 = addmod_f(instr_3, instr_1, instr_2)

        expected_dict = {'empty': empty(), 's(0)': instr_0, 's(1)': instr_1, 's(2)': instr_2,
                         's(3)': instr_3, 's(4)': instr_4}

        expected_functions = [add_f, push_1_f, push_2_f, sub_f, addmod_f, empty]

        self.assertDictEqual(created_dict, expected_dict)
        self.assertListEqual(created_functions, expected_functions)

    def test_uop_creation_with_uf_different_sort(self):
        instruction_jsons = [
            {"id": 'INSTR_0', 'outpt_sk': ["s(0)"], 'inpt_sk': [], 'gas': 0, 'disasm': "PUSH", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_1', 'outpt_sk': ["s(1)"], 'inpt_sk': [], 'gas': 0, 'disasm': "PUSH [$]", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': True},
            {"id": 'INSTR_2', 'outpt_sk': ["s(2)"], 'inpt_sk': ["s(0)", "s(0)", "s(1)"], 'gas': 0, 'disasm': "PUSH #[$]",
             'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_3', 'outpt_sk': ["s(3)"], 'inpt_sk': ["s(2)", "s(0)", "s(2)"], 'gas': 0, 'disasm': "SUB",
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

        uop_creation = UninterpretedOpcodeTermCreation(instructions, [], False, Sort.uninterpreted)
        created_dict, created_functions = uop_creation.opcode_rep_with_uf()

        push_ini = Function('INSTR_0', Sort.uninterpreted)
        push_1_f = Function('INSTR_1', Sort.uninterpreted)
        push_2_f = Function('PUSHSUBSIZE', Sort.uninterpreted, Sort.uninterpreted, Sort.uninterpreted, Sort.uninterpreted)
        sub_f = Function('SUB', Sort.uninterpreted, Sort.uninterpreted, Sort.uninterpreted, Sort.uninterpreted)
        addmod_f = Function('ADDMOD', Sort.uninterpreted, Sort.uninterpreted, Sort.uninterpreted, Sort.uninterpreted)

        instr_0 = push_ini()
        instr_1 = push_1_f()
        instr_2 = push_2_f(instr_0, instr_0, instr_1)
        instr_3 = sub_f(instr_2, instr_0, instr_2)
        instr_4 = addmod_f(instr_3, instr_1, instr_2)

        expected_dict = {'s(0)': instr_0, 's(1)': instr_1, 's(2)': instr_2, 's(3)': instr_3, 's(4)': instr_4}

        expected_functions = [push_ini, push_1_f, push_2_f, sub_f, addmod_f]
        self.assertDictEqual(created_dict, expected_dict)
        self.assertListEqual(created_functions, expected_functions)

    def test_uop_creation_with_stack_vars(self):
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
        uop_creation = UninterpretedOpcodeTermCreation(instructions, [])
        created_dict, created_functions = uop_creation.opcode_rep_with_stack_vars()

        s_0_f = Function('s_0', Sort.integer)
        s_1_f = Function('s_1', Sort.integer)
        s_2_f = Function('s_2', Sort.integer)
        s_3_f = Function('s_3', Sort.integer)
        s_4_f = Function('s_4', Sort.integer)

        expected_dict = {'s(0)': s_0_f(), 's(1)': s_1_f(), 's(2)': s_2_f(), 's(3)': s_3_f(), 's(4)': s_4_f()}

        expected_functions = [s_0_f, s_1_f, s_2_f, s_3_f, s_4_f]
        self.assertDictEqual(created_dict, expected_dict)
        self.assertListEqual(created_functions, expected_functions)

    def test_uf_different_sort_initial_stack(self):
        instruction_jsons = [
            {"id": 'INSTR_0', 'outpt_sk': ["s(0)"], 'inpt_sk': [], 'gas': 0, 'disasm': "PUSH", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_1', 'outpt_sk': ["s(1)"], 'inpt_sk': [], 'gas': 0, 'disasm': "PUSH [$]", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': True},
            {"id": 'INSTR_2', 'outpt_sk': ["s(2)"], 'inpt_sk': ["s(0)", "s(0)", "s(1)"], 'gas': 0, 'disasm': "triple",
             'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_3', 'outpt_sk': ["s(3)"], 'inpt_sk': ["s(2)", "s(0)", "s(2)"], 'gas': 0, 'disasm': "SUB",
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

        uop_creation = UninterpretedOpcodeTermCreation(instructions, ["s(5)", "s(6)"], False, Sort.uninterpreted)
        created_dict, created_functions = uop_creation.opcode_rep_with_uf()

        push_ini = Function('INSTR_0', Sort.uninterpreted)
        push_1_f = Function('INSTR_1', Sort.uninterpreted)
        push_2_f = Function('TRIPLE', Sort.uninterpreted, Sort.uninterpreted, Sort.uninterpreted, Sort.uninterpreted)
        sub_f = Function('SUB', Sort.uninterpreted, Sort.uninterpreted, Sort.uninterpreted, Sort.uninterpreted)
        addmod_f = Function('ADDMOD', Sort.uninterpreted, Sort.uninterpreted, Sort.uninterpreted, Sort.uninterpreted)
        s_5 = Function('s_0', Sort.uninterpreted)
        s_6 = Function('s_1', Sort.uninterpreted)

        instr_0 = push_ini()
        instr_1 = push_1_f()
        instr_2 = push_2_f(instr_0, instr_0, instr_1)
        instr_3 = sub_f(instr_2, instr_0, instr_2)
        instr_4 = addmod_f(instr_3, instr_1, instr_2)
        instr_5 = s_5()
        instr_6 = s_6()

        expected_dict = {'s(0)': instr_0, 's(1)': instr_1, 's(2)': instr_2, 's(3)': instr_3,
                         's(4)': instr_4, 's(5)': instr_5, 's(6)': instr_6}

        expected_functions = [s_5, s_6, push_ini, push_1_f, push_2_f, sub_f, addmod_f]
        self.assertDictEqual(created_dict, expected_dict)
        self.assertListEqual(created_functions, expected_functions)

    def test_stack_vars_initial_stack(self):
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
            {"id": 'INSTR_4', 'outpt_sk': ["s(4)"], 'inpt_sk': ["s(3)", "s(1)", "s(2)"], 'gas': 0,
             'disasm': "ADDMOD",
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
        uop_creation = UninterpretedOpcodeTermCreation(instructions, ["s(8)", "s(10)"])
        created_dict, created_functions = uop_creation.opcode_rep_with_stack_vars()

        # Functions in initial stack
        s_8_f = Function('s_0', Sort.integer)
        s_10_f = Function('s_1', Sort.integer)

        # Functions from uninterpreted operations
        s_0_f = Function('s_2', Sort.integer)
        s_1_f = Function('s_3', Sort.integer)
        s_2_f = Function('s_4', Sort.integer)
        s_3_f = Function('s_5', Sort.integer)
        s_4_f = Function('s_6', Sort.integer)

        expected_dict = {'s(0)': s_0_f(), 's(1)': s_1_f(), 's(2)': s_2_f(), 's(3)': s_3_f(), 's(4)': s_4_f(),
                         's(8)': s_8_f(), 's(10)': s_10_f()}

        expected_functions = [s_8_f, s_10_f, s_0_f, s_1_f, s_2_f, s_3_f, s_4_f]

        self.assertDictEqual(created_dict, expected_dict)
        self.assertListEqual(created_functions, expected_functions)


if __name__ == '__main__':
    unittest.main()
