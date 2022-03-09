import unittest

from smt_encoding.complete_encoding.instruction_bounds import generate_lower_bound_dict, \
    generate_first_position_instr_cannot_appear, generate_dependency_graph
from smt_encoding.instructions.instruction_factory import InstructionFactory
from smt_encoding.instructions.encoding_instruction import InstructionSubset

class TestInstructionBounds(unittest.TestCase):

    def test_prev_instructions_repeated_dependency_graph(self):
        instruction_jsons = [
            {"id": 'INSTR_0', 'outpt_sk': ["s(0)"], 'inpt_sk': [5, 6], 'gas': 0, 'disasm': "a", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_1', 'outpt_sk': ["s(1)"], 'inpt_sk': [], 'gas': 0, 'disasm': "a", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_2', 'outpt_sk': ["s(2)"], 'inpt_sk': ["s(0)", 7, "s(1)"], 'gas': 0, 'disasm': "a", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_3', 'outpt_sk': ["s(3)"], 'inpt_sk': ["s(2)", 8, "s(2)"], 'gas': 0, 'disasm': "a", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_4', 'outpt_sk': ["s(4)"], 'inpt_sk': ["s(3)", "s(1)", "s(2)"], 'gas': 0, 'disasm': "a",
             'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
        ]
        factory = InstructionFactory()
        instructions = []
        for instr_json in instruction_jsons:
            instructions.append(factory.create_instruction_json_format(instr_json))

        stack_element_to_id = {"s(0)": "INSTR_0", "s(1)": "INSTR_1", "s(2)": "INSTR_2", "s(3)": "INSTR_3", "s(4)": "INSTR_4"}
        dependency_graph = generate_dependency_graph(instructions, [], stack_element_to_id)

        expected_dependency_graph = {'INSTR_4': ['INSTR_3', 'INSTR_1', 'INSTR_2'],
                            'INSTR_2': ['INSTR_0', 'PUSH', 'INSTR_1'],
                            'INSTR_0': ['PUSH', 'PUSH'], 'INSTR_1': [],
                            'INSTR_3': ['INSTR_2', 'PUSH', 'INSTR_2'], 'PUSH': []}
        self.assertDictEqual(dependency_graph, expected_dependency_graph)


    def test_order_tuples_dependency_graph(self):
        instruction_jsons = [
            {"id": 'INSTR_0', 'outpt_sk': ["s(0)"], 'inpt_sk': [5, 6], 'gas': 0, 'disasm': "a", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_1', 'outpt_sk': ["s(1)"], 'inpt_sk': [], 'gas': 0, 'disasm': "a", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_2', 'outpt_sk': ["s(2)"], 'inpt_sk': ["s(0)", 7, "s(1)"], 'gas': 0, 'disasm': "a", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_3', 'outpt_sk': ["s(3)"], 'inpt_sk': ["s(2)", 8, "s(2)"], 'gas': 0, 'disasm': "a", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_4', 'outpt_sk': ["s(4)"], 'inpt_sk': ["s(3)", "s(1)", "s(2)"], 'gas': 0, 'disasm': "a",
             'opcode': "a", 'size': 0, 'storage': False, 'commutative': False},

            {"id": 'INSTR_5', 'outpt_sk': [], 'inpt_sk': ["s(0)", 7], 'gas': 0, 'disasm': "a",
             'opcode': "a", 'size': 0, 'storage': True, 'commutative': False},
            {"id": 'INSTR_6', 'outpt_sk': [], 'inpt_sk': ["s(2)", "s(2)"], 'gas': 0, 'disasm': "a",
             'opcode': "a", 'size': 0, 'storage': True, 'commutative': False},
            {"id": 'INSTR_7', 'outpt_sk': [], 'inpt_sk': ["s(4)", "s(1)"], 'gas': 0, 'disasm': "a",
             'opcode': "a", 'size': 0, 'storage': True, 'commutative': False},
        ]
        factory = InstructionFactory()
        instructions = []
        for instr_json in instruction_jsons:
            instructions.append(factory.create_instruction_json_format(instr_json))

        stack_element_to_id = {"s(0)": "INSTR_0", "s(1)": "INSTR_1", "s(2)": "INSTR_2", "s(3)": "INSTR_3", "s(4)": "INSTR_4"}
        order_tuples = [('INSTR_5', 'INSTR_6'), ('INSTR_6', 'INSTR_7')]
        dependency_graph = generate_dependency_graph(instructions, order_tuples, stack_element_to_id)

        expected_dependency_graph = {'INSTR_4': ['INSTR_3', 'INSTR_1', 'INSTR_2'],
                            'INSTR_2': ['INSTR_0', 'PUSH', 'INSTR_1'],
                            'INSTR_0': ['PUSH', 'PUSH'], 'INSTR_1': [],
                            'INSTR_3': ['INSTR_2', 'PUSH', 'INSTR_2'],
                            'INSTR_5': ['INSTR_0', 'PUSH'],
                            'INSTR_6': ['INSTR_2', 'INSTR_2', 'INSTR_5'],
                            'INSTR_7': ['INSTR_4', 'INSTR_1', 'INSTR_6'],
                            'PUSH': []}
        self.assertDictEqual(dependency_graph, expected_dependency_graph)


    def test_prev_instructions_repeated_values(self):
        dependency_graph = {'INSTR_4': ['INSTR_3', 'INSTR_1', 'INSTR_2'],
                            'INSTR_2': ['INSTR_0', 'PUSH', 'INSTR_1'],
                            'INSTR_0': ['PUSH', 'PUSH'], 'INSTR_1': [],
                            'INSTR_3': ['INSTR_2', 'PUSH', 'INSTR_2'], 'PUSH': []}

        expected_output = {'INSTR_0': 2, 'INSTR_1': 0, 'INSTR_2': 5, 'INSTR_3': 8, 'INSTR_4': 11, 'PUSH': 0}
        output = generate_lower_bound_dict(dependency_graph)
        self.assertDictEqual(expected_output, output)

    def test_prev_instructions_several_maximal_elements(self):
        dependency_graph = {'INSTR_0': ['PUSH', 'PUSH'], 'INSTR_1': [],
                            'INSTR_2': ['INSTR_0', 'PUSH', 'INSTR_1'],
                            'INSTR_3': ['INSTR_2','PUSH', 'INSTR_2'],
                            'INSTR_4': ['INSTR_3', 'INSTR_1', 'INSTR_2'],
                            'INSTR_5': ['INSTR_3','INSTR_3', 'INSTR_2'],
                            'INSTR_6': ['INSTR_4', 'INSTR_5', 'INSTR_2'], 'PUSH': []}

        expected_output = {'INSTR_0': 2, 'INSTR_1': 0, 'INSTR_2': 5, 'INSTR_3': 8,
                           'INSTR_4': 11, 'INSTR_5': 11, 'INSTR_6': 17, 'PUSH': 0}
        output = generate_lower_bound_dict(dependency_graph)
        self.assertDictEqual(expected_output, output)


    def test_prev_instructions_several_dependencies(self):
        dependency_graph = {'INSTR_0': ['PUSH', 'PUSH'], 'INSTR_1': [],
                            'INSTR_2': ['INSTR_0', 'PUSH', 'INSTR_1'],
                            'INSTR_3': ['INSTR_2', 'PUSH', 'INSTR_2'],
                            'INSTR_4': ['INSTR_3', 'INSTR_1','INSTR_2'],
                            'INSTR_5': ['INSTR_3', 'INSTR_3', 'INSTR_2'],
                            'INSTR_6': ['INSTR_4', 'INSTR_5', 'INSTR_2'],
                            'INSTR_7': ['PUSH', 'PUSH', 'INSTR_2'], 'PUSH': []}

        expected_output = {'INSTR_0': 2, 'INSTR_1': 0, 'INSTR_2': 5, 'INSTR_3': 8,
                           'INSTR_4': 11, 'INSTR_5': 11, 'INSTR_6': 17, 'INSTR_7': 8, 'PUSH': 0}
        output = generate_lower_bound_dict(dependency_graph)
        self.assertDictEqual(expected_output, output)


    def test_first_position_cannot_appear_repeated_values(self):
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
             'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
        ]
        factory = InstructionFactory()
        instructions = []

        for instr_json in instruction_jsons:
            instructions.append(factory.create_instruction_json_format(instr_json))

        stack_element_to_id_dict = {instruction.output_stack: instruction.id
                                                     for instruction in instructions if
                                                     instruction.output_stack is not None}

        instr_by_id_dict = {instruction.id: instruction for instruction in
                                                               instructions}

        dependency_graph = generate_dependency_graph(instructions, [], stack_element_to_id_dict)

        b0 = 15

        final_stack_instr = ['s(2)', 's(4)', 's(0)']
        expected_output = {'INSTR_0': 10, 'INSTR_1': 9, 'INSTR_2': 11, 'INSTR_3': 13, 'INSTR_4': 14, 'PUSH': 15}
        output = generate_first_position_instr_cannot_appear(b0, stack_element_to_id_dict, final_stack_instr,
                                                             dependency_graph, [], instr_by_id_dict)

        self.assertDictEqual(expected_output, output)


    def test_first_position_cannot_appear_several_maximal_elements(self):
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
             'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_5', 'outpt_sk': ["s(5)"], 'inpt_sk': ["s(3)", "s(2)", "s(4)"], 'gas': 0, 'disasm': "a",
             'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_6', 'outpt_sk': ["s(6)"], 'inpt_sk': ["s(4)", "s(3)", "s(2)"], 'gas': 0, 'disasm': "a",
             'opcode': "a", 'size': 0, 'storage': False, 'commutative': False},
        ]
        factory = InstructionFactory()
        instructions = []

        for instr_json in instruction_jsons:
            instructions.append(factory.create_instruction_json_format(instr_json))

        stack_element_to_id_dict = {instruction.output_stack: instruction.id
                                    for instruction in instructions if
                                    instruction.output_stack is not None}

        instr_by_id_dict = {instruction.id: instruction for instruction in
                            instructions}

        dependency_graph = generate_dependency_graph(instructions, [], stack_element_to_id_dict)

        b0 = 17

        final_stack_instr = ['s(0)', 's(2)', 's(6)', 's(5)']
        expected_output = {'INSTR_0': 10, 'INSTR_1': 9, 'INSTR_2': 11, 'INSTR_3': 13, 'INSTR_4': 14, 'INSTR_5': 16,
                          'INSTR_6': 16, 'PUSH': 17}
        output = generate_first_position_instr_cannot_appear(b0, stack_element_to_id_dict, final_stack_instr,
                                                             dependency_graph, [], instr_by_id_dict)

        self.assertDictEqual(expected_output, output)


    def test_first_position_cannot_appear_several_commutative_operations(self):
        instruction_jsons = [
            {"id": 'INSTR_0', 'outpt_sk': ["s(0)"], 'inpt_sk': [5, 6], 'gas': 0, 'disasm': "a", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_1', 'outpt_sk': ["s(1)"], 'inpt_sk': [], 'gas': 0, 'disasm': "a", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_2', 'outpt_sk': ["s(2)"], 'inpt_sk': ["s(0)", 7, "s(1)"], 'gas': 0, 'disasm': "a",
             'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_3', 'outpt_sk': ["s(3)"], 'inpt_sk': ["s(1)", "s(2)"], 'gas': 0, 'disasm': "a",
             'opcode': "a", 'size': 0, 'storage': False, 'commutative': True},
            {"id": 'INSTR_4', 'outpt_sk': ["s(4)"], 'inpt_sk': ["s(3)", "s(1)", "s(2)"], 'gas': 0, 'disasm': "a",
             'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_5', 'outpt_sk': ["s(5)"], 'inpt_sk': ["s(3)", "s(4)"], 'gas': 0, 'disasm': "a",
             'opcode': "a",
             'size': 0, 'storage': False, 'commutative': True},
            {"id": 'INSTR_6', 'outpt_sk': ["s(6)"], 'inpt_sk': ["s(4)", "s(3)", "s(2)"], 'gas': 0, 'disasm': "a",
             'opcode': "a", 'size': 0, 'storage': False, 'commutative': False},
        ]
        factory = InstructionFactory()
        instructions = []

        for instr_json in instruction_jsons:
            instructions.append(factory.create_instruction_json_format(instr_json))

        stack_element_to_id_dict = {instruction.output_stack: instruction.id
                                    for instruction in instructions if
                                    instruction.output_stack is not None}

        instr_by_id_dict = {instruction.id: instruction for instruction in
                            instructions}

        dependency_graph = generate_dependency_graph(instructions, [], stack_element_to_id_dict)

        b0 = 17

        final_stack_instr = ['s(0)', 's(2)', 's(6)', 's(5)']
        expected_output = {'INSTR_0': 12, 'INSTR_1': 11, 'INSTR_2': 13, 'INSTR_3': 14, 'INSTR_4': 15, 'INSTR_5': 16,
                          'INSTR_6': 16, 'PUSH': 17}
        output = generate_first_position_instr_cannot_appear(b0, stack_element_to_id_dict, final_stack_instr,
                                                             dependency_graph, [], instr_by_id_dict)

        self.assertDictEqual(expected_output, output)


    def test_order_tuples_first_position_instruction_cannot_appear(self):
        instruction_jsons = [
            {"id": 'INSTR_0', 'outpt_sk': ["s(0)"], 'inpt_sk': [5, 6], 'gas': 0, 'disasm': "a", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_1', 'outpt_sk': ["s(1)"], 'inpt_sk': [], 'gas': 0, 'disasm': "a", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_2', 'outpt_sk': ["s(2)"], 'inpt_sk': ["s(0)", 7, "s(1)"], 'gas': 0, 'disasm': "a", 'opcode': "a",
             'size': 0, 'storage': False, 'commutative': False},
            {"id": 'INSTR_3', 'outpt_sk': ["s(3)"], 'inpt_sk': ["s(2)", 8, "s(2)"], 'gas': 0, 'disasm': "a", 'opcode': "a",
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

        stack_element_to_id_dict = {instruction.output_stack: instruction.id
                                    for instruction in instructions if
                                    instruction.output_stack is not None}

        instr_by_id_dict = {instruction.id: instruction for instruction in
                            instructions}

        order_tuples = [('INSTR_5', 'INSTR_6'), ('INSTR_6', 'INSTR_7')]

        mem_ids = [instruction.id for instruction in instructions if instruction.instruction_subset == InstructionSubset.store]

        dependency_graph = generate_dependency_graph(instructions, order_tuples, stack_element_to_id_dict)

        b0 = 17

        final_stack_instr = ['s(2)', 's(4)', 's(0)']


        expected_output = {'INSTR_0': 11, 'INSTR_1': 10, 'INSTR_2': 12, 'INSTR_3': 14, 'INSTR_4': 16, 'INSTR_5': 15,
                           'INSTR_6': 16, 'INSTR_7': 17,'PUSH': 17}

        output = generate_first_position_instr_cannot_appear(b0, stack_element_to_id_dict, final_stack_instr,
                                                             dependency_graph, mem_ids, instr_by_id_dict)

        self.assertDictEqual(expected_output, output)


if __name__ == '__main__':
    unittest.main()
