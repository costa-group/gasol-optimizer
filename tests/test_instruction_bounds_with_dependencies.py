import unittest

from smt_encoding.instructions.instruction_dependencies import generate_dependency_graph_minimum
from smt_encoding.instructions.instruction_bounds_with_dependencies import generate_lower_bound_dict, \
    generate_first_position_instr_cannot_appear, InstructionBoundsWithDependencies
from smt_encoding.instructions.instruction_factory import InstructionFactory
from smt_encoding.instructions.encoding_instruction import InstructionSubset


class TestInstructionBoundsWithDependencies(unittest.TestCase):

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
                            'INSTR_3': ['INSTR_2', 'PUSH', 'INSTR_2'],
                            'INSTR_4': ['INSTR_3', 'INSTR_1', 'INSTR_2'],
                            'INSTR_5': ['INSTR_3', 'INSTR_3', 'INSTR_2'],
                            'INSTR_6': ['INSTR_4', 'INSTR_5', 'INSTR_2'], 'PUSH': []}

        expected_output = {'INSTR_0': 2, 'INSTR_1': 0, 'INSTR_2': 5, 'INSTR_3': 8,
                           'INSTR_4': 11, 'INSTR_5': 11, 'INSTR_6': 17, 'PUSH': 0}
        output = generate_lower_bound_dict(dependency_graph)
        self.assertDictEqual(expected_output, output)

    def test_prev_instructions_several_dependencies(self):
        dependency_graph = {'INSTR_0': ['PUSH', 'PUSH'], 'INSTR_1': [],
                            'INSTR_2': ['INSTR_0', 'PUSH', 'INSTR_1'],
                            'INSTR_3': ['INSTR_2', 'PUSH', 'INSTR_2'],
                            'INSTR_4': ['INSTR_3', 'INSTR_1', 'INSTR_2'],
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

        dependency_graph = generate_dependency_graph_minimum(instructions, [], stack_element_to_id_dict)

        b0 = 15

        final_stack_instr = ['s(2)', 's(4)', 's(0)']
        expected_output = {'INSTR_0': 10, 'INSTR_1': 13, 'INSTR_2': 11, 'INSTR_3': 13, 'INSTR_4': 14, 'PUSH': 15}
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

        dependency_graph = generate_dependency_graph_minimum(instructions, [], stack_element_to_id_dict)

        b0 = 17

        final_stack_instr = ['s(0)', 's(2)', 's(6)', 's(5)']
        expected_output = {'INSTR_0': 10, 'INSTR_1': 14, 'INSTR_2': 11, 'INSTR_3': 13, 'INSTR_4': 14, 'INSTR_5': 16,
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

        dependency_graph = generate_dependency_graph_minimum(instructions, [], stack_element_to_id_dict)

        b0 = 17

        final_stack_instr = ['s(0)', 's(2)', 's(6)', 's(5)']
        expected_output = {'INSTR_0': 12, 'INSTR_1': 14, 'INSTR_2': 13, 'INSTR_3': 14, 'INSTR_4': 15, 'INSTR_5': 16,
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

        stack_element_to_id_dict = {instruction.output_stack: instruction.id
                                    for instruction in instructions if
                                    instruction.output_stack is not None}

        instr_by_id_dict = {instruction.id: instruction for instruction in
                            instructions}

        order_tuples = [('INSTR_5', 'INSTR_6'), ('INSTR_6', 'INSTR_7')]

        mem_ids = [instruction.id for instruction in instructions if
                   instruction.instruction_subset == InstructionSubset.store]

        dependency_graph = generate_dependency_graph_minimum(instructions, order_tuples, stack_element_to_id_dict)

        b0 = 17

        final_stack_instr = ['s(2)', 's(4)', 's(0)']

        expected_output = {'INSTR_0': 11, 'INSTR_1': 15, 'INSTR_2': 12, 'INSTR_3': 14, 'INSTR_4': 16, 'INSTR_5': 15,
                           'INSTR_6': 16, 'INSTR_7': 17, 'PUSH': 17}

        output = generate_first_position_instr_cannot_appear(b0, stack_element_to_id_dict, final_stack_instr,
                                                             dependency_graph, mem_ids, instr_by_id_dict)

        self.assertDictEqual(expected_output, output)

    def test_bound_object_is_well_generated(self):
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

        order_tuples = [('INSTR_5', 'INSTR_6'), ('INSTR_6', 'INSTR_7')]

        final_stack_instr = ['s(2)', 's(4)', 's(0)']

        b0 = 17

        ib = InstructionBoundsWithDependencies(instructions, order_tuples, final_stack_instr, b0, 5)

        expected_output = {0: 11, 1: 15, 2: 12, 3: 14, 4: 16, 5: 15, 6: 16, 7: 17}

        self.assertDictEqual(ib._first_position_not_instr_by_theta_value, expected_output)
        self.assertEqual(ib.first_position_sequence, 5)
        self.assertEqual(ib.last_position_sequence, 21)

    def test_lb_tight_dependencies(self):
        """
        Test for case in which the lower bounds are not correctly obtained. Shows previous approach fails when
        memory dependencies overlap instruction dependencies. We need to consider only those memory dependencies that
        has not been considered before (even indirectly)

        Original block: PUSH FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF AND
                        PUSH FFFFFFFFFFFFFFFFFFFFFFFF0000000000000000000000000000000000000000
                        PUSH 0 SLOAD AND OR PUSH 0 SSTORE

        Explanation: we have the dependency (SLOAD, SSTORE), so we would add SLOAD to the dependency graph of SSTORE.
        However, OR also happens before SSTORE, and SLOAD must happen before OR, so SLOAD is considered twice when obtaining
        the bounds. Thus, the lb of SSTORE is 9, whereas it should be at most 8 according to the example.

        Solution: don't include SLOAD as a direct dependency of SSTORE, as it is already dependent
        """
        instruction_jsons = [
            {'id': 'SSTORE_0', 'opcode': '55', 'disasm': 'SSTORE', 'inpt_sk': ['s(5)', 's(1)'], 'sto_var': ['sto0'],
             'outpt_sk': [], 'gas': 5000, 'commutative': False, 'storage': True, 'size': 1},
            {'id': 'AND_1', 'opcode': '16', 'disasm': 'AND', 'inpt_sk': ['s(6)', 's(0)'], 'outpt_sk': ['s(4)'],
             'gas': 3,
             'commutative': True, 'storage': False, 'size': 1},
            {'id': 'SLOAD_0', 'opcode': '54', 'disasm': 'SLOAD', 'inpt_sk': ['s(5)'], 'outpt_sk': ['s(3)'], 'gas': 700,
             'commutative': False, 'storage': False, 'size': 1},
            {'id': 'AND_0', 'opcode': '16', 'disasm': 'AND', 'inpt_sk': ['s(3)', 's(7)'], 'outpt_sk': ['s(2)'],
             'gas': 3,
             'commutative': True, 'storage': False, 'size': 1},
            {'id': 'OR_0', 'opcode': '17', 'disasm': 'OR', 'inpt_sk': ['s(2)', 's(4)'], 'outpt_sk': ['s(1)'], 'gas': 3,
             'commutative': True, 'storage': False, 'size': 1},
            {'id': 'PUSH_0', 'opcode': '60', 'disasm': 'PUSH', 'inpt_sk': [], 'value': [0], 'outpt_sk': ['s(5)'],
             'gas': 3,
             'commutative': False, 'storage': False, 'size': 2},
            {'id': 'PUSH_1', 'opcode': '60', 'disasm': 'PUSH', 'inpt_sk': [],
             'value': [1461501637330902918203684832716283019655932542975], 'outpt_sk': ['s(6)'], 'gas': 3,
             'commutative': False, 'storage': False, 'size': 21},
            {'id': 'PUSH_2', 'opcode': '60', 'disasm': 'PUSH', 'inpt_sk': [],
             'value': [115792089237316195423570985007226406215939081747436879206741300988257197096960],
             'outpt_sk': ['s(7)'], 'gas': 3, 'commutative': False, 'storage': False, 'size': 33}]

        factory = InstructionFactory()
        instructions = []
        sstore_theta_value = -1
        for instr_json in instruction_jsons:
            instr = factory.create_instruction_json_format(instr_json)
            instructions.append(instr)

            if instr_json['id'] == 'SSTORE_0':
                sstore_theta_value = instr.theta_value

        order_tuples = [('SLOAD_0', 'SSTORE_0')]

        final_stack_instr = []

        b0 = 9

        ib = InstructionBoundsWithDependencies(instructions, order_tuples, final_stack_instr, b0, 5)

        # Check SSTORE instruction can appear in the sequence
        self.assertLess(ib.lower_bound_theta_value(sstore_theta_value), b0)


if __name__ == '__main__':
    unittest.main()
