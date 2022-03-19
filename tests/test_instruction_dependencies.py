import unittest

from smt_encoding.instructions.instruction_dependencies import generate_dependency_graph_minimum
from smt_encoding.instructions.instruction_factory import InstructionFactory

class TestInstructionBoundsWithDependencies(unittest.TestCase):




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
        dependency_graph = generate_dependency_graph_minimum(instructions, [], stack_element_to_id)

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
        dependency_graph = generate_dependency_graph_minimum(instructions, order_tuples, stack_element_to_id)

        expected_dependency_graph = {'INSTR_4': ['INSTR_3', 'INSTR_1', 'INSTR_2'],
                            'INSTR_2': ['INSTR_0', 'PUSH', 'INSTR_1'],
                            'INSTR_0': ['PUSH', 'PUSH'], 'INSTR_1': [],
                            'INSTR_3': ['INSTR_2', 'PUSH', 'INSTR_2'],
                            'INSTR_5': ['INSTR_0', 'PUSH'],
                            'INSTR_6': ['INSTR_2', 'INSTR_2', 'INSTR_5'],
                            'INSTR_7': ['INSTR_4', 'INSTR_1', 'INSTR_6'],
                            'PUSH': []}
        self.assertDictEqual(dependency_graph, expected_dependency_graph)