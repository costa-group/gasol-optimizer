
from smt_encoding.instructions.uninterpreted_instruction import UninterpretedInstruction, Id_T
from smt_encoding.instructions.encoding_instruction import InstructionSubset
from smt_encoding.constraints.function import ExpressionReference, Function, Sort
from smt_encoding.constraints.connector import Formula_T
from typing import List, Dict, Tuple, Union


class UninterpretedOpcodeTermCreation:

    def __init__(self, instructions: List[UninterpretedInstruction], sort_type: Sort = Sort.integer):
        """
        :param instructions: instructions to generate an ExpressionReference
        :param sort_type: sort range for the uninterpreted generated expressions
        """
        self._instructions = instructions
        self._sort_type = sort_type

        self._stack_element_to_instr = {instruction.output_stack: instruction
                                             for instruction in instructions if instruction.output_stack is not None}

    def opcode_rep_with_stack_vars(self) -> Tuple[Dict[Id_T, Formula_T], List[Function]]:
        counter = 0
        id_to_term = dict()
        created_functions = []

        for instruction in self._instructions:
            # We are considering only instructions that actually output a value
            if instruction.output_stack is not None:
                function = Function(f"s_{counter}", self._sort_type)
                counter += 1
                id_to_term[instruction.id] = function()
                created_functions.append(function)

        return id_to_term, created_functions

    def opcode_rep_with_int(self, initial_int: int = 0) -> Tuple[Dict[Id_T, Formula_T], List[Function]]:
        """
        Encodes stack var directly as integers, assigning values from initial_int (included) onwards
        :param initial_int: initial value from which the assignment is made
        :return: a tuple with the conversion from instruction id to the corresponding integer and list representing
        the created functions (empty in this case)
        """
        id_to_term = {instruction.id: (i + initial_int) for i, instruction in
                      enumerate((instr for instr in self._instructions if instr.output_stack is not None))}
        return id_to_term, []

    def _opcode_rep_with_uf(self, instruction: UninterpretedInstruction, sort_type: Sort,
                            id_to_term: Dict[Id_T, ExpressionReference],
                            functors: Dict[Id_T, Function]) -> Union[int, ExpressionReference]:

        if instruction.id in id_to_term:
            return id_to_term[instruction.id]

        arguments = []

        for input_element in instruction.input_stack:
            if type(input_element) == int:
                arguments.append(input_element)
            else:
                arguments.append(self._opcode_rep_with_uf(self._stack_element_to_instr[input_element],
                                                             sort_type, id_to_term, functors))

        # Functor name: remove all whitespaces (such as "PUSH [$]" or "PUSH #[$]") and lower the opcode name
        functor_name = instruction.opcode_name.replace(' ', '').lower()
        functor = Function(functor_name,
                           *[arg.type if type(arg) == ExpressionReference else Sort.integer for arg in arguments], sort_type)
        term_encoding = ExpressionReference(functor, *arguments)

        id_to_term[instruction.id] = term_encoding
        functors[instruction.id] = functor

        return term_encoding

    def opcode_rep_with_uf(self) -> Tuple[Dict[Id_T, Formula_T], List[Function]]:
        id_to_term: Dict[Id_T, ExpressionReference] = dict()
        functors: Dict[Id_T, Function] = dict()

        for instruction in self._instructions:
            # We are considering only non-store operations, as store operations do not have an uninterpreted
            # function so far
            if instruction.instruction_subset != InstructionSubset.store:
                self._opcode_rep_with_uf(instruction, self._sort_type, id_to_term, functors)
        return id_to_term, list(functors.values())
