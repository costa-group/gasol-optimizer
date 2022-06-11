
from smt_encoding.instructions.uninterpreted_instruction import UninterpretedInstruction
from smt_encoding.instructions.encoding_instruction import InstructionSubset, Stack_Var_T
from smt_encoding.constraints.function import ExpressionReference, Function, Sort
from smt_encoding.constraints.connector import Formula_T
from collections import Set
from typing import List, Dict, Tuple, Union

# TODO: instead of returning Dict[str, Formula_T], return Dict[str, List[Formula_T]] to allow stack vars being obtained
#  from different operations e.g. LT(a, b) and GE(b, a)


class UninterpretedOpcodeTermCreation:

    def __init__(self, instructions: List[UninterpretedInstruction], initial_stack: List[Stack_Var_T],
                 sort_type: Sort = Sort.integer):
        """
        :param instructions: instructions to generate an ExpressionReference
        :param initial_stack: elements contained in the initial stack (ground elements)
        :param sort_type: sort range for the uninterpreted generated expressions
        """
        self._instructions = instructions

        # We need only to consider those stack variables that are strings. Int stack variables are directly encoded
        # using that representation
        self._ground_stack_elements = initial_stack
        self._sort_type = sort_type

        self._stack_element_to_instr = {instruction.output_stack: instruction
                                        for instruction in instructions if instruction.output_stack is not None}

    def opcode_rep_with_stack_vars(self) -> Tuple[Dict[str, Formula_T], List[Function]]:
        counter = 0
        stack_var_to_term = dict()
        created_functions = []
        
        for stack_var in self._ground_stack_elements:
            function = Function(f"s_{counter}", self._sort_type)
            counter += 1
            stack_var_to_term[stack_var] = function()
            created_functions.append(function)

        for instruction in self._instructions:
            # We are considering only instructions that actually output a value
            if instruction.output_stack is not None:
                function = Function(f"s_{counter}", self._sort_type)
                counter += 1
                stack_var_to_term[instruction.output_stack] = function()
                created_functions.append(function)

        return stack_var_to_term, created_functions

    def opcode_rep_with_int(self, initial_int: int = 0) -> Tuple[Dict[str, Formula_T], List[Function]]:
        """
        Encodes stack var directly as integers, assigning values from initial_int (included) onwards
        :param initial_int: initial value from which the assignment is made
        :return: a tuple with the conversion from instruction id to the corresponding integer and list representing
        the created functions (empty in this case)
        """
        ground_stack_var_to_term = {stack_var: (i + initial_int)
                                    for i, stack_var in enumerate(self._ground_stack_elements)}

        next_int = initial_int + len(ground_stack_var_to_term)
        
        instr_stack_var_to_term = {instruction.output_stack: (i + next_int) for i, instruction in
                                   enumerate((instr for instr in self._instructions if instr.output_stack is not None))}
        
        return dict(ground_stack_var_to_term, **instr_stack_var_to_term), []

    def _opcode_rep_with_uf(self, instruction: UninterpretedInstruction, sort_type: Sort,
                            stack_var_to_term: Dict[str, ExpressionReference],
                            functors: Dict[str, Function]) -> Union[int, ExpressionReference]:

        if instruction.output_stack in stack_var_to_term:
            return stack_var_to_term[instruction.output_stack]

        arguments = []

        for input_element in instruction.input_stack:
            if type(input_element) == int:
                arguments.append(input_element)
            # Element is part of the initial stack, as it has no instruction tied to it. Therefore, already contained
            # in stack_var_to_term dict
            elif input_element not in self._stack_element_to_instr:
                arguments.append(stack_var_to_term[input_element])
            else:
                arguments.append(self._opcode_rep_with_uf(self._stack_element_to_instr[input_element],
                                                          sort_type, stack_var_to_term, functors))

        # Functor name: remove all whitespaces (such as "PUSH [$]" or "PUSH #[$]") and lower the opcode name
        functor_name = instruction.opcode_name.replace(' ', '').lower()
        functor = Function(functor_name,
                           *[arg.type if type(arg) == ExpressionReference else Sort.integer for arg in arguments],
                           sort_type)
        term_encoding = ExpressionReference(functor, *arguments)

        stack_var_to_term[instruction.output_stack] = term_encoding
        functors[instruction.output_stack] = functor

        return term_encoding

    def opcode_rep_with_uf(self) -> Tuple[Dict[str, Formula_T], List[Function]]:
        stack_var_to_term: Dict[str, ExpressionReference] = dict()
        functors: Dict[str, Function] = dict()
        
        for i, stack_var in enumerate(self._ground_stack_elements):
            function = Function(f"s_{i}", self._sort_type)
            stack_var_to_term[stack_var] = function()
            functors[stack_var] = function

        for instruction in self._instructions:
            # We are considering only non-store operations, as store operations do not have an uninterpreted
            # function so far
            if instruction.instruction_subset != InstructionSubset.store:
                self._opcode_rep_with_uf(instruction, self._sort_type, stack_var_to_term, functors)
        return stack_var_to_term, list(functors.values())
