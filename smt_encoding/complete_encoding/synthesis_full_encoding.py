from smt_encoding.instructions.instruction_factory import InstructionFactory
from typing import Dict, Any, Tuple, List, Callable
from argparse import Namespace
from smt_encoding.complete_encoding.synthesis_encoding_instructions_stack import AssertHard, EncodingForStack
from smt_encoding.complete_encoding.synthesis_functions import SynthesisFunctions
from smt_encoding.instructions.instruction_bounds import InstructionBounds
from smt_encoding.instructions.instruction_bounds_simple import DumbInstructionBounds
from smt_encoding.instructions.instruction_bounds_with_dependencies import InstructionBoundsWithDependencies
from smt_encoding.complete_encoding.synthesis_soft_constraints import AssertSoft
import global_params.constants as constants
from smt_encoding.constraints.function import Function, Sort
from smt_encoding.instructions.encoding_instruction import InstructionSubset, Id_T
from smt_encoding.complete_encoding.synthesis_opcode_term_creation import UninterpretedOpcodeTermCreation, Formula_T
from smt_encoding.complete_encoding.synthesis_initialize_variables import stack_encoding_for_position, \
    restrict_t_domain, \
    expressions_are_distinct, initialize_stack_variables, stack_encoding_for_terminal, stack_encoding_for_position_empty
from smt_encoding.complete_encoding.synthesis_stack_constraints import push_basic_encoding, pop_encoding, nop_encoding, \
    swapk_encoding, dupk_encoding, non_comm_function_encoding, comm_function_encoding, store_stack_function_encoding, \
    pop_uninterpreted_encoding, push_basic_encoding_empty, pop_uninterpreted_encoding_empty, nop_encoding_empty, \
    swapk_encoding_empty, dupk_encoding_empty, non_comm_function_encoding_empty, comm_function_encoding_empty, \
    store_stack_function_encoding_empty, pop_encoding_empty
from smt_encoding.instructions.instruction_dependencies import (generate_dependency_graph_minimum,
                                                                generate_dependency_graph_only_memory)
from smt_encoding.complete_encoding.synthesis_pre_order import l_conflicting_constraints, direct_conflict_constraints
from smt_encoding.instructions.encoding_instruction import EncodingInstruction
from smt_encoding.complete_encoding.synthesis_soft_constraints import soft_constraints_direct, \
    soft_constraints_grouped_by_weight
from smt_encoding.complete_encoding.synthesis_additional_constraints import fromnop_encoding, \
    each_instruction_is_used_at_least_once, no_output_before_pop, each_function_is_used_at_most_once
from itertools import chain

SMS_T = Dict[str, Any]


class FullEncoding:

    def __init__(self, sms: SMS_T, flags: Namespace, initial_idx: int = 0):
        self._flags = flags
        self._initial_idx = initial_idx

        self._instruction_factory = InstructionFactory()

        self._encoding_stack = EncodingForStack()
        self._initialize_from_sms(sms)
        self._initialize_basic_instructions_with_encoding(self._encoding_stack)
        self._encoding_for_uninterpreted(self._encoding_stack)
        self._instructions: List[EncodingInstruction] = [*self._basic_instructions, *self._uninterpreted_instructions]
        self.theta_to_instr = self._instruction_factory.theta_value_to_instr()

        self._stack_var_to_term = self._initialize_term_to_variable_conversion()
        self._term_factory = None

        if self._flags.encode_terms == "uninterpreted_uf":
            self._term_factory = SynthesisFunctions(self._stack_var_to_term, Sort.uninterpreted,
                                                    Sort.uninterpreted_theta)
        else:
            self._term_factory = SynthesisFunctions(self._stack_var_to_term)

        stack_element_to_id_dict: Dict[str, Id_T] = {instruction.output_stack: instruction.id
                                                     for instruction in self._uninterpreted_instructions
                                                     if instruction.output_stack is not None}

        if flags.order_conflicts:
            # Allow complete dependency graph in the encoding by changing the way it is initialized (future)
            self._dependency_graph = generate_dependency_graph_minimum(self._uninterpreted_instructions, self.mem_order,
                                                                       stack_element_to_id_dict)
        else:
            self._dependency_graph = generate_dependency_graph_only_memory(self._uninterpreted_instructions,
                                                                           self.mem_order)

        self._bounds = self._initialize_bounds()

    def _initialize_from_sms(self, sms: SMS_T) -> None:
        self.bs = sms['max_sk_sz']
        self.b0 = sms['init_progr_len']

        self._uninterpreted_instructions = [self._instruction_factory.create_instruction_json_format(instr_json)
                                            for instr_json in sms['user_instrs']]

        self.current_cost = sms['current_cost']

        self.initial_instructions = sms['original_instrs']
        self.mem_order = [*sms['storage_dependences'], *sms['memory_dependences']]

        self.initial_stack = sms['src_ws']
        self.final_stack = sms['tgt_ws']
        self.variables = sms['vars']

        # Terminal flag appears in the SMS because when splitting the block,
        # only the last sub-block must have it enabled
        self._terminal = sms['is_revert']

    def _initialize_basic_instructions_with_encoding(self, stack_encoding: EncodingForStack) -> None:
        nop_instruction = self._instruction_factory.create_instruction_name("NOP")
        basic_instructions = [nop_instruction]
        encoding_function = nop_encoding_empty if self._flags.empty else nop_encoding
        stack_encoding.register_function_for_encoding(nop_instruction, encoding_function)

        if self._flags.pop_basic:
            pop_instruction = self._instruction_factory.create_instruction_name("POP")
            basic_instructions.append(pop_instruction)
            encoding_function = pop_encoding_empty if self._flags.empty else pop_encoding
            stack_encoding.register_function_for_encoding(pop_instruction, encoding_function)

        if self._flags.push_basic:
            push_basic = self._instruction_factory.create_instruction_name("PUSH")
            basic_instructions.append(push_basic)
            encoding_function = push_basic_encoding_empty if self._flags.empty else push_basic_encoding
            stack_encoding.register_function_for_encoding(push_basic, encoding_function)

        for k in range(1, min(self.bs, constants.max_k_dup + 1)):
            dupk_instruction = self._instruction_factory.create_instruction_name(''.join(('DUP', str(k))))
            basic_instructions.append(dupk_instruction)
            encoding_function = dupk_encoding_empty if self._flags.empty else dupk_encoding
            stack_encoding.register_function_for_encoding(dupk_instruction, encoding_function, k=k)

        for k in range(1, min(self.bs, constants.max_k_swap + 1)):
            swapk_instruction = self._instruction_factory.create_instruction_name(''.join(('SWAP', str(k))))
            basic_instructions.append(swapk_instruction)
            encoding_function = swapk_encoding_empty if self._flags.empty else swapk_encoding
            stack_encoding.register_function_for_encoding(swapk_instruction, encoding_function, k=k)

        self._basic_instructions = basic_instructions

    def _encoding_for_uninterpreted(self, stack_encoding: EncodingForStack) -> None:

        for instruction in self._uninterpreted_instructions:
            if instruction.instruction_subset == InstructionSubset.store:

                encoding_function = store_stack_function_encoding_empty if self._flags.empty \
                    else store_stack_function_encoding
                stack_encoding.register_function_for_encoding(instruction, encoding_function,
                                                              o0=instruction.input_stack[0],
                                                              o1=instruction.input_stack[1])

            elif instruction.instruction_subset == InstructionSubset.comm:
                # TODO add ac_solver option
                encoding_function = comm_function_encoding_empty if self._flags.empty else comm_function_encoding
                stack_encoding.register_function_for_encoding(instruction, encoding_function,
                                                              o0=instruction.input_stack[0],
                                                              o1=instruction.input_stack[1],
                                                              r=instruction.output_stack)

            elif instruction.instruction_subset == InstructionSubset.non_comm:

                encoding_function = non_comm_function_encoding_empty if self._flags.empty else non_comm_function_encoding

                stack_encoding.register_function_for_encoding(instruction, encoding_function,
                                                              o=instruction.input_stack,
                                                              r=instruction.output_stack)

            elif instruction.instruction_subset == InstructionSubset.pop:

                encoding_function = pop_uninterpreted_encoding_empty if self._flags.empty else pop_uninterpreted_encoding

                # Uninterpreted pop
                stack_encoding.register_function_for_encoding(instruction, encoding_function,
                                                              o0=instruction.input_stack[0])
            else:
                raise ValueError(f"{instruction.id} is a basic operation and should not appear in the list of uop")

    def _initialize_bounds(self) -> InstructionBounds:
        if self._flags.order_bounds:
            return InstructionBoundsWithDependencies(self._uninterpreted_instructions, self.mem_order,
                                                     self.final_stack, self.b0, self._initial_idx)
        else:
            return DumbInstructionBounds(self._initial_idx, self._initial_idx + self.b0 - 1)

    def _initialize_term_to_variable_conversion(self) -> Dict[str, Formula_T]:
        # Uninterpreted opcode creation must use their own Sort for evm representation when using UF
        if self._flags.encode_terms == "uninterpreted_uf":
            sort_type = Sort.uninterpreted
        else:
            sort_type = Sort.integer

        uop_creation = UninterpretedOpcodeTermCreation(self._uninterpreted_instructions, self.initial_stack,
                                                       self._flags.empty, sort_type)

        if self._flags.encode_terms.startswith("uninterpreted"):
            return uop_creation.opcode_rep_with_uf()[0]
        elif self._flags.encode_terms == "stack_vars":
            return uop_creation.opcode_rep_with_stack_vars()[0]
        elif self._flags.push_basic:
            # If push basic is in the encoding, then stack variables start from constants.int_limit onwards
            return uop_creation.opcode_rep_with_int(constants.int_limit)[0]
        else:
            # Otherwise, they start from 0 onwards
            return uop_creation.opcode_rep_with_int()[0]

    def _select_additional_constraints_from_flags(self) -> List[AssertHard]:
        # From nop encoding and each uninterpreted function is used at least once are always included by default

        theta_nop = \
            [instruction.theta_value for instruction in self._basic_instructions if instruction.opcode_name == "NOP"][0]
        theta_pops = [instruction.theta_value for instruction in self._instructions if
                      instruction.opcode_name.startswith("POP")]
        theta_swaps = [instruction.theta_value for instruction in self._basic_instructions if
                       instruction.opcode_name.startswith("SWAP")]
        theta_mem = [instruction.theta_value for instruction in self._uninterpreted_instructions
                     if instruction.instruction_subset == InstructionSubset.store]
        theta_uninterpreted = [instruction.theta_value for instruction in self._uninterpreted_instructions]

        additional_constraints = [*fromnop_encoding(self._term_factory, self._bounds, theta_nop),
                                  *each_instruction_is_used_at_least_once(self._term_factory,
                                                                          self._bounds, theta_uninterpreted),
                                  *no_output_before_pop(self._term_factory, self._bounds, theta_swaps, theta_mem,
                                                        theta_pops)]

        if self._flags.memory_encoding == "direct":
            additional_constraints.extend([constraint for instruction in self._uninterpreted_instructions
                                           if instruction.instruction_subset == InstructionSubset.store
                                           for constraint in
                                           each_function_is_used_at_most_once(self._term_factory, self._bounds,
                                                                              instruction.theta_value)])

        return additional_constraints

    def generate_hard_constraints(self) -> List[AssertHard]:
        initialization_constraints = restrict_t_domain(self._term_factory, self._bounds,
                                                       [instruction.theta_value for instruction in self._instructions])

        stack_constraints = [constraint for instruction in self._instructions for constraint in
                             self._encoding_stack.encode_instruction(instruction, self._bounds,
                                                                     self._term_factory, self.bs)]

        pre_order_encoding_function = l_conflicting_constraints
        if self._flags.memory_encoding == "l_vars":
            pre_order_constraints = pre_order_encoding_function(self._instructions, self._bounds,
                                                                self._dependency_graph, self._term_factory)
        else:
            pre_order_constraints = direct_conflict_constraints(self._uninterpreted_instructions, self.mem_order,
                                                                self.b0, self._bounds, self._term_factory,
                                                                self._flags.order_conflicts)

        stack_encoding_f = stack_encoding_for_position_empty if self._flags.empty else stack_encoding_for_position

        initial_stack_constraints = stack_encoding_f(self._initial_idx, self._term_factory,
                                                     self.initial_stack, self.bs)
        if self._terminal:
            # If block is terminal with REVERT, only two top elements in the stack must be checked
            final_stack_constraints = stack_encoding_for_terminal(self._initial_idx + self.b0, self._term_factory,
                                                                  self.final_stack)
        else:
            final_stack_constraints = stack_encoding_f(self._initial_idx + self.b0, self._term_factory,
                                                       self.final_stack, self.bs)
        distinct_constraints = []

        # Only works for UF encoding
        if self._flags.encode_terms.startswith("uninterpreted"):
            distinct_constraints = []
            theta_values = self._term_factory.created_theta_values()
            created_vars = self._term_factory.created_stack_vars()

            if len(created_vars) > 1:
                # Only include a distinct constraint if there are at least two expressions in the encoding
                distinct_constraints.extend(expressions_are_distinct(*created_vars))

            if len(theta_values) > 1:
                # It can be empty, if uninterpreted_int is activated and theta values are considered as numbers
                distinct_constraints.extend(expressions_are_distinct(*theta_values))

        elif self._flags.encode_terms == "stack_vars":
            if self._flags.push_basic:
                distinct_constraints.extend(initialize_stack_variables(self._term_factory, constants.int_limit))
            else:
                distinct_constraints.extend(initialize_stack_variables(self._term_factory, 0))

        additional_constraints = self._select_additional_constraints_from_flags()

        return list(
            chain(initialization_constraints, stack_constraints, pre_order_constraints, initial_stack_constraints,
                  final_stack_constraints, distinct_constraints, additional_constraints))

    def generate_soft_constraints(self) -> List[AssertSoft]:

        # Direct encoding considers all non-store operations susceptible of appearing multiple times
        def direct_encoding_filter(instruction: EncodingInstruction) -> bool:
            return instruction.instruction_subset != InstructionSubset.store

        # L_vars encoding only considers all not unique instructions in the soft constraints
        def l_vars_encoding_filter(instruction: EncodingInstruction) -> bool:
            return not instruction.unique_ui

        if self._flags.memory_encoding == "direct":
            soft_instruction_filter = direct_encoding_filter
        else:
            soft_instruction_filter = l_vars_encoding_filter

        if self._flags.size:
            weight_dict = {instruction.theta_value: min(instruction.size_cost, 5)
                           for instruction in self._instructions if soft_instruction_filter(instruction)}
        elif self._flags.length:
            weight_dict = {instruction.theta_value: 1 if instruction.id != 'NOP' else 0
                           for instruction in self._instructions if soft_instruction_filter(instruction)}
        else:
            weight_dict = {instruction.theta_value: instruction.gas_cost
                           for instruction in self._instructions if soft_instruction_filter(instruction)}

        if self._flags.direct:
            return soft_constraints_direct(self._term_factory, weight_dict, self._bounds, "cost")
        else:
            return soft_constraints_grouped_by_weight(self._term_factory, self.b0, weight_dict, self._bounds, "cost")

    def generate_full_encoding(self) -> Tuple[List[Function], List[AssertHard], List[AssertSoft]]:
        hard_constraints = self.generate_hard_constraints()
        soft_constraints = self.generate_soft_constraints()

        # Obtaining functions declared only makes sense AFTER having declared all the constraints
        functions_declared = self._term_factory.created_functions()

        return functions_declared, hard_constraints, soft_constraints
