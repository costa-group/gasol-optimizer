import json
import os
import sys

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))


import itertools

import global_params.constants as constants
from smt_encoding.encoding_initialize import (initialize_a_vars,
                                              initialize_l_vars,
                                              initialize_s_vars,
                                              initialize_t_vars,
                                              initialize_u_vars,
                                              initialize_x_vars)
from smt_encoding.instructions.instruction_factory import InstructionFactory


def generate_uninterpreted_instructions(user_instr_dict, fact_instr : InstructionFactory):
    return [fact_instr.create_instruction_json_format(instr) for instr in user_instr_dict]


class SMSEncoding:

    def __init__(self, json_format, flags, var_initial_idx=0):
        self._factory = InstructionFactory(var_initial_idx)
        self._flags = flags
        self._initialize_from_json_format(json_format)
        self._encoding_instructions = self._generate_instructions_from_flags()


    def _initialize_from_json_format(self, json_format):
        self._bs = json_format['max_sk_sz']
        self._user_instr = json_format['user_instrs']
        self._b0 = json_format["init_progr_len"]
        self._initial_stack = json_format['src_ws']
        self._final_stack = json_format['tgt_ws']
        self._variables = json_format['vars']
        self._current_cost = json_format['current_cost']
        self._mem_order = [*json_format['storage_dependences'], *json_format['memory_dependences']]


    # When initializing the encoding, we need to select which instructions are considered when building the model.
    # This includes using PUSH as uninterpreted functions or not, same for POP and so on...
    def _generate_instructions_from_flags(self):
        instructions = []

        if not self._flags["push_uninterpreted"]:
            instructions.append(self._factory.create_instruction_name("PUSH"))

        if not self._flags["pop_uninterpreted"]:
            instructions.append(self._factory.create_instruction_name("POP"))

        instructions.append(self._factory.create_instruction_name("NOP"))

        swapk_instr = [self._factory.create_instruction_name("SWAP" + str(k))
                       for k in range(1, min(self._bs, constants.max_k_swap + 1))]
        instructions.extend(swapk_instr)

        dupk_instr = [self._factory.create_instruction_name("DUP" + str(k))
                       for k in range(1, min(self._bs, constants.max_k_dup + 1))]
        instructions.extend(dupk_instr)

        uninterpreted_instr = generate_uninterpreted_instructions(self._user_instr, self._factory)
        instructions.extend(uninterpreted_instr)

        return instructions

    def _initialize_variables_from_flags(self):
        initialize_x_vars(self._b0, self._bs, self._ini)
        initialize_u_vars()
        initialize_t_vars()
        initialize_s_vars()

        # If PUSH is considered as a basic operation, then aj variables are generated
        if not self._flags["push_uninterpreted"]:
            initialize_a_vars()


    def generate_hard_constraints(self):
        constraints = []
        # Encoding of the impact instructions as hard constraints
        constraints.extend(itertools.chain.from_iterable(
            [instr.encoding_instruction(b0 = self._b0, bs = self._bs, initial_pos_seq=0, final_pos_seq=self._b0,
                                        initial_pos_instr=0, final_pos_instr=self._b0) for instr in self._encoding_instructions]))
        return constraints


    def generate_soft_constraints(self):
        pass


if __name__ == "__main__":
    with open("../examples/example.json") as f:
        json_data = json.load(f)

    flags = {"push_uninterpreted": False, "pop_uninterpreted": False}
    encoding = SMSEncoding(json_data, flags)
    for constraint in encoding.generate_hard_constraints():
        print(constraint)
