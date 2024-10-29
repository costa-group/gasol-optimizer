#!/usr/bin/env python3

# use it with
# python3 dzn_generator file.json

# --solver = chuffed

import json
import sys
from typing import Dict, List
from collections import defaultdict


def make_list(l):
    return ', '.join(str(elem) for elem in l)


class SMSgreedy:

    def __init__(self, json_format, file=sys.stdout):
        self._f = file
        self._bs = json_format['max_sk_sz']
        self._user_instr = json_format['user_instrs']
        self._b0 = json_format["init_progr_len"]
        self._initial_stack = json_format['src_ws']
        self._final_stack = json_format['tgt_ws']
        self._variables = json_format['vars']
        self._deps = json_format['dependencies']
        self._registers = json_format["register_changes"] if 'register_changes' in json_format else None
        self._max_registers = json_format["max_registers_sz"] if 'max_registers_sz' in json_format else None
        self._min_length = json_format['min_length'] if 'min_length' in json_format else 0
        self._original_code_with_ids = json_format['original_code_with_ids'] if 'original_code_with_ids' in json_format else []
        self._lower_bounds = json_format['lower_bounds'] if 'lower_bounds' in json_format else {}
        self._upper_bounds = json_format['upper_bounds'] if 'upper_bounds' in json_format else {}

        # Extra declarations
        self._var2repr = {var: f"s{i}" for i, var in enumerate(self._variables)}

        self._id2instr = {instr['id']: instr for instr in self._user_instr}

        # Dict that given the number of elements consumed and produced (in_n and out_n) returns the category name.
        # Push instructions are considered separately, as they overlap with ZEROARYOP instructions
        self._arity2name = {(0, 1): 'ZEROARYOP', (2, 0): 'STOROP', (1, 1): 'UNARYOP', (2, 1): 'BINARYOP'}

        # Given the category name, returns the preffix associated to the variables name and the category identifier
        self._name2info = {'ZEROARYOP': ['zero', 'Z'], 'PUSHOP': ['push', 'P'], 'STOROP': ['stor', 'S'],
                           'UNARYOP': ['un', 'U'], 'BINARYOP': ['bin', 'B']}

    def _group_instructions(self) -> Dict[str, Dict[str, List]]:
        """
        Returns the different variables that need to be declared in the dzn for every category of instructions.
        For each category, it contains a subdict with the name of the different lists that need to be declared:
        comm, gas, sz, in, out...
        """
        name2declarations = defaultdict(lambda: defaultdict(lambda: []))
        for ins in self._user_instr:
            in_n, out_n = len(ins["inpt_sk"]), len(ins["outpt_sk"])

            # Push instructions are treated separately, as the category is not identified by in_n and out_n
            if ins["push"]:
                category = 'PUSHOP'
            # Otherwise, check the arity2name dict and initialize a new category if it is not included
            else:
                category_info = self._arity2name.get((in_n, out_n), None)

                # TODO: here decide how to process call instructions
                # If there is no such category, we introduce another one called "CALL_{in_n}_{our_ar}"
                if category_info is None:
                    category = f"call_{in_n}_{out_n}"
                    dep = f"C_{in_n}_{out_n}"
                    preffix = f"c_{in_n}_{out_n}_"
                    self._arity2name[(in_n, out_n)] = category
                    self._name2info[category] = [preffix, dep]
                else:
                    category = category_info

            # Now we introduce the corresponding variables
            current_vars = name2declarations[category]

            # If there are whitespaces or '.' in between, we add '
            if " " in ins["id"] or '.' in ins["id"]:
                id_ = "\'" + ins["id"] + "\'"
            else:
                id_ = ins["id"]

            current_vars["id"].append(id_)

            # Only add the i+1 subindex if there is at least two elements
            for i in range(in_n):
                current_vars[f"in{i+1 if in_n > 1 else ''}"].append(self._var2repr[ins["inpt_sk"][i]])

            for i in range(out_n):
                current_vars[f"out{i+1 if out_n > 1 else ''}"].append(self._var2repr[ins["outpt_sk"][i]])

            current_vars['comm'].append(str(ins["commutative"]).lower())
            current_vars['gas'].append(ins["gas"])
            current_vars['sz'].append(ins["size"])
            if len(self._lower_bounds) > 0:
                current_vars['lb'].append(self._lower_bounds[ins["id"]] + 1)
                current_vars['ub'].append(self._upper_bounds[ins["id"]] + 1)
            else:
                current_vars['lb'].append(1)
                current_vars['ub'].append(self._b0)

        # If there is a category with no instructions, we add the dummy instructions
        for category in self._name2info:
            if category not in name2declarations:
                current_vars = name2declarations[category]

                # Determine arity by searching dict self._arity2name. Push instructions is not included
                if category == "PUSHOP":
                    in_n, out_n = 0, 1
                else:
                    in_n, out_n = [ar for ar, other_cat in self._arity2name.items() if other_cat == category][0]

                current_vars["id"].append(category + "_dummy")

                for i in range(in_n):
                    current_vars[f"in{i+1 if in_n > 1 else ''}"].append("null")

                for i in range(out_n):
                    current_vars[f"out{i+1 if out_n > 1 else ''}"].append("null")

                current_vars['comm'].append('false')
                current_vars['gas'].append(0)
                current_vars['sz'].append(0)
                current_vars['lb'].append(1)
                current_vars['ub'].append(self._b0)

        return name2declarations

    def _detect_category(self, id_: str) -> str:
        """
        Returns the letter used to identify a category of instructions. For instance, U for unary, B for binary...
        """
        instr = self._id2instr[id_]
        in_n, out_n = len(instr["inpt_sk"]), len(instr["outpt_sk"])
        category = self._arity2name[(in_n, out_n)]
        return self._name2info[category][1]

    def generate_dzn(self):
        term = "TERM = { \'.\'"
        for v, rep in self._var2repr.items():
            term += ", " + rep
        term += " };"
        print(term, file=self._f)
        print("null = \'.\';", file=self._f)
        print("s = " + str(self._b0) + ";", file=self._f)
        print("n = " + str(self._bs) + ";", file=self._f)
        print("min = " + str(self._min_length) + ";", file=self._f)

        categories2decl = self._group_instructions()
        # print("origsol = "+str(self._original_code_with_ids)+";", file=self._f)
        # print("% when empty means not available", file=self._f)

        for category, declrs in categories2decl.items():
            preffix, _ = self._name2info[category]

            for decl, variables_list in declrs.items():
                # The id follows a different format convention
                if decl == 'id':
                    print(f"{category} = [ " + make_list(variables_list) + " ];", file=self._f)

                # Comm operations are only the ones in binary category.
                # Gas and sz do not appear in the category STOROP
                elif (decl != 'comm' or category == 'BINARYOP') and (decl not in ['gas', 'sz'] or category != 'STOROP'):
                    print(f"{preffix}{decl} = [ " + make_list(variables_list) + " ];", file=self._f)

        startstack = [self._var2repr[v] for v in self._initial_stack]
        print("startstack = [ " + make_list(startstack) + " ];", file=self._f)

        endstack = [self._var2repr[v] for v in self._final_stack]
        print("endstack = [ " + make_list(endstack) + " ];", file=self._f)

        before = []
        after = []
        for p in self._deps:
            id1, id2 = p

            # Detect to which category belong id1 and id2
            before.append(f"{self._detect_category(id1)}({id1})")
            after.append(f"{self._detect_category(id2)}({id2})")

        print("before = [ " + make_list(before) + " ];", file=self._f)
        print("after = [ " + make_list(after) + " ];", file=self._f)

        # WASM structures:

        # TODO: decide how to process max_regs to deal with the EVM case
        if self._max_registers is not None:
            print("max_regs = " + str(self._max_registers) + ";", file=self._f)

        # TODO: decide how to process the state of the registers
        if self._registers is not None:
            initial_registers = [register[0] for register in self._registers]
            final_registers = [register[1] for register in self._registers]
            print("initial_registers = [ " + make_list(self._var2repr[var] for var in initial_registers) + " ];", file=self._f)
            print("final_registers = [ " + make_list(self._var2repr[var] for var in final_registers) + " ];", file=self._f)


if __name__ == "__main__":
    with open(sys.argv[1]) as f:
        json_data = json.load(f)

    out_file_name = ""
    if sys.argv[1].endswith(".json"):
        out_file_name = sys.argv[1][:-4] + "dzn"
    else:
        out_file_name = sys.argv[1] + "dzn"
    if len(sys.argv) > 2:
        name = out_file_name
        if '/' in name:
            p = len(name) - 1 - list(reversed(name)).index('/')
            name = name[p + 1:]
        out_file_name = sys.argv[2] + "/" + name

    with open(out_file_name, 'w') as f:
        encoding = SMSgreedy(json_data, f)
        encoding.generate_dzn()
