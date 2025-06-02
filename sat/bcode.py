#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## bcode.py
##
##  Created on: Oct 26, 2022
##      Author: Alexey Ignatiev
##      E-mail: alexey.ignatiev@monash.edu
##

#
#==============================================================================
from collections import defaultdict
import json
import os
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver
import sys


#
#==============================================================================
class Instruction(object):
    """
        A class for representing EVM instructions.
    """

    def __init__(self, id_, type_, inps, outs, size, gas, commutative=False, wasm=False):
        """
            Initialiser.
        """

        self.id = id_
        self.type = type_
        self.inps = inps
        self.outs = outs
        self.size = size
        self.gas = gas
        self.comm = commutative
        self.uniq = False
        self.wasm = wasm

    def small_zeroary(self):
        """
            Check if this operation is zero-ary with a small size.
        """

        return self.type in ('PUSH', 'ZERO') and (self.size <= 2 or self.wasm)

    def large_zeroary(self):
        """
            Check if this operation is zero-ary with a small size.
        """
        # PUSH and ZERO instructions in Wasm are zero-ary
        return self.type in ('PUSH', 'ZERO') and self.size > 2 and not self.wasm


#
#==============================================================================
class ByteCode(object):
    """
        EVM byte code representation.
    """

    def __init__(self, options, from_filename=None, from_fp=None, from_string=None, from_dict=None):
        """
            Initialiser.
        """

        self.options = options
        self.to_pop = []
        self.ideps = {}
        self.mingap = 0
        self.maxgap = 0
        self.maxinp = 1
        self.maxout = 1
        self.store_present = False

        if from_filename:
            self.from_file(from_filename)
        elif from_fp:
            self.from_fp(from_fp)
        elif from_string:
            self.from_string(from_string)
        elif from_dict:
            # If the json file is passed directly as a dict, we just process the data
            self.process_data(from_dict)

    def from_file(self, filename):
        """
            Read a JSON file given its name.
        """

        with open(filename, 'r') as fp:
            self.from_fp(fp)

    def from_fp(self, filepointer):
        """
            Actual file pointer reading.
        """

        data = json.load(filepointer)
        self.process_data(data)

    def from_string(self, json_string):
        """
            Reading from a string.
        """

        data = json.loads(json_string)
        self.process_data(data)

    def process_data(self, data):
        """
            Processing the data.
        """

        # initial and maximum program length
        self.mlen = data['init_progr_len']

        # reading minimul length if it is available
        self.minlen = data['min_length'] if 'min_length' in data else 0

        # original solution
        if 'original_instrs' in data:
            self.oins = data['original_instrs']
        if self.options.init and 'original_code_with_ids' in data:
            self.osol = data['original_code_with_ids']
        else:
            self.osol = []

        if 'current_cost' in data:
            self.cost = data['current_cost']

        # source and target states
        self.ssta = data['src_ws']
        self.tsta = data['tgt_ws']

        # instruction dependencies
        if 'instr_dependencies' in data:
            self.ideps = data['instr_dependencies']

        # stack size
        self.sksz = data['max_sk_sz']

        # storage and memory dependencies
        self.adeps = data['dependencies']

        # a list of pairs forbidding immediate dependencies
        self.ndeps = set([])
        if 'non_immediate_dependencies' in data:
            self.ndeps = set([tuple([p[1], p[0]]) for p in data['non_immediate_dependencies']])

        # variables (null + the actual variables)
        self.vars = tuple([None] + data['vars'])

        # we expect this to be provided for WASM code only
        if self.options.wasm:
            # the total number of available registers
            self.rgsz = data['max_registers_sz']

            # register changes
            self.regs = [(pair[0], pair[1]) for pair in data['register_changes']]

        # user instructions
        self.inst = defaultdict(lambda: Instruction(None, None, [], [], None, None))
        self.imap = {}  # output to instruction map
        for inst in data['user_instrs']:
            self.inst[inst['id']].id = inst['id']
            self.inst[inst['id']].inps = inst['inpt_sk']
            self.inst[inst['id']].outs = inst['outpt_sk']
            self.inst[inst['id']].size = inst['size']
            self.inst[inst['id']].gas = inst['gas']
            self.inst[inst['id']].comm = inst['commutative']
            self.inst[inst['id']].uniq = True  # ops from the file are unique
            self.inst[inst['id']].wasm = self.options.wasm # store the language used to determine small zeroary ops

            # keeping track of the maximum number of inputs and outputs
            self.maxinp = max(self.maxinp, len(inst['inpt_sk']))
            self.maxout = max(self.maxout, len(inst['outpt_sk']))

            # classifying the type of operation
            if len(inst['inpt_sk']) == 1 and len(inst['outpt_sk']) == 1:
                self.inst[inst['id']].type = 'UNARY'
            elif len(inst['inpt_sk']) == 2 and len(inst['outpt_sk']) == 1:
                self.inst[inst['id']].type = 'BINARY'
            elif (self.options.wasm and (inst['opcode'] == '10' or inst['opcode'] == '1b')) or len(inst['inpt_sk']) == 1 and len(inst['outpt_sk']) == 0:
                # here global.set instructions are treated as function calls
                # since they are essentially a POP with an input requirement
                self.inst[inst['id']].type = 'FCALL'
            elif len(inst['inpt_sk']) == 2 and len(inst['outpt_sk']) == 0:
                self.inst[inst['id']].type = 'STORE'
                self.store_present = True
            elif len(inst['inpt_sk']) == 0 and len(inst['outpt_sk']) == 1 and not inst['disasm'].startswith('PUSH'):
                self.inst[inst['id']].type = 'ZERO'
            elif inst['disasm'].startswith('PUSH'):
                # all the PUSH operations are treated specially
                self.inst[inst['id']].type = 'PUSH'
            else:  # by default, take the type from the input file
                   # e.g. POP go here
                self.inst[inst['id']].type = inst['disasm']

            # difference between the numbers of inputs and outputs
            gap = len(inst['inpt_sk']) - len(inst['outpt_sk'])
            self.mingap = min(self.mingap, gap)
            self.maxgap = max(self.maxgap, gap)

            if 'value' in inst:
                self.inst[inst['id']].value = inst['value']

            if inst['outpt_sk']:
                # here we assume there is always a single output (if any)!
                self.imap[inst['outpt_sk'][0]] = inst['id']

        if self.options.pdeps:
            self.analyze_deps()

            # the length of the shortest prefices and suffices per operation
            if 'lower_bounds' in data:
                self.preflen = {op: max(len(self.to_pop), data['lower_bounds'][op]) for op in self.inst}
            else:
                self.preflen = {op: len(self.to_pop) for op in self.inst}

            if 'upper_bounds' in data:
                self.sufflen = {op: self.mlen - data['upper_bounds'][op] - 1 for op in self.inst}
            else:
                self.sufflen = {op: 0 for op in self.inst}

            if self.options.bounds:
                self.analyze_bounds()

        if self.options.tail:
            self.analyze_tail()

        # special instruction None == NOP
        self.inst[None] = Instruction(None, None, [], [], None, None)
        self.imap[None] = None

        # keeping all the operations (plus None == NOP)
        self.ops = tuple(list(self.inst.keys()))

    def analyze_deps(self):
        """
            Analyse the inputs and outputs of the operations and check
            operation dependencies.
        """

        # mapping from variables to operations
        inps, outs = defaultdict(lambda: []), defaultdict(lambda: [])
        ssta, tsta = set(self.ssta), set(self.tsta)

        # source and target register states
        sreg, treg = set(), set()
        if self.options.wasm:
            sreg, treg = set([p[0] for p in self.regs]), set([p[1] for p in self.regs])

        for op, inst in self.inst.items():
            for inp in inst.inps:
                inps[inp].append(op)

            for out in inst.outs:
                outs[out].append(op)

        # each term must have a single creator
        assert all(map(lambda o: True if len(o) == 1 else False, outs.values()))

        # incrementing the number of uses for terms appearing in the target
        for var in self.tsta:
            inps[var].append('TSTA')

        # same stuff for variables required to be in the final register states
        if self.options.wasm:
            for pair in self.regs:
                inps[pair[1]].append('TREG')

        # here, we will store the pair of (dependent, dependency)
        self.pdeps = []
        self.deps_avail = set([])  # operations participating in the dependencies

        # getting the dependencies
        for inp in inps:
            if inp not in ssta and inp not in sreg:  # unless this input is given in source state
                creator = self.inst[outs[inp][0]]

                # traversing all the users of this term
                for user in inps[inp]:
                    if user in ('TSTA', 'TREG'):  # ignoring the target state
                        continue

                    # actual instruction instead of its id
                    user = self.inst[user]

                    # unary immediate dependency
                    if self.options.config not in ('base', 'e', 'g', 'h', 'allbutf') and inp not in treg and ((user.type in ('UNARY', 'FCALL') and len(user.inps) == 1 and (len(inps[inp]) == 1 or creator.small_zeroary())) or \
                            (user.type in ('BINARY', 'STORE', 'FCALL') and len(user.inps) > 1 and user.inps[0] == inp and (user.inps[1] in ssta or user.inps[1] in sreg) and not user.comm and (len(inps[inp]) == 1 or creator.small_zeroary()))):
                        self.pdeps.append(tuple([user.id, tuple([creator.id]), 1]))

                    # binary immediate dependency
                    elif self.options.config not in ('base', 'e', 'f', 'h') and inp not in treg and (user.type in ('BINARY', 'STORE', 'FCALL') and len(user.inps) == 2 and \
                            ((not self.options.wasm and (not user.comm and user.inps[0] == inp or user.comm and inp in user.inps)) or \
                                (self.options.wasm and user.inps[0] == inp))):

                        # and the two inputs are:
                        if not user.comm:
                            i1, i2 = inp, user.inps[1]
                        else:
                            if user.inps[0] != user.inps[1]:
                                i1, i2 = inp, (set(user.inps) - set([inp])).pop()  # may lead to duplicate dependencies
                            else:  # a weird case of duplicate arguments
                                i1, i2 = inp, inp

                        if i2 in ssta or i2 in sreg: # skip instructions whose second input is given in the source state
                            creator1 = self.inst[outs[i1][0]]
                            if creator1.small_zeroary() and user.comm:
                                self.pdeps.append(tuple([user.id, tuple([creator1.id]), 1]))

                            continue

                        creator1, creator2 = self.inst[outs[i1][0]], self.inst[outs[i2][0]]

                        if user.comm:  # commutative operation
                            if len(inps[i1]) == 1 and len(inps[i2]) == 1:
                                self.pdeps.append(tuple([user.id, tuple(sorted([creator1.id, creator2.id])), 1]))
                            elif creator1.small_zeroary():
                                # first is zeroary
                                self.pdeps.append(tuple([user.id, tuple([creator1.id]), 1]))

                                if creator2.small_zeroary():
                                    # both are zeroary
                                    self.pdeps.append(tuple([user.id, tuple([creator2.id]), 2]))
                            elif creator2.small_zeroary():
                                # second is zeroary
                                self.pdeps.append(tuple([user.id, tuple([creator2.id]), 1]))

                        else:  # non-commutative operation
                            if creator1.small_zeroary():
                                # first is zeroary
                                self.pdeps.append(tuple([user.id, tuple([creator1.id]), 1]))

                                if creator2.small_zeroary() or len(inps[i2]) == 1:
                                    # both are zeroary
                                    self.pdeps.append(tuple([user.id, tuple([creator2.id]), 2]))
                            elif len(inps[i1]) == 1:
                                self.pdeps.append(tuple([user.id, tuple([creator1.id]), 1]))

                    else:  # here goes everything else
                        self.pdeps.append(tuple([user.id, tuple([creator.id]), 0]))

        # taking storage and memory dependencies into account
        for dep in self.adeps:
            self.pdeps.append(tuple([dep[1], tuple([dep[0]]), 0]))

        # taking instruction dependencies from the input into account
        for idep in self.ideps:
            for depcy in self.ideps[idep]:
                self.pdeps.append(tuple([idep, tuple([depcy]), 0]))

        # removing duplicate dependencies
        self.pdeps = sorted(set(self.pdeps))

        # removing immediate dependencies conflicting with ndeps
        # (these are coming from JSON)
        pdeps, dflags = [], []
        for dep in self.pdeps:
            to_test = dep[1][0] if len(dep[1]) == 1 else dep[1]
            if dep[2] == 0 or tuple([dep[0], to_test]) not in self.ndeps:
                pdeps.append(dep)
                dflags.append(True)
            else:
                dflags.append(False)
        self.pdeps, pdeps = pdeps, self.pdeps  # swapping original with filtered
                                               # (for verbose printing below)

        # aggregating all the involved instructions
        for dep in self.pdeps:
            self.deps_avail.add(dep[0])
            self.deps_avail = self.deps_avail.union(dep[1])

        self.pdeps = sorted(set(self.pdeps))
        self.deps_avail = sorted(self.deps_avail)

        if self.options.verbose > 3:
            for flag, dep in zip(dflags, pdeps):
                if flag:
                    print('c dep {0}: {1} -> {2}'.format(dep[2], dep[0], ' | '.join(dep[1])))
                else:
                    print('c dep {0}: {1} -> {2} ## {3}'.format(dep[2], dep[0], ' | '.join(dep[1]), 'blocked as conflicting!'))

        if self.options.config not in ('base', 'f', 'g', 'h'):
            # now, we need to deal with unused values in the source stack
            for inp in self.ssta:
                if inp not in inps and inp not in tsta:
                    self.to_pop.append(inp)
                else:
                    break

    def analyze_tail(self):
        """
            Get the common suffix for the source and target states.
        """

        self.tail = []

        ssta = self.ssta[::-1]
        tsta = self.tsta[::-1]

        for v1, v2 in zip(ssta, tsta):
            if v1 == v2:
                self.tail.append(v1)
            else:
                break

        self.tail.reverse()

        if self.options.verbose > 1 and self.tail:
            print('c tail:', ', '.join(self.tail))

    def analyze_bounds(self):
        """
            Try to analyse the potential start and end times for each
            operation in the dependency. Do so locally given the dependency
            of instructions detected.
        """

        cnf, mgr = CNF(), IDPool()
        for depcy in self.pdeps:
            cnf.append([-mgr.id(depcy[0])] + [mgr.id(reqw) for reqw in depcy[1]])

        # here are all the variables introduced
        vids = sorted(mgr.id2obj.keys())

        preflen = {op: len(self.to_pop) for op in self.inst}
        sufflen = {op: 0 for op in self.inst}

        # first, determining the prefices
        with Solver(name=self.options.solver, bootstrap_with=cnf) as solver:
            solver.set_phases(literals=[-v for v in vids])
            for v in vids:
                _, props = solver.propagate(assumptions=[v])
                preflen[mgr.obj(v)] += len(props) - 1  # excluding v itself

        # next, determining the suffices
        with Solver(name=self.options.solver, bootstrap_with=cnf) as solver:
            solver.set_phases(literals=vids)
            for v in vids:
                _, props = solver.propagate(assumptions=[-v])
                sufflen[mgr.obj(v)] += len(props) - 1  # excluding v itself

        # updating the final prefix and suffix lengths
        for op in self.inst:
            self.preflen[op] = max(self.preflen[op], preflen[op])
            self.sufflen[op] = max(self.sufflen[op], sufflen[op])
