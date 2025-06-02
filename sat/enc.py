#!/bin/env python
#-*- coding:utf-8 -*-
##
## enc.py
##
##  Created on: Oct 26, 2022
##      Author: Alexey Ignatiev
##      E-mail: alexey.ignatiev@monash.edu
##

#
#==============================================================================
from functools import reduce
from io import StringIO
import itertools
from collections import OrderedDict, defaultdict
import typing
from pysat.card import *
from pysat.formula import CNFPlus, IDPool, WCNFPlus
import sys


#
#==============================================================================
instr_id_T = typing.Optional[str]


def select_instructions_position(j: int, instructions: typing.List[typing.Tuple[instr_id_T, typing.Any]], b0: int,
                                 lb: typing.Dict[str, int], ub: typing.Dict[str, int]) -> typing.List[typing.Tuple[instr_id_T, typing.Any]]:
    return [(id_, arg) for id_, arg in instructions if lb.get(id_, 0) <= j <= ub.get(id_, b0)]


# Generates an ordered dict that has the cost of Wp sets as keys
# and the theta value of opcodes with that cost as values.
# Ordered by increasing costs
def generate_disjoint_sets_from_cost(instr_cost_tuple: typing.List[typing.Tuple[instr_id_T, typing.Any, int]]) -> \
        typing.List[typing.Tuple[int, typing.List[typing.Tuple[instr_id_T, typing.Any]]]]:
    disjoint_set: typing.Dict[int, typing.List[typing.Tuple[instr_id_T, typing.Any]]] = defaultdict(lambda: [])
    for instr_id, arg, cost in instr_cost_tuple:
        disjoint_set[cost].append((instr_id, arg))
    return [(k, v) for k, v in sorted(disjoint_set.items(), key=lambda elem: elem[0])]


class Encoding(object):
    """
        Encoding of a byte code block.
    """

    def __init__(self, bcode, options):
        """
            Initialiser.
        """

        # saving a copy of the byte code representation
        self.bcode = bcode

        # saving all the options
        self.options = options

        # lower bound on the length
        self.lenlb = 0

        # all the variables are to be stored here
        self.vpool = IDPool()

        # the final WCNF formula (potentially with native cardinality constraints)
        self.formula = WCNFPlus()

        # applying the encoding
        self.encode()

    def encode(self):
        """
            Apply the encoding.
        """

        # there must be something at the top of the stack
        # self.non_empty()

        # encode the states of the stack and the list of instructions
        self.exactly1()

        # encode emptyness implications
        self.empty_implies()

        # encode how step-by-step instructions change the stack
        self.instructions()

        # encode propagation forward
        if self.options.fprop:
            self.fpropagate()

        # encode propagation backward
        if self.options.bprop:
            self.bpropagate()

        # encode register value connections
        if self.options.wasm:
            self.lpropagate()

        if self.options.pdeps:
            self.dependencies()

        if self.options.tail and self.bcode.tail:
            self.enforce_tail()

        if self.options.bounds:
            self.enforce_bounds()

        if self.options.nodummy:
            self.forbid_dummy()

        # encode the constraints on the initial and target states of the stack
        self.targets()

        # encode the objective function
        self.objective()

        # augment the formula with the comments on the variables meaning
        self.comments()

    def comments(self):
        """
            Add the comments on the meaning of the variables used.
        """

        for obj, id_ in self.vpool.obj2id.items():
            self.formula.comments.append('c {0} <-> {1}'.format(id_, obj))

    def targets(self):
        """
            Encoding the constraints on the initial and target states.
        """

        # first, handling the constraints on the inputs
        # whatever values are specified in the input file
        ssta = self.bcode.ssta + ([None] if len(self.bcode.ssta) < self.bcode.sksz else [])
        for pos, val in enumerate(ssta):
            self.formula.append([self.var(step=0, pos=pos, val=val)])

        # second, constraints on the target stack
        # whatever values are specified in the input file
        tsta = self.bcode.tsta + ([None] if len(self.bcode.tsta) < self.bcode.sksz else [])
        for pos, val in enumerate(tsta):
            self.formula.append([self.var(step=self.bcode.mlen, pos=pos, val=val)])

        if self.options.wasm:
            # third, if we deal with WASM programs, we may have
            # the constraints on the initial and target content
            # of some of the registers
            regs = self.bcode.regs + ([(None, None)] if len(self.bcode.regs) < self.bcode.rgsz else [])
            for pos, reg in enumerate(self.bcode.regs):
                self.formula.append([self.loc(step=0, pos=pos, val=reg[0])])
                self.formula.append([self.loc(step=self.bcode.mlen, pos=pos, val=reg[1])])

            # all the other registers must contain None at the beginning
            # we don't do the same with the target state as we don't care
            if len(self.bcode.regs) < self.bcode.rgsz:
                self.formula.append([self.loc(step=0, pos=len(self.bcode.regs), val=None)])
                # (the others a propagated to the right)

    def soft_grouped(self, opcode_info: typing.List[typing.Tuple[instr_id_T, int, typing.Any]]):
        # Imagine opcode info contains instructions [('SWAP1', 3, 1), ('DUP2', 1, 2),
        # (None, 0, None), ('POP', 2, None)]. Then, disjoint_cost_id_arg_tuples groups them by their associated
        # cost and in an ascendant order. In the previous example:
        # [(0, [(None, None)]), (2, [('POP', None)]), (3, [('DUP2', 2), ('SWAP1', 1)])]
        disjoint_cost_id_arg_tuples = generate_disjoint_sets_from_cost(opcode_info)
        previous_cost = 0
        or_id_arg_tuples = []
        first_set = True

        for cost, id_arg_tuples in disjoint_cost_id_arg_tuples:
            # We skip the first set of instructions, as they have
            # no soft constraint associated. Nevertheless, we add
            # opcodes with cost 0 to the set of variables till p
            if first_set:
                or_id_arg_tuples.extend(id_arg_tuples)
                previous_cost = cost
                first_set = False
                continue

            wi = cost - previous_cost

            # Before adding current associated opcodes, we generate
            # the constraints for each tj.
            for step in range(self.bcode.mlen):

                theta_in_range = select_instructions_position(step, or_id_arg_tuples, self.bcode.mlen,
                                                              self.bcode.preflen, self.bcode.sufflen)

                # Only add a constraint if any instruction satisfies the condition
                if theta_in_range:
                    self.formula.append([self.op(step, id_, arg) if arg is not None else self.op(step, id_)
                                         for id_, arg in theta_in_range], weight=wi)
            or_id_arg_tuples.extend(id_arg_tuples)

            # We update previous_cost
            previous_cost = cost

    def soft_direct(self, opcode_info: typing.List[typing.Tuple[instr_id_T, typing.Any, int]]):
        for step in range(self.bcode.mlen):
            for id_, arg, weight in opcode_info:
                # Reject <= 0 weights
                if weight <= 0:
                    continue
                # Param arg is not None if it's needed by self.op
                if arg is not None:
                    self.formula.append([-self.op(step, id_, arg)], weight=weight)
                else:
                    self.formula.append([-self.op(step, id_)], weight=weight)

    def objective(self):
        """
            Encoding the constraints on the initial and target states.
        """

        if self.options.objf == 'len':
            # maximizing the number of None's
            for step in range(self.lenlb, self.bcode.mlen):
                self.formula.append([self.op(step)], weight=1)
        elif self.options.objf == 'none':
            pass
        elif self.options.objf == 'gas':
            # adding input operations
            opcode_info = [(op, None, self.bcode.inst[op].gas) for op in self.bcode.ops
                           if self.bcode.inst[op].type in ('PUSH', 'ZERO')]

            # adding NOP instruction
            opcode_info.append((None, None, 0))

            # adding POP instruction:
            opcode_info.append(('POP', None, 2))

            # adding DUP instructions:
            for pos in range(min(self.bcode.sksz, 17) - 1):
                opcode_info.append((f'DUP{pos + 1}', pos, 3))
            # adding SWAP instructions:
            for pos in range(1, min(self.bcode.sksz, 17)):
                opcode_info.append((f'SWAP{pos}', pos, 3))

            # self.soft_grouped(opcode_info)
            self.soft_direct(opcode_info)

        elif self.options.objf == 'size':
            # adding input operations
            opcode_info = [(op, None, self.bcode.inst[op].gas) for op in self.bcode.ops
                           if self.bcode.inst[op].type in ('PUSH', 'ZERO')]

            # adding NOP instruction
            opcode_info.append((None, None, 0))

            # adding POP instruction:
            opcode_info.append(('POP', None, 1))

            # adding DUP instructions:
            for pos in range(min(self.bcode.sksz, 17) - 1):
                opcode_info.append((f'DUP{pos + 1}', pos, 1))
            # adding SWAP instructions:
            for pos in range(1, min(self.bcode.sksz, 17)):
                opcode_info.append((f'SWAP{pos}', pos, 1))

            # self.soft_grouped(opcode_info)
            self.soft_direct(opcode_info)

        else:
            assert False, 'Unknown optimisation criterion!'

    def non_empty(self):
        """
            There must be something at the top of the stack.
        """

        if self.bcode.tsta:
            for step in range(len(self.bcode.to_pop) + 1, self.bcode.mlen + 1):
                self.formula.append([-self.var(step, 0)])

    def exactly1(self):
        """
            Add Equals1 constraints.
        """

        if self.options.verbose > 1:
            szbef = len(self.formula.hard) + len(self.formula.atms)

        # first, exactly-1 constraints
        for step in range(self.bcode.mlen + 1):
            # stack state variables
            for pos in range(self.bcode.sksz):
                # taking all possible variables plus 'null'
                vars = [self.var(step, pos, val) for val in self.bcode.vars]
                e1 = CardEnc.equals(vars, vpool=self.vpool, encoding=self.options.cenc)

                # adding the new constraint to the formula
                for cl in e1.clauses:
                    self.formula.append(cl)
                for am in e1.atmosts:
                    self.formula.append(am, is_atmost=True)

            # similar stuff for locals in case of WASM programs
            if self.options.wasm:
                for pos in range(self.bcode.rgsz):
                    # taking all possible variables plus 'null'
                    vars = [self.loc(step, pos, val) for val in self.bcode.vars]
                    e1 = CardEnc.equals(vars, vpool=self.vpool, encoding=self.options.cenc)

                    # adding the new constraint to the formula
                    for cl in e1.clauses:
                        self.formula.append(cl)
                    for am in e1.atmosts:
                        self.formula.append(am, is_atmost=True)

        # same stuff but for instruction cells
        for step in range(self.bcode.mlen):
            # general instructions available as part of the input
            ops  = [self.op(step, op) for op in self.bcode.ops]

            # adding POP instruction:
            ops += [self.op(step, 'POP')]

            if not self.options.nods:
                if not self.options.wasm:  # EVM
                    # adding dup instructions:
                    ops += [self.op(step, 'DUP{0}'.format(pos + 1), pos) for pos in range(min(self.bcode.sksz, 17) - 1)]
                    # adding swap instructions:
                    ops += [self.op(step, 'SWAP{0}'.format(pos), pos) for pos in range(1, min(self.bcode.sksz, 17))]
                else:  # WASM
                    # adding get instructions:
                    ops += [self.op(step, 'LGET_{0}'.format(pos), pos) for pos in range(self.bcode.rgsz)]
                    # adding set instructions:
                    ops += [self.op(step, 'LSET_{0}'.format(pos), pos) for pos in range(self.bcode.rgsz)]
                    # adding tee instructions:
                    ops += [self.op(step, 'LTEE_{0}'.format(pos), pos) for pos in range(self.bcode.rgsz)]

            oe1 = CardEnc.equals(ops, vpool=self.vpool, encoding=self.options.cenc)
            for cl in oe1.clauses:
                self.formula.append(cl)
            for am in oe1.atmosts:
                self.formula.append(am, is_atmost=True)

        if self.options.nofocc:
            # enforcing the number of occurrences for each unique operation
            for op in self.bcode.ops:
                if self.bcode.inst[op].type in ('UNARY', 'BINARY', 'STORE', 'FCALL') or self.bcode.inst[op].large_zeroary():
                    # each unary and binary operations appears *exactly* once
                    e1 = CardEnc.equals([self.op(step, op) for step in range(self.bcode.mlen)], vpool=self.vpool, encoding=self.options.cenc)
                    for cl in e1.clauses:
                        self.formula.append(cl)
                    for am in e1.atmosts:
                        self.formula.append(am, is_atmost=True)
                    self.lenlb += 1
                elif self.bcode.inst[op].type in ('PUSH', 'ZERO'):
                    # each push appears *at least* once
                    self.formula.append([self.op(step, op) for step in range(self.bcode.mlen)])
                    self.lenlb += 1

            # if we don't want to use the lower bound:
            if not self.options.lenlb:
                self.lenlb = 0

            # enforcing the lower bound
            for step in range(self.lenlb):
                self.formula.append([-self.op(step)])

        if self.options.verbose > 1:
            szaft = len(self.formula.hard) + len(self.formula.atms)
            print('c len lb:', self.lenlb)
            print('c e1 contrib:', szaft - szbef)

    def enforce_bounds(self):
        """
            Enforce the lower and upper bound on the steps an operation can
            be performed in.
        """

        # lower bounds
        for op, plen in self.bcode.preflen.items():
            if plen:
                self.formula.append([-self.opdone(plen - 1, op)])

        # upper bounds
        for op, slen in self.bcode.sufflen.items():
            if not slen:
                continue

            if self.options.wasm and self.bcode.inst[op].small_zeroary() or \
                    not self.options.wasm and self.bcode.inst[op].type == 'PUSH':
                # PUSH can occur multiple times
                self.formula.append([self.opdone(self.bcode.mlen - slen - 1, op)])
            else:
                for step in range(self.bcode.mlen - slen, self.bcode.mlen):
                    self.formula.append([-self.op(step, op)])

    def empty_implies(self):
        """
            If a cell is None than some other cells must be None too.
        """

        if self.options.verbose > 1:
            szbef = len(self.formula.hard) + len(self.formula.atms)

        # (stack) implications to the right
        for step in range(self.bcode.mlen + 1):
            for pos in range(self.bcode.sksz - 1):
                self.formula.append([-self.var(step, pos), self.var(step, pos + 1)])

        if self.options.bprop or self.options.fprop:
            # (stack) implications on the main diagonal
            mgap = max(1, -self.bcode.mingap)
            for step in range(self.bcode.mlen):
                for pos in range(self.bcode.sksz - mgap):
                    self.formula.append([-self.var(step, pos), self.var(step + 1, pos + mgap)])

            # (stack) implications on the anti-diagonal
            # this got complicated due to the store instructions
            mgap = max(int(self.bcode.store_present), self.bcode.maxgap - 1)
            for step in range(1, self.bcode.mlen + 1):
                for pos in range(self.bcode.sksz - 1 - mgap):
                    maxp = min(self.bcode.sksz, pos + 2 + mgap)
                    self.formula.append([-self.var(step, pos)] + [self.var(step - 1, p2) for p2 in range(pos + 1, maxp)])

        # (instructions)
        for step in range(self.bcode.mlen - 1):
            self.formula.append([-self.op(step), self.op(step + 1)])

        if self.options.verbose > 1:
            szaft = len(self.formula.hard) + len(self.formula.atms)
            print('c ei contrib:', szaft - szbef)

        if self.options.wasm:
            # (locals) implications to the right
            for step in range(self.bcode.mlen + 1):
                for reg in range(self.bcode.rgsz - 1):
                    self.formula.append([-self.loc(step, reg), self.loc(step, reg + 1)])

    def instructions(self):
        """
            Step-by-step operation application.
        """

        # numbers of clauses contributed by each available instruction
        nof_cls = [0 for op in range(9 + (2 if self.options.wasm else 0))]

        # for each time step
        for step in range(self.bcode.mlen):

            # traversing all available operations
            for op in self.bcode.ops:
                # getting the full instruction spec
                inst = self.bcode.inst[op]

                if inst.type == None:  # NOP
                    nof_cls[0] += self.apply_nop(step)
                elif inst.type == 'PUSH':
                    nof_cls[2] += self.apply_push(step, inst)
                elif inst.type == 'UNARY':
                    nof_cls[3] += self.apply_unary(step, inst)
                elif inst.type == 'BINARY':
                    nof_cls[4] += self.apply_binary(step, inst)
                elif inst.type == 'FCALL':  # only for WASM programs
                    nof_cls[10] += self.apply_fcall(step, inst)
                elif inst.type == 'STORE':
                    nof_cls[7] += self.apply_store(step, inst)
                elif inst.type == 'ZERO':
                    # we are treating ZERO instructions as PUSH
                    nof_cls[8] += self.apply_push(step, inst)
                else:
                    assert False, 'Unknown operation {0}!'.format(inst.type)

            # POP aren't in the list either
            nof_cls[1] += self.apply_pop(step)

            # DUP and SWAP aren't in the list;
            # they can be applied to any position in the stack
            if not self.options.nods:
                if not self.options.wasm:
                    nof_cls[5] += self.apply_dup(step)
                    nof_cls[6] += self.apply_swap(step)
                else:
                    nof_cls[5] += self.apply_get(step)
                    nof_cls[6] += self.apply_set(step)
                    nof_cls[9] += self.apply_tee(step)

        if self.options.verbose > 1:
            if not self.options.wasm:
                print('c op contrib:', sum(nof_cls), '({0} nop, {1} pop, {2} push, {3} unary, {4} binary, {5} dup, {6} swap, {7} store, {8} zero)'.format(*nof_cls))
            else:
                print('c op contrib:', sum(nof_cls), '({0} nop, {1} pop, {2} push, {3} unary, {4} binary, {10} calls, {5} lget, {6} lset, {7} store, {8} zero, {9} ltee)'.format(*nof_cls))

    def fpropagate(self):
        """
            Do propagation of values forward.
        """

        if self.bcode.mlen > 1:
            if not self.options.wasm:
                for step in range(self.bcode.mlen):
                    for pos in range(2, self.bcode.sksz):
                        minp = max(pos - 1 - int(self.bcode.store_present), 1)
                        maxp = min(self.bcode.sksz, pos + 2)
                        for val in self.bcode.vars[1:]:
                            cl = [-self.var(step, pos, val), +self.var(step + 1, 0, val)]
                            for p2 in range(minp, maxp):
                                cl.append(+self.var(step + 1, p2, val))
                            self.formula.append(cl)
            else:
                for step in range(self.bcode.mlen):
                    for pos in range(self.bcode.maxinp, self.bcode.sksz):
                        minp = max(pos - max(self.bcode.maxgap, 1), 0)
                        maxp = min(self.bcode.sksz, pos - min(self.bcode.mingap, -1) + 1)
                        for val in self.bcode.vars[1:]:
                            cl = [-self.var(step, pos, val)]
                            for p2 in range(minp, maxp):
                                cl.append(self.var(step + 1, p2, val))
                            self.formula.append(cl)

    def bpropagate(self):
        """
            Do propagation of values backward.
        """

        if self.bcode.mlen > 1:
            if not self.options.wasm:
                for step in range(1, self.bcode.mlen + 1):
                    for pos in range(1, self.bcode.sksz):
                        minp = max(pos - 1, 1)
                        maxp = min(self.bcode.sksz, pos + 2 + int(self.bcode.store_present))
                        for val in self.bcode.vars[1:]:
                            cl = [-self.var(step, pos, val), +self.var(step - 1, 0, val)]
                            for p2 in range(minp, maxp):
                                cl.append(+self.var(step - 1, p2, val))
                            self.formula.append(cl)
            else:
                for step in range(1, self.bcode.mlen + 1):
                    for pos in range(self.bcode.maxout, self.bcode.sksz):
                        minp = max(pos + min(self.bcode.mingap, -1), 0)
                        maxp = min(self.bcode.sksz, pos + max(self.bcode.maxgap, 1) + 1)
                        for val in self.bcode.vars[1:]:
                            cl = [-self.var(step, pos, val)]
                            for p2 in range(minp, maxp):
                                cl.append(+self.var(step - 1, p2, val))
                            self.formula.append(cl)

    def lpropagate(self):
        """
            Connect register content to the past.

            1. If a value is stored in a register at a given step then it must
            have been there before or either a LSET or LTEE operation was
            applied (in this case, the previous top of the stack must have
            contained the same value).

            2. (currently not implemented) At most one change is allowed in
            the list of all registers, i.e. we cannot modify the values in
            more than 1 register at once.
        """

        if self.bcode.mlen > 1:
            # 1. a value in a register means it either was there
            # already or we have just applied LSET or LTEE operation
            for step in range(1, self.bcode.mlen + 1):
                for reg in range(self.bcode.rgsz):
                    for val in self.bcode.vars:
                        # either it was already here
                        cl = [-self.loc(step, reg, val), self.loc(step - 1, reg, val)]

                        # or he've just applied a LSET or a LTEE operation
                        self.formula.append(cl + [self.op(step - 1, 'LSET_{0}'.format(reg), reg), self.op(step - 1, 'LTEE_{0}'.format(reg), reg)])

                        # in the latter case, this value must have
                        # been at the top of the stack previously
                        self.formula.append(cl + [self.var(step - 1, 0, val)])

            # 2. at most one register can be modified at a time
            # this seems to be propagated from the semantics of LSET and LTEE
            # as well as the fact that we can apply at most one such
            # instruction at a time
            pass

    def dependencies(self):
        """
            Apply instruction dependencies.
            Also, enforce POP of unused inputs at the beginning (if any).
        """

        # popping the unused inputs
        for step in range(len(self.bcode.to_pop)):
            self.formula.append([self.op(step, 'POP')])

        # introducing all the op-done variables
        for op in self.bcode.deps_avail:
            # initial step
            self.formula.append([-self.op(0, op), +self.opdone(0, op)])
            self.formula.append([+self.op(0, op), -self.opdone(0, op)])

            # following steps
            for step in range(1, self.bcode.mlen):
                just = self.op(step, op)
                prev = self.opdone(step - 1, op)
                self.formula.append([-just, self.opdone(step, op)])
                self.formula.append([-prev, self.opdone(step, op)])
                self.formula.append([just, prev, -self.opdone(step, op)])

        # adding the dependency constraints
        for depcy in self.bcode.pdeps:
            dept, deps, gap = depcy  # dependent and dependencies
            if gap != 0:  # immediate dependency
                for step in range(gap, self.bcode.mlen):
                    cl = [self.op(step - gap, required) for required in deps]
                    self.formula.append([-self.op(step, dept)] + cl)
            else:
                for step in range(1, self.bcode.mlen):
                    cl = [self.opdone(step - 1, required) for required in deps]
                    self.formula.append([-self.opdone(step, dept)] + cl)

        # everything must be done by the end
        for op in self.bcode.deps_avail:
            self.formula.append([self.opdone(self.bcode.mlen - 1, op)])

        # the only operations before POP must be POP, SWAP, or STORE
        if self.options.pop_prev:
            pop_prev = []
            if self.bcode.store_present:
                pop_prev += [op for op in self.bcode.ops if self.bcode.inst[op].type == 'STORE']
            for step in range(1, self.bcode.mlen):
                cl  = [-self.op(step, 'POP'), self.op(step - 1, 'POP')]
                cl += [+self.op(step - 1, storeop) for storeop in pop_prev]
                if not self.options.wasm:
                    cl += [+self.op(step - 1, 'SWAP{0}'.format(pos), pos) for pos in range(1, min(self.bcode.sksz, 17))]
                else:
                    # no SWAP instructions in WASM mode
                    pass
                self.formula.append(cl)

    def forbid_dummy(self):
        """
            Forbid instructions doing nothing with the stack, unless we are at
            the end of the program. This essentially forbid occurrences of two
            consecutive empty stacks.
        """

        for step in range(self.bcode.mlen - 1):
            # if the stack is empty at a given step and the next step then
            # the only way it can happen is by applying the NOP instruction
            self.formula.append([-self.var(step, 0), -self.var(step + 1, 0), self.op(step)])

    def enforce_tail(self):
        """
            Enforce the tail to remain the same after each step.
        """

        # ignoring the first and last steps here
        for step in range(1, self.bcode.mlen - 1):
            for start in range(self.bcode.sksz - len(self.bcode.tail) + 1):
                stop = start + len(self.bcode.tail)
                for i, pos in enumerate(range(start, stop)):
                    if stop == self.bcode.sksz:
                        self.formula.append([self.var(step, stop - 1),
                                         self.var(step, pos, val=self.bcode.tail[i])])
                    else:
                        self.formula.append([-self.var(step, stop),
                                         self.var(step, stop - 1),
                                         self.var(step, pos, val=self.bcode.tail[i])])

    def shuffle_left(self, step, opvar, start_from=1, incr=1):
        """
            Do shuffling to the left in state i if a given operation is
            applied. Shuffling is applied starting from a given position.
        """

        assert step < self.bcode.mlen, 'Program length is reached!'

        for pos in range(start_from, self.bcode.sksz):
            for val in self.bcode.vars:
                self.formula.append([-opvar, -self.var(step, pos, val),  self.var(step + 1, pos - incr, val)])
                self.formula.append([-opvar,  self.var(step, pos, val), -self.var(step + 1, pos - incr, val)])

    def shuffle_right(self, step, opvar):
        """
            Do shuffling to the right in state i if a given operation is
            applied.
        """

        assert step < self.bcode.mlen, 'Program length is reached!'

        for pos in range(self.bcode.sksz - 1):
            for val in self.bcode.vars:
                self.formula.append([-opvar, -self.var(step, pos, val),  self.var(step + 1, pos + 1, val)])
                self.formula.append([-opvar,  self.var(step, pos, val), -self.var(step + 1, pos + 1, val)])

    def process_edge(self, step, opvar, incr=+1, start_from=1):
        """
            Process the edge/end of the stack depending on the operation.
            Starting from 0 is useless because having None at position 0
            is not allowed by other constraints. But starting from 2 may
            be useful, e.g. for binary operations.
        """

        if incr in (-1, -2):
            # popping a value from the stack
            for pos in range(start_from, self.bcode.sksz - 1):
                # setting Nones at the end
                for i in range(-incr):
                    self.formula.append([-opvar, self.var(step, pos), -self.var(step, pos + 1),  self.var(step + 1, pos - i)])
                # copying the last value
                for val in self.bcode.vars[1:]:
                    self.formula.append([-opvar, -self.var(step, pos, val), -self.var(step, pos + 1), self.var(step + 1, pos + incr, val)])

            # also, the last cell must contain None
            self.formula.append([-opvar, self.var(step + 1, self.bcode.sksz - 1)])

            if incr == -2:
                self.formula.append([-opvar, self.var(step + 1, self.bcode.sksz - 2)])
        elif incr == +1:
            # pushing a value to the stack
            for pos in range(start_from, self.bcode.sksz - 1):
                self.formula.append([-opvar, self.var(step, pos - 1), -self.var(step, pos), +self.var(step + 1, pos + 1)])
                # copying the last value
                for val in self.bcode.vars[1:]:
                    self.formula.append([-opvar, -self.var(step, pos - 1, val), -self.var(step, pos), self.var(step + 1, pos, val)])

            # if we are pushing, the last cell must be empty
            self.formula.append([-opvar, self.var(step, self.bcode.sksz - 1)])
        else:  # incr == 0
            # the code below should not be useful
            pass
            # # not changing stack size; None will stay None
            # for pos in range(start_from, self.bcode.sksz):
            #     self.formula.append([-opvar, -self.var(step, pos), +self.var(step + 1, pos)])
            #     self.formula.append([-opvar, +self.var(step, pos), -self.var(step + 1, pos)])

    def apply_nop(self, step):
        """
            Apply no operation to stack in state i. The result of the
            operation in state i+1 is the stack content gets unmodified.
        """

        assert step < self.bcode.mlen, 'Program length is reached!'

        # instruction variable
        opvar = self.op(step)

        nof_cls = len(self.formula.hard)

        # copying all positions in the stack to its new state
        for pos in range(self.bcode.sksz):
            for val in self.bcode.vars:
                self.formula.append([-opvar, -self.var(step, pos, val),  self.var(step + 1, pos, val)])
                self.formula.append([-opvar,  self.var(step, pos, val), -self.var(step + 1, pos, val)])

        return len(self.formula.hard) - nof_cls

    def apply_pop(self, step):
        """
            Apply POP operation to stack in state i. The result of the
            operation in state i+1 is the stack content gets shifted by one
            position to the left and the top element is popped.
        """

        assert step < self.bcode.mlen, 'Program length is reached!'

        # instruction variable
        opvar = self.op(step, 'POP')

        nof_cls = len(self.formula.hard)

        # shuffling to the left
        self.shuffle_left(step, opvar)

        if self.options.corner:
            # the last non-empty cell should contain None as a result of POP
            # here, we are excluding pos == 0 because we don't allow None at
            # the top of the stack in any of the states;
            # also, the last cell must necessarily result in None
            self.process_edge(step, opvar, incr=-1)

        return len(self.formula.hard) - nof_cls

    def apply_push(self, step, op):
        """
            Apply PUSH operation to stack in state i. The result of the
            operation in state i+1 is the stack gets shifted by one position
            to the right and a new top element is added to the left.
        """

        assert step < self.bcode.mlen, 'Program length is reached!'

        # instruction variable
        opvar = self.op(step, op.id)

        nof_cls = len(self.formula.hard)

        # the first cell in the new state must contain the pushed value
        self.formula.append([-opvar, self.var(step + 1, 0, val=op.outs[0])])

        # shuffling to the right
        self.shuffle_right(step, opvar)

        if self.options.corner:
            # propagating the edge of the stack;
            # also, the last cell must be empty
            self.process_edge(step, opvar, incr=+1)

        return len(self.formula.hard) - nof_cls

    def apply_dup(self, step):
        """
            Duplication instruction. Given an integer argument, it
            duplicates the value stored at that position by pushing it to
            the stack.
        """

        assert step < self.bcode.mlen, 'Program length is reached!'

        nof_cls = len(self.formula.hard)

        for pos in range(min(self.bcode.sksz, 17) - 1):
            # operation variable depends on the value we duplicate
            opvar = self.op(step, 'DUP{0}'.format(pos + 1), pos)

            # copying all the values
            for val in self.bcode.vars:
                self.formula.append([-opvar, -self.var(step, pos, val), +self.var(step + 1, 0, val)])
                self.formula.append([-opvar, +self.var(step, pos, val), -self.var(step + 1, 0, val)])

            # shuffling to the right
            self.shuffle_right(step, opvar)

            if self.options.corner:
                # propagating the edge of the stack;
                # also, the last cell must be empty
                self.process_edge(step, opvar, incr=+1)

        return len(self.formula.hard) - nof_cls

    def apply_swap(self, step):
        """
            Swap instruction. Given two integer arguments, it
            swaps the values stored at those positions.
        """

        assert step < self.bcode.mlen, 'Program length is reached!'

        nof_cls = len(self.formula.hard)

        # considering all possible positions up to 16
        for pos in range(1, min(self.bcode.sksz, 17)):
            # operation variable depends on the values we swap
            opvar = self.op(step, 'SWAP{0}'.format(pos), pos)

            # copying all the values
            for val in self.bcode.vars:
                # pos -> 0
                self.formula.append([-opvar, -self.var(step, pos, val), +self.var(step + 1, 0, val)])
                self.formula.append([-opvar, +self.var(step, pos, val), -self.var(step + 1, 0, val)])

                # 0 -> pos
                self.formula.append([-opvar, -self.var(step, 0, val), +self.var(step + 1, pos, val)])
                self.formula.append([-opvar, +self.var(step, 0, val), -self.var(step + 1, pos, val)])

            # copying the remaining ones
            for pos2 in range(1, self.bcode.sksz):
                if pos2 != pos:
                    for val in self.bcode.vars:
                        self.formula.append([-opvar, -self.var(step, pos2, val), +self.var(step + 1, pos2, val)])
                        self.formula.append([-opvar, +self.var(step, pos2, val), -self.var(step + 1, pos2, val)])

            if self.options.corner:
                # propagating the edge of the stack
                self.process_edge(step, opvar, incr=0)

        return len(self.formula.hard) - nof_cls

    def apply_get(self, step):
        """
            Get instruction.
        """

        assert step < self.bcode.mlen, 'Program length is reached!'

        nof_cls = len(self.formula.hard)

        # considering all possible locals
        for pos in range(self.bcode.rgsz):
            # operation variable depends on the local value we push
            opvar = self.op(step, 'LGET_{0}'.format(pos), pos)

            # copying all Boolean values from the corresponding
            # local variable to the top of the new stack state
            for val in self.bcode.vars:
                self.formula.append([-opvar, -self.loc(step, pos, val), +self.var(step + 1, 0, val)])
                self.formula.append([-opvar, +self.loc(step, pos, val), -self.var(step + 1, 0, val)])

            # shuffling to the right
            self.shuffle_right(step, opvar)

            if self.options.corner:
                # propagating the edge of the stack;
                # also, the last cell must be empty
                self.process_edge(step, opvar, incr=+1)

        return len(self.formula.hard) - nof_cls

    def apply_set(self, step):
        """
            Set instruction.
        """

        assert step < self.bcode.mlen, 'Program length is reached!'

        nof_cls = len(self.formula.hard)

        # considering all possible locals
        for pos in range(self.bcode.rgsz):
            # operation variable depends on the local value we push
            opvar = self.op(step, 'LSET_{0}'.format(pos), pos)

            # copying all Boolean values from the corresponding
            # local variable to the top of the new stack state
            for val in self.bcode.vars:
                self.formula.append([-opvar, -self.var(step, 0, val), +self.loc(step + 1, pos, val)])
                self.formula.append([-opvar, +self.var(step, 0, val), -self.loc(step + 1, pos, val)])

            # shuffling to the left
            self.shuffle_left(step, opvar)

            if self.options.corner:
                # the last non-empty cell should contain None as a result of POP
                # here, we are excluding pos == 0 because we don't allow None at
                # the top of the stack in any of the states;
                # also, the last cell must necessarily result in None
                self.process_edge(step, opvar, incr=-1)

        return len(self.formula.hard) - nof_cls

    def apply_tee(self, step):
        """
            Tee instruction.
            Same as the set instruction but without left shuffling.
        """

        assert step < self.bcode.mlen, 'Program length is reached!'

        nof_cls = len(self.formula.hard)

        # considering all possible locals
        for rpos in range(self.bcode.rgsz):
            # operation variable depends on the local value we push
            opvar = self.op(step, 'LTEE_{0}'.format(rpos), rpos)

            # copying all Boolean values from the corresponding
            # local variable to the top of the new stack state
            for val in self.bcode.vars:
                self.formula.append([-opvar, -self.var(step, 0, val),  self.loc(step + 1, rpos, val)])
                self.formula.append([-opvar,  self.var(step, 0, val), -self.loc(step + 1, rpos, val)])

            # copying all positions in the stack to its new state
            for spos in range(self.bcode.sksz):
                for val in self.bcode.vars:
                    self.formula.append([-opvar, -self.var(step, spos, val),  self.var(step + 1, spos, val)])
                    self.formula.append([-opvar,  self.var(step, spos, val), -self.var(step + 1, spos, val)])

        return len(self.formula.hard) - nof_cls

    def apply_unary(self, step, op):
        """
            Apply one of the available unary operations. As a result, the top
            element is replaced by the result of the operation while
            everything else is kept the same.
        """

        assert step < self.bcode.mlen, 'Program length is reached!'

        # instruction variable
        opvar = self.op(step, op.id)

        nof_cls = len(self.formula.hard)

        # the old top must contain the input value
        self.formula.append([-opvar, self.var(step, 0, val=op.inps[0])])

        # the new top must contain the output value
        self.formula.append([-opvar, self.var(step + 1, 0, val=op.outs[0])])

        # copying all the other positions in the stack to its new state
        for pos in range(1, self.bcode.sksz):
            for val in self.bcode.vars:
                self.formula.append([-opvar, -self.var(step, pos, val),  self.var(step + 1, pos, val)])
                self.formula.append([-opvar,  self.var(step, pos, val), -self.var(step + 1, pos, val)])

        if self.options.corner:
            # propagating the edge of the stack
            self.process_edge(step, opvar, incr=0)

        return len(self.formula.hard) - nof_cls

    def apply_binary(self, step, op):
        """
            Apply one of the available binary operations. As a result, the top
            and next top items are popped and the result of the operation is
            pushed to the stack. This way, the content of the stack is
            shuffled left.
        """

        assert step < self.bcode.mlen, 'Program length is reached!'

        # instruction variable
        opvar = self.op(step, op.id)

        nof_cls = len(self.formula.hard)

        # dealing with inputs
        if op.comm:  # commutative operation
            # the first two positions can contain either of the inputs
            self.formula.append([-opvar, self.var(step, 0, val=op.inps[0]), self.var(step, 0, val=op.inps[1])])
            self.formula.append([-opvar, self.var(step, 1, val=op.inps[0]), self.var(step, 1, val=op.inps[1])])
            self.formula.append([-opvar, self.var(step, 0, val=op.inps[0]), self.var(step, 1, val=op.inps[0])])
            self.formula.append([-opvar, self.var(step, 0, val=op.inps[1]), self.var(step, 1, val=op.inps[1])])
        else:  # non-commutative
            self.formula.append([-opvar, self.var(step, 0, val=op.inps[0])])
            self.formula.append([-opvar, self.var(step, 1, val=op.inps[1])])

        # the new top must contain the output value
        self.formula.append([-opvar, self.var(step + 1, 0, val=op.outs[0])])

        # shuffling all the remaining positions to the left
        self.shuffle_left(step, opvar, start_from=2)

        if self.options.corner:
            # propagating the edge of the stack
            self.process_edge(step, opvar, incr=-1, start_from=2)

        return len(self.formula.hard) - nof_cls

    def apply_fcall(self, step, op):
        """
            Apply one of the available function call operations. As a result,
            N top elements are used as the input to the function call and M
            new elements are pushed to the stack given the call's output.
        """

        assert step < self.bcode.mlen, 'Program length is reached!'

        # instruction variable
        opvar = self.op(step, op.id)

        nof_cls = len(self.formula.hard)

        assert not op.comm, 'Function calls are expected to be non-commutative!'

        # dealing with inputs
        for i, inp in enumerate(op.inps):
            self.formula.append([-opvar, self.var(step    , i, val=inp)])

        # dealing with outputs
        for i, inp in enumerate(op.outs):
            self.formula.append([-opvar, self.var(step + 1, i, val=inp)])

        # the difference between the numbers of inputs and outputs
        gap = len(op.inps) - len(op.outs)

        # main part of the stack should be copied
        for pos in range(len(op.inps), min(self.bcode.sksz, self.bcode.sksz + gap)):
            for val in self.bcode.vars:
                self.formula.append([-opvar, -self.var(step, pos, val),  self.var(step + 1, pos - gap, val)])
                self.formula.append([-opvar,  self.var(step, pos, val), -self.var(step + 1, pos - gap, val)])

        # remaining part of the source (or target) stack should be empty
        # here, at most one of the loops runs depending on the sign of gap
        for pos in range(self.bcode.sksz + gap, self.bcode.sksz):
            self.formula.append([-opvar, self.var(step    , pos)])
        for pos in range(self.bcode.sksz - gap, self.bcode.sksz):
            self.formula.append([-opvar, self.var(step + 1, pos)])

        return len(self.formula.hard) - nof_cls

    def apply_store(self, step, op):
        """
            Apply STORE operation to stack in state i. The result of the
            operation in state i+1 is the stack content gets shifted by two
            positions to the left and the two top elements are popped.
        """

        assert step < self.bcode.mlen, 'Program length is reached!'

        # instruction variable
        opvar = self.op(step, op.id)

        nof_cls = len(self.formula.hard)

        # shuffling to the left
        self.shuffle_left(step, opvar, start_from=2, incr=2)

        # store instructions receive two inputs and are not commutative
        self.formula.append([-opvar, self.var(step, 0, val=op.inps[0])])
        self.formula.append([-opvar, self.var(step, 1, val=op.inps[1])])

        if self.options.corner:
            # the last 2 non-empty cells should contain None as a result of
            # STORE; here, we are excluding pos == 0 because we don't allow
            # None at the top of the stack in any of the states;
            # also, the last cell must necessarily result in None
            self.process_edge(step, opvar, incr=-2, start_from=2)

        return len(self.formula.hard) - nof_cls

    def var(self, step, pos, val=None):
        """
            Stack variables.
        """

        return self.vpool.id(tuple(['var', step, pos, val]))

    def loc(self, step, pos, val=None):
        """
            Register variables.
        """

        return self.vpool.id(tuple(['loc', step, pos, val]))

    def op(self, step, opcode=None, arg=None):
        """
            Instruction variables. May receive an optional argument.
        """

        return self.vpool.id(tuple(['op', step, opcode] + ([arg] if arg is not None else [])))

    def opdone(self, step, opcode, arg=None):
        """
            Instruction is already performed at this step.
        """

        return self.vpool.id(tuple(['op-done', step, opcode] + ([arg] if arg is not None else [])))

    def anyvar(self, descr):
        """
            Get any variables based on its description as a tuple.
        """

        return self.vpool.id(descr)

    def __str__(self):
        """
            String representation of the encoding.
        """

        # creating the dummy file pointer
        dummyfp = StringIO()

        # dumping
        self.formula.to_fp(dummyfp)

        # getting the string and closing the file pointer
        result = dummyfp.getvalue()
        dummyfp.close()

        return result

    def solution(self, model, program_only=False):
        """
            Print a solution to stdout.
        """

        # the result of all the processing will be stored here
        ops = [' ' for step in range(self.bcode.mlen + 1)]
        states = [[' ' for pos in range(self.bcode.sksz)] for step in range(self.bcode.mlen + 1)]

        if self.options.wasm:
            locals = [[' ' for pos in range(self.bcode.rgsz)] for step in range(self.bcode.mlen + 1)]

        for var in model:
            if var in self.vpool.id2obj:
                obj = self.vpool.obj(var)

                if obj[0] == 'op':
                    ops[obj[1] + 1] = obj[2] if obj[2] is not None else ' '
                elif obj[0] == 'var':
                    states[obj[1]][obj[2]] = obj[3] if obj[3] is not None else ' '
                elif obj[0] == 'loc' and self.options.wasm:
                    locals[obj[1]][obj[2]] = obj[3] if obj[3] is not None else ' '

        # computing the cost of the solution
        plen, pgas, psize = 0, 0, 0
        for op in ops:
            if op != ' ':
                plen += 1
                if op == 'POP':
                    pgas += 2
                    psize += 1
                elif op.startswith('DUP') or op.startswith('SWAP') or op.startswith('LGET') or op.startswith('LSET') or op.startswith('LTEE'):
                    pgas += 3
                    psize += 1
                else:
                    pgas += self.bcode.inst[op].gas
                    psize += self.bcode.inst[op].size

        # printing the cost
        if not program_only:
            print('c cost: {0} len, {1} gas, {2} size'.format(plen, pgas, psize))

        if self.options.csv:
            print(','.join(['step', 'program'] + [''] + ['pos{0}'.format(pos) for pos in range(self.bcode.sksz)]), file=sys.stderr)
            for step in range(self.bcode.mlen + 1):
                print(','.join([str(step), ops[step]] + [''] + states[step]), file=sys.stderr)
        elif self.options.ponly or program_only:
            ops = list(map(lambda op: op if op != ' ' else 'NOP', ops[1:]))
            print('c', 'len {0}'.format(plen) if program_only else  'result', 'program: {0}'.format(','.join(ops)), flush=True)
        else:
            olen = len(max(ops, key=lambda val: len(val)))
            vlen = len(max(reduce(lambda a, b: a + b, states), key=lambda val: len(val)))
            slen = len(str(self.bcode.mlen))

            if self.options.wasm:
                rlen = len(max(reduce(lambda a, b: a + b, locals), key=lambda val: len(val)))

            print('c result program:')
            for step in range(self.bcode.mlen):
                sstr = '{0:>{width}}'.format(step, width=slen)
                if not self.options.wasm:
                    print('c', '{0}. {1:>{width}} ## [ {2} ]'.format(sstr, ops[step], ', '.join(['{0: >{width}}'.format(val, width=vlen) for val in states[step]]), width=olen))
                else:
                    print('c', '{0}. {1:>{width}} ## [ {2} ] $$ [ {3} ]'.format(sstr, ops[step], ', '.join(['{0: >{width}}'.format(val, width=vlen) for val in states[step]]), ', '.join(['{0: >{width}}'.format(val, width=rlen) for val in locals[step]]), width=olen))

            if not self.options.wasm:
                sstr = '{0:>{width}}'.format(self.bcode.mlen, width=slen)
                print('c', '{0}. {1:>{width}} ## [ {2} ]'.format(sstr, ops[-1], ', '.join(['{0: >{width}}'.format(val, width=vlen) for val in states[-1]]), width=olen))
            else:
                sstr = '{0:>{width}}'.format(self.bcode.mlen, width=slen)
                print('c', '{0}. {1:>{width}} ## [ {2} ] $$ [ {3} ]'.format(sstr, ops[-1], ', '.join(['{0: >{width}}'.format(val, width=vlen) for val in states[-1]]), ', '.join(['{0: >{width}}'.format(val, width=rlen) for val in locals[-1]]), width=olen))


    def opcode_seq(self, model):
        # the result of all the processing will be stored here
        ops = [' ' for step in range(self.bcode.mlen + 1)]

        for var in model:
            if var in self.vpool.id2obj:
                obj = self.vpool.obj(var)

                if obj[0] == 'op':
                    ops[obj[1] + 1] = obj[2] if obj[2] is not None else ' '

        return ops
