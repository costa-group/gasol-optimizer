#!/usr/bin/env python3

import json
import os
import sys
import resource
from typing import List, Dict, Tuple, Any
import traceback

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))

import itertools

output_stack_T = str
id_T = str
disasm_T = str


def get_ops_map(instructions: List[Dict[str, Any]], op: id_T) -> Dict[output_stack_T, id_T]:
    """
    Maps the output stack element from the instruction with op as a disasm to the corresponding id
    """
    return {ins['outpt_sk'][0]: ins['id'] for ins in instructions if ins['disasm'] == op}


def get_ops_id(instructions: List[Dict[str, Any]], op: id_T) -> List[id_T]:
    """
    List of instruction ids who share the same disasm field
    """
    return [ins['id'] for ins in instructions if op in ins['disasm']]


def get_deps(e, instr_map, op):
    """
    Seems to be used at no point. Ask Albert
    """
    if e not in instr_map:
        return []
    else:
        if instr_map[e]['disasm'] == op:
            return [instr_map[e]['outpt_sk'][0]]
        else:
            l = []
            for v in instr_map[e]['inpt_sk']:
                l += get_deps(v, instr_map, op)
            return l


def get_min_pos(o, deps):
    minpos = 0
    for p in deps:
        if o == p[1]:
            minpos = max(minpos, get_min_pos(p[0], deps) + 1)
    return minpos


def get_max_pos_noSTORE(o, tmax, deps, pos):
    maxpos = tmax
    for p in deps:
        if o == p[0]:
            maxpos = min(maxpos, pos[p[1]] - 1)
    return maxpos


def sort_with_deps(elems, deps, opid_instr_map, var_instr_map):
    ops = sorted(list(set([e for p in deps for e in p] + elems)))
    # print(ops)
    pos = {}
    for o in ops:
        pos[o] = get_min_pos(o, deps)
    maxpos = max(pos.values(), default=0)
    lpos = list(pos.items())
    if len(list(filter(lambda x: 'STORE' in x[0], filter(lambda x: x[1] == maxpos, pos)))) > 0:
        maxpos += 1
    poslops = {}
    possops = {}
    for p in lpos:
        if "STORE" not in p[0]:
            mpos = get_max_pos_noSTORE(p[0], maxpos, deps, pos)
            if mpos not in poslops:
                poslops[mpos] = [p[0]]
            else:
                poslops[mpos] += [p[0]]
        else:
            if p[1] not in possops:
                possops[p[1]] = [p[0]]
            else:
                possops[p[1]] = [p[0]] + possops[p[1]]
    poslops = list(poslops.items())
    poslops.sort(key=lambda x: x[0])
    possops = list(possops.items())
    possops.sort(key=lambda x: x[0])
    # print(poslops)
    # print(possops)
    opsord = []
    cur = 0
    for sop in possops:
        if sop[0] == cur:
            opsord += sop[1]
            if len(poslops) == 0 or poslops[0][0] != cur:
                cur += 1
        else:
            assert (poslops[0][0] == cur)
            assert (sop[0] == cur + 1)
            nostores = poslops[0][1]
            poslops.pop(0)
            if len(poslops) > 0 and poslops[0][0] == cur + 1:
                cur += 1
            else:
                cur += 2
            ldep = {}
            ldeps = {}
            for so in sop[1]:
                ldep[so] = []
                ldeps[so] = []
            for lo in nostores:
                for so in sop[1]:
                    if [lo, so] in deps:
                        ldep[so] += [lo]
                        # ldeps[so] += [lo]
                        vl = opid_instr_map[lo]['outpt_sk'][0]
                        args = opid_instr_map[so]['inpt_sk']
                        for v in args:
                            if needed(vl, v, var_instr_map):
                                break
                        else:
                            ldeps[so] += [lo]
            ldeps = list(ldeps.items())
            ldeps.sort()
            ldeps.sort(key=lambda x: len(x[1]))
            nostores_done = set([])
            # print(ldep)
            for sod in ldeps:
                for lop in ldep[sod[0]]:
                    # for lop in sod[1]:
                    if lop not in nostores_done:
                        opsord += [lop]
                        nostores_done.add(lop)
                opsord += [sod[0]]
    # don't add the final nostores
    final_no_store = []
    if len(poslops) > 0:
        final_no_store = [e for ll in poslops for e in ll[1]]
    return (opsord, final_no_store)


def merge(morder, sorder, final_no_mstore, final_no_sstore, opid_instr_map, var_instr_map):
    torder = []
    if len(morder) == 0:
        return sorder
    if len(sorder) == 0:
        return morder
    while len(morder) > 0:
        o = morder.pop(0)
        i = -1
        for op in final_no_sstore:
            if computed(opid_instr_map[op]['outpt_sk'][0], o, opid_instr_map, var_instr_map):
                return torder + sorder + [o] + morder
        j = len(sorder) - 1
        while j > 0:
            if "STORE" not in sorder[j] and computed(opid_instr_map[sorder[j]]['outpt_sk'][0], o, opid_instr_map,
                                                     var_instr_map):
                torder += sorder[:j + 1] + [o]
                return torder + merge(morder, sorder[j + 1:], final_no_mstore, final_no_sstore, opid_instr_map,
                                      var_instr_map)
            j -= 1
        torder += [o]
    torder += sorder
    return torder


def needed_list(v, lops, needed_set, opid_instr_map, var_instr_map):
    n = 0
    for od in lops:
        n += needed_one(v, od, needed_set, opid_instr_map, var_instr_map)
    return n


def needed_one(v, od, needed_set, opid_instr_map, var_instr_map):
    if isinstance(od, int):
        return 0
    inpts = []
    if 'STORE' in od:
        inpts += opid_instr_map[od]['inpt_sk']
    else:
        if v == od:
            return 1
        else:
            if od not in var_instr_map or od in needed_set:
                return 0
            inpts += var_instr_map[od]['inpt_sk']
    return needed_list(v, inpts, needed_set, opid_instr_map, var_instr_map)


def computed(v, od, opid_instr_map, var_instr_map):
    # checks if od needs v
    if isinstance(od, int):
        return False
    if 'STORE' in od:
        inpts = opid_instr_map[od]['inpt_sk']
    else:
        if v == od:
            return True
        else:
            if od not in var_instr_map:
                return False
            inpts = var_instr_map[od]['inpt_sk']
    for iod in inpts:
        if computed(v, iod, opid_instr_map, var_instr_map):
            return True
    return False


def remove_nostores_and_rename(torder, opid_instr_map, var_instr_map):
    final_ops = []
    while len(torder) > 0:
        op = torder.pop(0)
        if "STORE" in op:
            final_ops += [op]
        else:
            lchk = []
            lchk += final_ops
            if "SLOAD" in op:
                for o in torder:
                    if "STORE" not in o:
                        lchk += [opid_instr_map[o]['outpt_sk'][0]]
                    else:
                        lchk += [o]
                    if "SSTORE" in o:
                        break
            elif "STORE" not in op:  # MLOAD or KECCAK256
                for o in torder:
                    if "STORE" not in o:
                        lchk += [opid_instr_map[o]['outpt_sk'][0]]
                    else:
                        lchk += [o]
                    if "MSTORE" in o:
                        break
            vop = opid_instr_map[op]['outpt_sk'][0]
            for od in lchk:
                if computed(vop, od, opid_instr_map, var_instr_map):
                    break
            else:
                final_ops += [vop]
    return final_ops


def needed_nostores(msops, final_stack, opid_instr_map, var_instr_map):
    result = []
    aux = msops.copy()
    while len(aux) > 0:
        op = aux.pop(0)
        if 'STORE' not in op:
            lops = aux.copy()
            if "SLOAD" in op:
                while len(lops) > 0:
                    op1 = lops.pop(0)
                    if 'SSTORE' in op1:
                        break
            else:  # MLOAD or KECCAK256
                while len(lops) > 0:
                    op1 = lops.pop(0)
                    if 'MSTORE' in op1:
                        break
            op = opid_instr_map[op]['outpt_sk'][0]
            for op2 in lops:
                if 'STORE' not in op2:
                    op2 = opid_instr_map[op2]['outpt_sk'][0]
                if computed(op, op2, opid_instr_map, var_instr_map):
                    result += [op]
                    break
            for v in final_stack:
                if computed(op, v, opid_instr_map, var_instr_map):
                    result += [op]
                    break
    return result


def add_needed_nostores_in_stack(nostores, torder, opid_instr_map, var_instr_map, mem_order, sto_order):
    if len(nostores) == 0:
        return torder
    else:
        i = 0
        while True:
            for j in list(range(1, i)) + list(range(i + 1, len(nostores))):
                if computed(nostores[i], nostores[j], opid_instr_map, var_instr_map):
                    break
            else:
                break
            i += 1
        op = nostores[i]
        newnostores = nostores[:i] + nostores[i + 1:]
        left = []
        while len(torder) > 0:
            cur = torder.pop(0)
            if op == cur:
                left = left + [cur]
                break
            elif computed(op, cur, opid_instr_map, var_instr_map):
                left = left + [op, cur]
                break
            elif [var_instr_map[op]["id"], cur] in mem_order or [var_instr_map[op]["id"], cur] in sto_order:
                left = left + [op, cur]
                break
            elif len(torder) == 0:
                left = left + [cur, op]
            else:
                left = left + [cur]
        torder = left + torder
        return add_needed_nostores_in_stack(newnostores, torder, opid_instr_map, var_instr_map, mem_order, sto_order)


def relative_pos(s1, s2, p):
    # returns the position p in s2 (from the end) as in s1. It is negative if it does not exist
    return len(s2) - (len(s1) - p)


def needed(p0, p1, var_instr_map):
    if p0 == p1:
        return True
    if p1 not in var_instr_map:
        return False
    for n in var_instr_map[p1]['inpt_sk']:
        if needed(p0, n, var_instr_map):
            return True
    return False


class SMSgreedy:

    def __init__(self, json_format):
        self._user_instr = json_format['user_instrs']
        self._b0 = json_format["init_progr_len"]
        self._initial_stack = json_format['src_ws']
        self._final_stack = json_format['tgt_ws']

        self._mem_order = json_format['memory_dependences']
        self._sto_order = json_format['storage_dependences']
        self._original_instrs = json_format['original_instrs']
        self._var_instr_map = {}

        for ins in self._user_instr:
            if len(ins['outpt_sk']) == 1:
                self._var_instr_map[ins['outpt_sk'][0]] = ins
        self._opid_instr_map = {}
        for ins in self._user_instr:
            self._opid_instr_map[ins['id']] = ins
        self._opid_times_used = {}
        for o in self._opid_instr_map:
            if len(self._opid_instr_map[o]['outpt_sk']) == 0:
                self._opid_times_used[o] = 1
            else:
                assert (len(self._opid_instr_map[o]['outpt_sk']) == 1)
                out = self._opid_instr_map[o]['outpt_sk'][0]
                n = self._final_stack.count(out)
                for ins in self._user_instr:
                    if out in ins['inpt_sk']:
                        n += 1
                self._opid_times_used[o] = n
        for ins in self._user_instr:
            self._opid_instr_map[ins['id']] = ins
        self._needed_in_stack_map = {}
        self._dup_stack_ini = 0
        self.uses = {}

    def count_ops_one(self, o):
        if o in self.occurrences:
            self.occurrences[o] += 1
        else:
            self.occurrences[o] = 1
            if o in self._var_instr_map:
                for oi in self._var_instr_map[o]["inpt_sk"]:
                    self.count_ops_one(oi)

    def count_ops(self):
        self.occurrences = {}
        for o in self._initial_stack:
            self.occurrences[o] = 0
        lmstore = get_ops_id(self._user_instr, 'MSTORE')
        lsstore = get_ops_id(self._user_instr, 'SSTORE')
        for o in lmstore + lsstore:
            inp = self._opid_instr_map[o]["inpt_sk"]
            self.count_ops_one(inp[0])
            self.count_ops_one(inp[1])
        for o in self._final_stack:
            self.count_ops_one(o)

    def duplicate(self, o):
        if o in self._forced_in_stack:
            return True
        if o in self._initial_stack:
            return True
        if not self.small_zeroary(o):
            return True
        if not self.easy_compute(o):
            return True
        else:
            return False

    def count_uses_one(self, o):
        if o in self.uses:
            self.uses[o] += 1
        else:
            if self.duplicate(o):
                self.uses[o] = 1
            if o in self._var_instr_map:
                for oi in self._var_instr_map[o]["inpt_sk"]:
                    self.count_uses_one(oi)

    def count_uses(self):
        for o in self._initial_stack:
            self.uses[o] = 0
        lmstore = get_ops_id(self._user_instr, 'MSTORE')
        lsstore = get_ops_id(self._user_instr, 'SSTORE')
        for o in lmstore + lsstore:
            inp = self._opid_instr_map[o]["inpt_sk"]
            self.count_uses_one(inp[0])
            self.count_uses_one(inp[1])
        for o in self._final_stack:
            self.count_uses_one(o)

    def precompute(self, final_stack, stack):
        opcode = []
        opcodeids = []
        while len(stack) > 0:
            if (stack[0] not in self._needed_in_stack_map or self._needed_in_stack_map[stack[0]] == 0):
                if stack[0] in self._needed_in_stack_map:
                    self._needed_in_stack_map.pop(stack[0], None);
                stack.pop(0)
                opcode += ['POP']
                opcodeids += ['POP']
                if verbose: print('POP', stack, len(stack))
            else:
                if len(stack) > len(final_stack) and stack[0] in final_stack:
                    pos = final_stack.index(stack[0]) - len(final_stack)  # position from the end in stack
                elif len(stack) <= len(final_stack) and stack[0] in final_stack[-len(stack):]:
                    pos = final_stack[-len(stack):].index(stack[0]) - len(stack)  # position from the end in stack
                else:
                    break
                pos_in_stack = len(stack) + pos  # position in stack
                assert (pos_in_stack >= 0)
                if pos_in_stack > 16:
                    break
                if pos_in_stack == 0:
                    break
                if pos_in_stack > 0:
                    opcode += ['SWAP' + str(pos_in_stack)]
                    opcodeids += ['SWAP' + str(pos_in_stack)]
                    stack = [stack[pos_in_stack]] + stack[1:pos_in_stack] + [stack[0]] + stack[pos_in_stack + 1:]
                    if verbose: print('SWAP' + str(pos_in_stack), stack, len(stack))
        solved = []
        i = len(stack) - 1
        j = len(final_stack) - 1
        while i >= 0 and j >= 0:
            if stack[i] == final_stack[j]:
                solved += [j]
                if stack[i] in self._needed_in_stack_map:
                    assert (self._needed_in_stack_map[stack[i]] > 0)
                    if self._needed_in_stack_map[stack[i]] == 1:
                        self._needed_in_stack_map.pop(stack[i], None);
                    else:
                        self._needed_in_stack_map[stack[i]] -= 1
            i -= 1
            j -= 1
        return (opcode, opcodeids, solved, stack)

    def must_reverse(self, o, inpts, stack, needed_stack):
        if o not in self._var_instr_map:
            return True
        if not self._var_instr_map[o]['commutative']:
            return True
        if self.needs_in_stack_too_far(inpts[0], stack, needed_stack) >= 16:
            return False
        if inpts[0] in self._var_instr_map and self.small_zeroary(inpts[0]):
            return True
        if inpts[1] in self._var_instr_map and self.small_zeroary(inpts[1]):
            return False
        return True

    def compute_one_with_stack(self, o, stack, needed_stack, solved, max_to_swap):
        # print(o,stack,needed_stack,self._dup_stack_ini)
        if o in self._var_instr_map:
            if self.small_zeroary(o):
                if 'PUSH' in self._var_instr_map[o]['disasm'] and 'value' in self._var_instr_map[o]:
                    if 'tag' in self._var_instr_map[o]['disasm']:
                        tag = str(self._var_instr_map[o]['value'][0])
                        # tag = hex(self._var_instr_map[o]['value'][0])
                        # tag = tag[2:]
                        opcode = self._var_instr_map[o]['disasm']
                        opcodeid = self._var_instr_map[o]['id']
                        if verbose: print(opcode + ' ' + tag, [o] + stack, len([o] + stack))
                        self._dup_stack_ini += 1
                        return ([opcode + ' ' + tag], [opcodeid], [o] + stack)
                    else:
                        h = hex(self._var_instr_map[o]['value'][0])
                        h = h[2:]
                        n = (len(h) + 1) // 2
                        if verbose: print('PUSH' + str(n) + ' ' + h, [o] + stack, len([o] + stack))
                        opcodeid = self._var_instr_map[o]['id']
                        if "[" in self._var_instr_map[o]['disasm'] or 'data' in self._var_instr_map[o]['disasm']:
                            opcode = self._var_instr_map[o]['disasm']
                        else:
                            opcode = 'PUSH' + str(n)
                        self._dup_stack_ini += 1
                        return ([opcode + ' 0x' + h], [opcodeid], [o] + stack)
                if isinstance(o, int):
                    h = hex(o)
                    h = h[2:]
                    n = (len(h) + 1) // 2
                    if verbose: print('PUSH' + str(n) + ' ' + h, [o] + stack, len([o] + stack))
                    self._dup_stack_ini += 1
                    return (['PUSH' + str(n) + ' 0x' + h], ['PUSH' + str(n) + ' 0x' + h], [o] + stack)
                assert (len(self._var_instr_map[o]['inpt_sk']) == 0)
                opcode = self._var_instr_map[o]['disasm']
                opcodeid = self._var_instr_map[o]['id']
                self._dup_stack_ini += 1
                return ([opcode], [opcodeid], [o] + stack)
        if not (o not in needed_stack or o in stack[:16]):
            if self._dup_stack_ini == 0:
                self.clean_stack(o, stack, needed_stack, solved)
        # if not (o not in needed_stack or o in stack[:16]):
        #    print(o,stack,needed_stack,solved,self._dup_stack_ini)
        assert (o not in needed_stack or o in stack[:16])
        # print(o,stack,needed_stack)
        if o in stack and stack.index(o) < 16:
            pos = stack.index(o)
            if o in needed_stack and needed_stack[o] == 1:
                if pos < self._dup_stack_ini:
                    # it is just computed on top. Need to take the next one
                    # print(o,stack,self._dup_stack_ini,needed_stack)
                    pos = stack[self._dup_stack_ini:].index(o) + self._dup_stack_ini
                if (len(self._final_stack) - len(stack)) not in solved and (
                        len(self._final_stack) + pos - len(stack)) not in solved:
                    if self._dup_stack_ini == 0:
                        if pos == 0:
                            self._dup_stack_ini += 1
                            return ([], [], stack)
                        assert (o == stack[pos])
                        needed_stack.pop(o, None)
                        swaps = ['SWAP' + str(pos)]
                        tstack = [stack[pos]] + stack[1:pos] + [stack[0]] + stack[pos + 1:]
                        if verbose: print('SWAP' + str(pos), tstack, len(tstack))
                        self._dup_stack_ini += 1
                        return (swaps, swaps.copy(), tstack)
                    solved_before = False
                    for i in range(len(self._final_stack) + pos - len(stack) + 1):
                        if i in solved:
                            solved_before = True
                    if not solved_before:
                        assert (max_to_swap <= 16)
                        if pos < max_to_swap or len(stack) >= 16:
                            needed_stack.pop(o, None)
                            swaps = []
                            tstack = stack
                            for i in range(1, pos + 1):
                                swaps += ['SWAP' + str(i)]
                                tstack = [tstack[i]] + tstack[1:i] + [tstack[0]] + tstack[i + 1:]
                                if verbose: print('SWAP' + str(i), tstack, len(tstack))
                            for i in range(pos):
                                if len(self._final_stack) + i - len(stack) in solved:
                                    assert (False)
                                    solved.remove(len(self._final_stack) + i - len(stack))
                            self._dup_stack_ini += 1
                            return (swaps, swaps.copy(), tstack)
            if o in needed_stack:
                assert (1 <= needed_stack[o])
                needed_stack[o] -= 1
            else:
                for n in needed_stack:
                    if needed_stack[n] > 0:
                        nn = needed_one(n, o, set(needed_stack.keys()), self._opid_instr_map, self._var_instr_map)
                        assert (nn <= needed_stack[n])
                        needed_stack[n] -= nn
            if verbose: print('DUP' + str(stack.index(o) + 1), [o] + stack, len([o] + stack))
            self._dup_stack_ini += 1
            return (['DUP' + str(stack.index(o) + 1)], ['DUP' + str(stack.index(o) + 1)], [o] + stack)
        elif isinstance(o, int):
            h = hex(o)
            h = h[2:]
            n = (len(h) + 1) // 2
            if verbose: print('PUSH' + str(n) + ' ' + h, [o] + stack, len([o] + stack))
            self._dup_stack_ini += 1
            return (['PUSH' + str(n) + ' 0x' + h], ['PUSH' + str(n) + ' 0x' + h], [o] + stack)
        else:
            inpts = []
            if 'STORE' in o:
                inpts += self._opid_instr_map[o]['inpt_sk']
                opcode = self._opid_instr_map[o]['disasm']
                opcodeid = self._opid_instr_map[o]['id']
                outs = []
            elif 'PUSH' in self._var_instr_map[o]['disasm'] and 'value' in self._var_instr_map[o]:
                if 'tag' in self._var_instr_map[o]['disasm']:
                    tag = str(self._var_instr_map[o]['value'][0])
                    # tag = hex(self._var_instr_map[o]['value'][0])
                    # tag = tag[2:]
                    opcode = self._var_instr_map[o]['disasm']
                    opcodeid = self._var_instr_map[o]['id']
                    if verbose: print(opcode + ' ' + tag, [o] + stack, len([o] + stack))
                    self._dup_stack_ini += 1
                    return ([opcode + ' ' + tag], [opcodeid], [o] + stack)
                else:
                    h = hex(self._var_instr_map[o]['value'][0])
                    h = h[2:]
                    n = (len(h) + 1) // 2
                    if verbose: print('PUSH' + str(n) + ' ' + h, [o] + stack, len([o] + stack))
                    opcodeid = self._var_instr_map[o]['id']
                    if "[" in self._var_instr_map[o]['disasm'] or 'data' in self._var_instr_map[o]['disasm']:
                        opcode = self._var_instr_map[o]['disasm']
                    else:
                        opcode = 'PUSH' + str(n)
                    self._dup_stack_ini += 1
                    return ([opcode + ' 0x' + h], [opcodeid], [o] + stack)
            else:
                inpts += self._var_instr_map[o]['inpt_sk']
                opcode = self._var_instr_map[o]['disasm']
                opcodeid = self._var_instr_map[o]['id']
                outs = self._var_instr_map[o]['outpt_sk']
                # print(opcodeid,inpts,outs)
            if len(inpts) == 2 and len(stack) >= 2 and self._dup_stack_ini == 0:
                op1, op2 = stack[0], stack[1]
                pos0_in_final = len(self._final_stack) - len(stack)
                if pos0_in_final not in solved and pos0_in_final + 1 not in solved:
                    if inpts == [op1, op2] or (
                            o in self._var_instr_map and self._var_instr_map[o]['commutative'] and inpts == [op2, op1]):
                        if op1 in needed_stack and needed_stack[op1] == 1:
                            if op2 in needed_stack and needed_stack[op2] == 1:
                                # print("Applied!")
                                needed_stack.pop(op1, None)
                                needed_stack.pop(op2, None)
                                self._dup_stack_ini += 1
                                if verbose: print(opcode, stack, len(stack))
                                return ([opcode], [opcodeid], outs + stack[len(inpts):])
            if len(inpts) == 2 and len(stack) >= 1 and self._dup_stack_ini == 0:
                op = stack[0]
                pos0_in_final = len(self._final_stack) - len(stack)
                if pos0_in_final not in solved:
                    if o in self._var_instr_map and self._var_instr_map[o]['commutative'] and inpts[0] == op:
                        if op in needed_stack and needed_stack[op] == 1:
                            needed_stack.pop(op, None)
                            self._dup_stack_ini += 1
                            # print("Applied2!",opcodeid,inpts[1],stack)
                            (opcodes, opcodeids, stack) = self.compute_one_with_stack(inpts[1], stack, needed_stack,
                                                                                      solved, max_to_swap)
                            opcodes += [opcode]
                            opcodeids += [opcodeid]
                            self._dup_stack_ini -= len(inpts)
                            self._dup_stack_ini += len(outs)
                            stack = outs + stack[len(inpts):]
                            if verbose: print(opcode, stack, len(stack))
                            return (opcodes, opcodeids, stack)
            if self.must_reverse(o, inpts, stack, needed_stack):
                inpts.reverse()
            (opcodes, opcodeids, stack) = self.compute_with_stack(inpts, stack, needed_stack, solved, max_to_swap)
            inpts.reverse()
            for i in range(len(inpts)):
                assert (inpts[i] == stack[i])
            opcodes += [opcode]
            opcodeids += [opcodeid]
            stack = outs + stack[len(inpts):]
            self._dup_stack_ini -= len(inpts)
            self._dup_stack_ini += len(outs)
            if verbose: print(opcode, stack, len(stack))
            if (o in needed_stack and o not in stack[1:]):
                # first time computed inside the term --> ERROR
                assert (False)
            return (opcodes, opcodeids, stack)

    def compute_with_stack(self, instr, stack, needed_stack, solved, max_to_swap):
        opcodes = []
        opcodeids = []
        for o in instr:
            (nopcodes, nopcodeids, stack) = self.compute_one_with_stack(o, stack, needed_stack, solved, max_to_swap)
            opcodes += nopcodes
            opcodeids += nopcodeids
        return (opcodes, opcodeids, stack)

    def choose_element(self, solved, cstack, needed_stack):
        # print(solved,cstack,self._final_stack)
        if len(cstack) > 0 and len(self._final_stack) - len(cstack) not in solved:
            # if cstack[0] (exists and) is not solved
            pos = len(self._final_stack) - 1
            posc = -1
            while len(cstack) + posc >= 0 and pos >= 0:
                if pos not in solved:
                    if self._final_stack[pos] == cstack[0]:
                        # print("case 0",posc)
                        return (0, posc)  # position in cstack (negative) SWAP if different
                pos -= 1
                posc -= 1
        # up_top_in_final = len(self._final_stack)-len(cstack)-1
        # if up_top_in_final> 0 and up_top_in_final not in solved and cstack.count(self._final_stack[up_top_in_final]) < self._final_stack.count(self._final_stack[up_top_in_final]):
        #    print("case 1",pos)
        #    return (1,up_top_in_final) #position in final_stack (positive): build and no need to swap
        pos = len(self._final_stack) - 1
        while pos >= 0:
            # print(pos,self._final_stack[pos],cstack.count(self._final_stack[pos]),
            if pos not in solved and cstack.count(self._final_stack[pos]) < self._final_stack.count(
                    self._final_stack[pos]):
                ns = self.needs_in_stack_too_far(self._final_stack[pos], cstack, needed_stack)
                pos1 = pos - 1
                while pos1 >= 0 and len(cstack) + pos1 - len(self._final_stack) >= 0:
                    if pos1 not in solved and cstack.count(self._final_stack[pos1]) < self._final_stack.count(
                            self._final_stack[pos1]):
                        # it is a candidate
                        ns1 = self.needs_in_stack_too_far(self._final_stack[pos1], cstack, needed_stack)
                        if ns <= ns1 and 15 <= ns1 and ns1 <= 16:
                            pos = pos1
                            break
                    pos1 -= 1
                # print("case 1",pos)
                return (1, pos)  # position in final_stack (positive): build and swap if needed
            pos -= 1

        # print(cstack,self._final_stack)
        # assert(len(cstack) == len(self._final_stack))
        for e in self._final_stack:
            assert (cstack.count(e) == self._final_stack.count(e))
        # assert(0 in solved)
        return (2, 0)  # We are in the permutation case

    def stack_too_long(self, stack, mem, needed_stack):
        i = len(stack) - 1
        num_no_store = 0
        for o in mem:
            if "STORE" not in o:
                num_no_store += 1
        while (i + num_no_store >= 15):
            num_no_store_aux = num_no_store
            j = len(mem) - 1
            while j > 0:
                if "STORE" not in mem[j]:
                    num_no_store_aux -= 1
                if stack[i] not in stack[:i]:
                    if needed_one(stack[i], mem[j], needed_stack, self._opid_instr_map, self._var_instr_map):
                        if i + num_no_store_aux >= 15:
                            # print("too long",stack[i],mem[j],stack,mem,needed_stack)
                            return True
                j -= 1
            i -= 1
        return False

    def needs_in_stack_too_far(self, o, stack, needed_stack):
        i = len(stack) - 1
        while (i >= 0):
            if stack[i] not in stack[:i]:
                if needed_one(stack[i], o, needed_stack, self._opid_instr_map, self._var_instr_map):
                    return i + 1
            i -= 1
        return 0

    def clean_stack(self, o, stack, needed_stack, solved):
        ops = []
        i = 0
        if self.needs_in_stack_too_far(o, stack, needed_stack) <= 14:
            return ([], stack, needed_stack)
        while i < len(stack) and len(stack) >= 10:
            while i < len(stack) and (len(self._final_stack) + i - len(stack)) not in solved:
                if stack[i] in needed_stack and needed_stack[stack[i]] == 0:
                    break
                i += 1
            if i < len(stack) and (len(self._final_stack) + i - len(stack)) not in solved:
                opr = stack[i]
                # print("Enter:",opr,stack,needed_stack,solved)
                ops += ['SWAP' + str(i)]
                stack = [stack[i]] + stack[1:i] + [stack[0]] + stack[i + 1:]
                if verbose: print('SWAP' + str(i), stack, len(stack))
                ops += ['POP']
                stack.pop(0)
                if verbose: print('POP', stack, len(stack))
                needed_stack.pop(opr, None)
                # print("Exit:",opr,stack,needed_stack,solved)
            else:
                break
        return (ops, stack, needed_stack)

    def pre_compute_list(self, o, cstack, cneeded_in_stack_map, lord):
        if o in cstack:
            return
        assert (o not in self._initial_stack)
        if 'STORE' in o:
            inpts = self._opid_instr_map[o]['inpt_sk']
        else:
            inpts = self._var_instr_map[o]['inpt_sk']
        for op in inpts:
            self.pre_compute_list(op, cstack, cneeded_in_stack_map, lord)
        if o not in lord and o in cneeded_in_stack_map:
            lord.append(o)

    def compute_pre_list(self, lord, cstack, cneeded_in_stack_map, solved, max_to_swap):
        opcodes = []
        opcodeids = []
        for op in lord:
            # print("computing:", op)
            (ops, cstack, cneeded_in_stack_map) = self.clean_stack(op, cstack, cneeded_in_stack_map, solved)
            opcodes += ops
            opcodeids += ops
            inpts = self._var_instr_map[op]['inpt_sk']
            opcode = self._var_instr_map[op]['disasm']
            opcodeid = self._var_instr_map[op]['id']
            outs = self._var_instr_map[op]['outpt_sk']
            if self.must_reverse(op, inpts, cstack, cneeded_in_stack_map):
                inpts.reverse()
            self._dup_stack_ini = 0
            (popcodes, popcodeids, cstack) = self.compute_with_stack(inpts, cstack, cneeded_in_stack_map, solved,
                                                                     max_to_swap)
            inpts.reverse()
            for i in range(len(inpts)):
                assert (inpts[i] == cstack[i])
            opcodes += popcodes
            opcodes += [opcode]
            opcodeids += popcodeids
            opcodeids += [opcodeid]
            cstack = outs + cstack[len(inpts):]
            if verbose: print(opcode, cstack, len(cstack))
        return (opcodes, opcodeids, cstack)

    def compute_memory_op(self, o, cstack, cneeded_in_stack_map, solved, max_to_swap):
        # print("memory",o)
        opcodes = []
        opcodeids = []
        lord = []
        self.pre_compute_list(o, cstack, cneeded_in_stack_map, lord)
        (popcodes, popcodeids, cstack) = self.compute_pre_list(lord, cstack, cneeded_in_stack_map, solved, max_to_swap)
        opcodes += popcodes
        opcodeids += popcodeids
        if 'STORE' not in o:
            assert (lord[-1] == o)  # means o was not in stack before and now it's computed
        else:
            # print("finally computing:", o)
            # Now we have to compute o
            (ops, cstack, cneeded_in_stack_map) = self.clean_stack(o, cstack, cneeded_in_stack_map, solved)
            opcodes += ops
            opcodeids += ops
            self._dup_stack_ini = 0
            (popcodes, popcodeids, cstack) = self.compute_one_with_stack(o, cstack, cneeded_in_stack_map, solved,
                                                                         max_to_swap)
            opcodes += popcodes
            opcodeids += popcodeids
        return (opcodes, opcodeids, cstack)

    def compute_regular_op(self, o, cstack, cneeded_in_stack_map, solved, max_to_swap):
        # print("regular",o,cstack)
        opcodes = []
        opcodeids = []
        lord = []
        self.pre_compute_list(o, cstack, cneeded_in_stack_map, lord)
        # print(o,lord)
        (popcodes, popcodeids, cstack) = self.compute_pre_list(lord, cstack, cneeded_in_stack_map, solved, max_to_swap)
        opcodes += popcodes
        opcodeids += popcodeids
        if o not in lord:
            # print("finally computing:", o)
            (ops, cstack, cneeded_in_stack_map) = self.clean_stack(o, cstack, cneeded_in_stack_map, solved)
            opcodes += ops
            opcodeids += ops
            self._dup_stack_ini = 0
            (popcodes, popcodeids, cstack) = self.compute_one_with_stack(o, cstack, cneeded_in_stack_map, solved,
                                                                         max_to_swap)
            opcodes += popcodes
            opcodeids += popcodeids
        return (opcodes, opcodeids, cstack)

    def compute(self, instr, final_no_store, opcodes_ini, opcodeids_ini, solved, initial, max_to_swap):
        # print(solved)
        # print('new initial stack:',initial)
        # print('final_stack:', self._final_stack)
        # print('store ops:',instr)
        # print(self._needed_in_stack_map)
        topcodes = []
        topcodeids = []
        cstack = initial
        cneeded_in_stack_map = self._needed_in_stack_map.copy()
        # print("before store")
        # print(solved)
        # print(self._final_stack)
        # print(cstack)
        # print(cneeded_in_stack_map)
        case = 0
        while case != 2:
            # print("enter",cstack,cneeded_in_stack_map,self._final_stack,solved)
            # print(solved)
            while len(cstack) > 0 and (cstack[0] not in cneeded_in_stack_map or cneeded_in_stack_map[cstack[0]] == 0):
                if (len(self._final_stack) - len(cstack)) in solved:
                    break
                topcodes += ['POP']
                topcodeids += ['POP']
                cstack.pop(0)
                if verbose: print('POP', cstack, len(cstack))
            if (len(instr) > 0 and "STORE" in instr[0]) or self.stack_too_long(cstack, instr,
                                                                               set(cneeded_in_stack_map.keys())):
                case = 3
            else:
                (case, pos) = self.choose_element(solved, cstack, cneeded_in_stack_map)
                # print('case:', case, pos)
            if case == 0:
                # pos in cstack (negative)
                if (cstack[0] == cstack[pos]):
                    # solved but not in solved list
                    assert (len(self._final_stack) + pos not in solved)
                    solved += [len(self._final_stack) + pos]
                else:
                    pos_in_stack = len(cstack) + pos
                    assert (pos_in_stack > 0 and pos_in_stack <= 16)
                    topcodes += ['SWAP' + str(pos_in_stack)]
                    topcodeids += ['SWAP' + str(pos_in_stack)]
                    lens = len(cstack)
                    cstack = [cstack[pos_in_stack]] + cstack[1:pos_in_stack] + [cstack[0]] + cstack[pos_in_stack + 1:]
                    if verbose: print('SWAP' + str(pos_in_stack), cstack, len(cstack))
                    assert (lens == len(cstack))
            elif case == 1:
                before_store = False
                # pos in final_stack
                o = self._final_stack[pos]
                # print(o,"case1")
                i = len(instr) - 1
                while i >= 0:
                    if "STORE" not in instr[i]:
                        if computed(instr[i], o, self._opid_instr_map, self._var_instr_map):
                            break
                    i -= 1
                j = len(final_no_store) - 1
                while j >= 0:
                    if computed(final_no_store[j], o, self._opid_instr_map, self._var_instr_map):
                        break
                    j -= 1
                if i >= 0 or j >= 0:
                    # print("in instr",o,i)
                    if j >= 0:
                        p = len(instr)
                        final_no_store = []
                    else:
                        if instr[i] == o:
                            p = i
                            for i in range(p, len(instr)):
                                if "STORE" in instr[i]:
                                    before_store = True
                                    break
                            instr = instr[:p] + instr[p + 1:]  # remove the operation
                        else:
                            p = i + 1
                    for op in instr[:p]:
                        # print("previous",op,cneeded_in_stack_map)
                        # print(cstack)
                        self._dup_stack_ini = 0
                        (opcodes, opcodeids, cstack) = self.compute_memory_op(op, cstack, cneeded_in_stack_map, solved,
                                                                              max_to_swap)
                        topcodes += opcodes
                        topcodeids += opcodeids
                    instr = instr[p:]
                    if len(instr) == 0:
                        final_no_store = []
                    # c print('current stack:',cstack)
                # now we perform the operation
                self._dup_stack_ini = 0
                # print("compute", o)
                if before_store:
                    (opcodes, opcodeids, cstack) = self.compute_memory_op(o, cstack, cneeded_in_stack_map, solved,
                                                                          max_to_swap)
                else:
                    (opcodes, opcodeids, cstack) = self.compute_regular_op(o, cstack, cneeded_in_stack_map, solved,
                                                                           max_to_swap)
                topcodes += opcodes
                topcodeids += opcodeids
                pos_in_stack = len(cstack) + pos - len(self._final_stack)
                assert (pos_in_stack >= 0 and pos_in_stack <= 16)
                solved += [pos]
                if pos_in_stack > 0:
                    topcodes += ['SWAP' + str(pos_in_stack)]
                    topcodeids += ['SWAP' + str(pos_in_stack)]
                    lens = len(cstack)
                    cstack = [cstack[pos_in_stack]] + cstack[1:pos_in_stack] + [cstack[0]] + cstack[pos_in_stack + 1:]
                    if verbose: print('SWAP' + str(pos_in_stack), cstack, len(cstack))
                    assert (lens == len(cstack))
            elif case == 3:
                o = instr.pop(0)
                # print(o)
                self._dup_stack_ini = 0
                (opcodes, opcodeids, cstack) = self.compute_memory_op(o, cstack, cneeded_in_stack_map, solved,
                                                                      max_to_swap)
                topcodes += opcodes
                topcodeids += opcodeids
            else:  # case 2
                # print("remaining:",instr)
                assert (len(instr) == 0 or "STORE" in instr[-1])
                # print("final:",instr)
                if len(instr) > 0:  # needs to continue after performing all store ops
                    case = 0
                for o in instr:
                    # print(o,cneeded_in_stack_map)
                    # print(cstack)
                    opcodes = []
                    opcodeids = []
                    self._dup_stack_ini = 0
                    (opcodes, opcodeids, cstack) = self.compute_memory_op(o, cstack, cneeded_in_stack_map, solved,
                                                                          max_to_swap)
                    while len(cstack) > 0 and (
                            cstack[0] not in cneeded_in_stack_map or cneeded_in_stack_map[cstack[0]] == 0):
                        if (len(self._final_stack) - len(cstack)) in solved:
                            break
                        opcodes += ['POP']
                        opcodeids += ['POP']
                        cstack.pop(0)
                        # s print('POP',cstack,len(cstack))
                    topcodes += opcodes
                    topcodeids += opcodeids
                instr = []
        # print('current stack:',cstack)
        # print('final stack:',self._final_stack)
        # print(solved)
        while cstack != self._final_stack:
            # invariant
            assert (len(cstack) == len(self._final_stack))
            for e in cstack:
                assert (cstack.count(e) == self._final_stack.count(e))
            assert (0 in solved)
            i = 1
            while i < len(cstack) - 1 and i in solved:
                i += 1
            # print(i,cstack,self._final_stack,solved)
            assert (i not in solved)
            assert (i <= 16)
            topcodes += ['SWAP' + str(i)]
            topcodeids += ['SWAP' + str(i)]
            lens = len(cstack)
            cstack = [cstack[i]] + cstack[1:i] + [cstack[0]] + cstack[i + 1:]
            assert (lens == len(cstack))
            # s print('SWAP'+str(i),cstack,len(cstack))
            solved.remove(0)
            while 0 not in solved:
                i = 0
                while i in solved or cstack[0] != self._final_stack[i]:
                    i += 1
                if i > 0:
                    assert (i < len(cstack))
                    assert (i <= 16)
                    topcodes += ['SWAP' + str(i)]
                    topcodeids += ['SWAP' + str(i)]
                    lens = len(cstack)
                    cstack = [cstack[i]] + cstack[1:i] + [cstack[0]] + cstack[i + 1:]
                    assert (lens == len(cstack))
                    # s print('SWAP'+str(i),cstack,len(cstack))
                solved += [i]
        assert (cstack == self._final_stack)
        # print("end",cstack,cneeded_in_stack_map)
        return (opcodes_ini + topcodes, opcodeids_ini + topcodeids)

    def target(self):
        # mloadmap = get_ops_map(self._user_instr,'MLOAD')
        # print(mloadmap)
        # sloadmap = get_ops_map(self._user_instr,'SLOAD')
        # print(sloadmap)
        lmstore = get_ops_id(self._user_instr, 'MSTORE')
        # print(lmstore)
        lsstore = get_ops_id(self._user_instr, 'SSTORE')
        # print(lsstore)
        # dep_target_mem = []
        # for e in self._final_stack:
        #    l = get_deps(e,self._var_instr_map,'MLOAD')
        #    dep_target_mem += list(map(lambda x: [mloadmap[x],e], l))
        # print("dep_target:",dep_target_mem)
        (morder, final_no_mstore) = sort_with_deps(lmstore, self._mem_order, self._opid_instr_map, self._var_instr_map)
        # dep_target_str = []
        # for e in self._final_stack:
        #    l = get_deps(e,self._var_instr_map,'SLOAD')
        #    dep_target_str += map(lambda x: [sloadmap[x],e], l)
        # print(dep_target_str)
        (sorder, final_no_sstore) = sort_with_deps(lsstore, self._sto_order, self._opid_instr_map, self._var_instr_map)
        # print(self._mem_order)
        # print(morder)
        # print(final_no_mstore)
        # print()
        # print(self._sto_order)
        # print(sorder)
        # print(final_no_sstore)
        # print()
        torder = merge(morder, sorder, final_no_mstore, final_no_sstore, self._opid_instr_map, self._var_instr_map)
        # print(torder)
        final_no_store = []
        for o in final_no_mstore + final_no_sstore:
            final_no_store += [self._opid_instr_map[o]['outpt_sk'][0]]
        # print('torder:',torder)
        needed_nostores_in_stack = needed_nostores(torder, self._final_stack, self._opid_instr_map, self._var_instr_map)
        self._forced_in_stack = set(needed_nostores_in_stack)
        needed_nostores_in_stack = sorted(list(self._forced_in_stack))
        # print('forced:',self._forced_in_stack)
        # print('needed:',needed_nostores_in_stack)
        torder = remove_nostores_and_rename(torder, self._opid_instr_map, self._var_instr_map)
        torder = add_needed_nostores_in_stack(needed_nostores_in_stack, torder, self._opid_instr_map,
                                              self._var_instr_map, self._mem_order, self._sto_order)
        # print("after:",torder)
        for o in needed_nostores_in_stack:
            assert (o in torder)
        # final_ops_to_count = torder.copy()
        # final_ops_full = torder + self._final_stack
        # for o in self._final_stack:
        #    if o not in needed_nostores_in_stack:
        #        final_ops_to_count += [o]
        final_ops_to_count = self._final_stack.copy()
        for o in torder:
            if o not in needed_nostores_in_stack:
                final_ops_to_count += [o]
        # print(final_ops_full)
        # print("foc:",final_ops_to_count)
        # print("nns:",needed_nostores_in_stack)
        needed_set = set([])
        for v in needed_nostores_in_stack:
            self._needed_in_stack_map[v] = 0
        for v in self._initial_stack:
            self._needed_in_stack_map[v] = 0
        needed_set = set(self._needed_in_stack_map.keys())
        # print("needed:",needed_set)
        for v in needed_nostores_in_stack:
            # self._needed_in_stack_map[v] = needed_list(v,final_ops_full,needed_set,self._opid_instr_map,self._var_instr_map)-1
            # for w in final_ops_to_count:
            #    print(v,"in",w,needed_one(v,w,self._opid_instr_map,self._var_instr_map))
            # print(v)
            self._needed_in_stack_map[v] += needed_list(v, final_ops_to_count, needed_set, self._opid_instr_map,
                                                        self._var_instr_map)
            for w in needed_set:
                self._needed_in_stack_map[w] += needed_list(w, self._var_instr_map[v]['inpt_sk'], needed_set,
                                                            self._opid_instr_map, self._var_instr_map)

        # print('needed in stack:',self._needed_in_stack_map,final_ops_to_count)
        for v in self._initial_stack:
            self._needed_in_stack_map[v] += needed_list(v, final_ops_to_count, needed_set, self._opid_instr_map,
                                                        self._var_instr_map)
        self.count_uses()
        # print("target")
        # print(self._needed_in_stack_map)
        # print(self.uses)
        to_remove = set([])
        for o in self.uses.keys():
            if o not in self._needed_in_stack_map and self.uses[o] == 1:
                to_remove.add(o)
        for o in to_remove:
            self.uses.pop(o, None)
        assert (set(self._needed_in_stack_map.keys()).issubset(set(self.uses.keys())))
        for o in self._needed_in_stack_map:
            self._needed_in_stack_map[o] <= self.uses[o]
        # print(self.uses)
        self._needed_in_stack_map = self.uses  # we don't want to recompute
        # print(self._needed_in_stack_map)
        # assert(sorted(list(self._needed_in_stack_map.items())) == sorted(list(self.uses.items())))
        # print('initial stack:  ', self._initial_stack)
        return (torder, final_no_store)
        # sort_dep(lm,self._mem_order)
        # sort_dep(ls,self._sto_order)
        # all_time_deps = compute_time_deps(lm++self._variables,self._mem_order,)
        # uses_per_val = compute_uses(lm++self._variables)

    def small_zeroary(self, op):
        return op in self._var_instr_map and len(self._var_instr_map[op]['inpt_sk']) == 0 and self._var_instr_map[op][
            'size'] <= 2

    def tree_size(self, op):
        if op not in self._var_instr_map:
            assert (op in self._initial_stack)
            return 1
        n = 1
        for ch in self._var_instr_map[op]['inpt_sk']:
            n += self.tree_size(ch)
        return n

    def easy_compute(self, op):
        # return True
        if op not in self._var_instr_map:
            return True
        if self._var_instr_map[op]['gas'] >= 15:
            return False
        for ch in self._var_instr_map[op]['inpt_sk']:
            if not self.easy_compute(ch):
                return False
        if self.tree_size(op) >= 3:
            return False
        return True

    def accept(self, l: List[id_T]) -> bool:
        for i in range(len(l)):
            if l[i] in self._opid_instr_map:
                if len(self._opid_instr_map[l[i]]['outpt_sk']) == 1:
                    v = self._opid_instr_map[l[i]]['outpt_sk'][0]
                else:
                    v = ""
                if len(self._opid_instr_map[l[i]]['inpt_sk']) == 0 and not self.small_zeroary(v):
                    if l.count(l[i]) > 1:
                        # print("Cas1:",l[i])
                        return False
        return True

    def correct(self, l: List[id_T]) -> bool:
        for i in range(len(l)):
            if l[i] in self._opid_instr_map:
                if len(self._opid_instr_map[l[i]]['outpt_sk']) == 1:
                    v = self._opid_instr_map[l[i]]['outpt_sk'][0]
                else:
                    v = ""
                if len(self._opid_instr_map[l[i]]['inpt_sk']) >= 1 or not self.small_zeroary(v):
                    if l.count(l[i]) > 1:
                        # print("Cas1:",l[i])
                        return False
                if len(self._opid_instr_map[l[i]]['inpt_sk']) == 1:
                    arg1 = self._opid_instr_map[l[i]]['inpt_sk'][0]
                    if arg1 in self._var_instr_map:
                        assert (i > 0)
                        o1 = self._var_instr_map[arg1]['id']
                        if self._opid_times_used[o1] == 1 and l[i - 1] != o1:
                            # print("Cas2",l[i])
                            return False
                        if self.small_zeroary(arg1) and l[i - 1] != o1:
                            # print("Cas3",l[i])
                            return False
                elif len(self._opid_instr_map[l[i]]['inpt_sk']) == 2:
                    arg1 = self._opid_instr_map[l[i]]['inpt_sk'][0]
                    arg2 = self._opid_instr_map[l[i]]['inpt_sk'][1]
                    # print(l[i],arg1,arg2)
                    if arg1 in self._var_instr_map:
                        o1 = self._var_instr_map[arg1]['id']
                    else:
                        o1 = ""
                    if arg2 in self._var_instr_map:
                        o2 = self._var_instr_map[arg2]['id']
                    else:
                        o2 = ""
                    if self._opid_instr_map[l[i]]['commutative']:
                        if o1 != "" and o2 != "":
                            assert (i > 1)
                            if self._opid_times_used[o1] == 1 and self._opid_times_used[o2] == 1:
                                if l[i - 1] != o1 and l[i - 1] != o2:
                                    # print("Cas4",l[i])
                                    return False
                        if o1 != "" and self.small_zeroary(arg1):
                            if l[i - 1] != o1:
                                # print("Cas5",l[i])
                                return False
                            if o2 != "" and self.small_zeroary(arg2):
                                if l[i - 2] != o2:
                                    # print("Cas6",l[i])
                                    return False
                        elif o2 != "" and self.small_zeroary(arg2):
                            if l[i - 1] != o2:
                                # print("Cas7",l[i])
                                return False
                    else:
                        if o1 != "" and self.small_zeroary(arg1):
                            if l[i - 1] != o1:
                                # print("Cas8",l[i])
                                return False
                            if o2 != "" and (self.small_zeroary(arg2) or self._opid_times_used[o2] == 1):
                                if l[i - 2] != o2:
                                    # print("Cas9",l[i])
                                    return False
                        elif o1 != "" and self._opid_times_used[o1] == 1:
                            if l[i - 1] != o1:
                                # print("Cas10",l[i])
                                return False
        return True


def greedy_from_json(json_data: Dict[str, Any], verb=False) -> Tuple[Dict[str, Any], SMSgreedy, List[str], List[str], int]:
    try:
        encoding = SMSgreedy(json_data.copy())
        # print(encoding._var_instr_map)
        # print()
        # print(encoding._opid_instr_map)
        # print(encoding._mem_order)
        # print(encoding._sto_order)
        global verbose
        verbose = verb
        (instr, final_no_store) = encoding.target()
        # print("before pre:",encoding._needed_in_stack_map,encoding._initial_stack)

        (opcodes_ini, opcodeids_ini, solved, initial) = encoding.precompute(encoding._final_stack.copy(),
                                                                            encoding._initial_stack.copy())
        # print("after pre:",encoding._needed_in_stack_map,initial,opcodeids_ini,solved)
        solved_aux = solved.copy()
        needed_in_stack_aux = encoding._needed_in_stack_map.copy()
        opcodes_ini_aux = opcodes_ini.copy()
        opcodeids_ini_aux = opcodeids_ini.copy()
        instr_aux = instr.copy()
        final_no_store_aux = final_no_store.copy()
        (res, resids) = encoding.compute(instr, final_no_store, opcodes_ini, opcodeids_ini, solved, initial, 3)
        # encoding._needed_in_stack_map = needed_in_stack_aux
        # (res1, resids1) = encoding.compute(instr_aux, final_no_store_aux, opcodes_ini_aux, opcodeids_ini_aux, solved_aux, initial, 2)
        # if len(res) > len(res1):
        #    res = res1
        #    resids = resids1
        assert (len(res) == len(resids))
        if encoding.accept(resids):
            # print(name, encoding._b0, len(res))
            # print(res)
            # print(resids)
            if len(res) < encoding._b0 or (len(res) <= encoding._b0 and encoding.correct(resids)):
                json_data["init_progr_len"] = len(res)
                json_data["original_instrs"] = str(res).replace(",", "")[1:-1].replace("\'", "")
                if encoding.correct(resids):
                    # print('correct:', resids)
                    json_data["original_code_with_ids"] = resids
                else:
                    # print('incorrect:', resids)
                    if "original_code_with_ids" in json_data:
                        json_data.pop("original_code_with_ids", None)
        else:
            pass
            # print(name, encoding._b0, encoding._b0)
        error = 0
    except Exception:
        # _, _, tb = sys.exc_info()
        # traceback.print_tb(tb)
        # print("Error")
        res = None
        resids = None
        # print(name,encoding._b0,0 )
        error = 1

    return json_data, encoding, res, resids, error


def minsize_from_json(json_data: Dict[str, Any]) -> int:
    encoding = SMSgreedy(json_data.copy())
    # print(encoding._initial_stack)
    encoding.count_ops()
    # print(encoding.occurrences)
    s = len(get_ops_id(encoding._user_instr, 'MSTORE')) + len(get_ops_id(encoding._user_instr, 'SSTORE'))
    for i in encoding.occurrences:
        if i in encoding._initial_stack:
            # if less uses than occurrences we need to pop
            # if more uses than occurrences we need to dup
            s += abs(encoding.occurrences[i] - encoding._initial_stack.count(i))
        else:
            s += encoding.occurrences[i]
    return s

def greedy_standalone(sms: Dict) -> Tuple[str, float, List[str]]:
    """
    Executes the greedy algorithm as a standalone configuration. Returns whether the execution has been
    sucessful or not ("non_optimal" or "error"), the total time and the sequence of ids returned.
    """
    usage_start = resource.getrusage(resource.RUSAGE_SELF)
    try:
        print("AA")
        json_info, _, _, seq_ids, error = greedy_from_json(sms)
        usage_stop = resource.getrusage(resource.RUSAGE_SELF)
    except:
        usage_stop = resource.getrusage(resource.RUSAGE_SELF)
        error = 1
        seq_ids = []
    optimization_outcome = "error" if error == 1 else "non_optimal"
    return optimization_outcome, usage_stop.ru_utime + usage_stop.ru_stime - usage_start.ru_utime - usage_start.ru_stime, seq_ids


if __name__ == "__main__":
    with open(sys.argv[1]) as f:
        json_read = json.load(f)

    initial_size = json_read['init_progr_len']

    # minst = minsize_from_json(json_read)

    name = sys.argv[1]
    if '/' in name:
        p = len(name) - 1 - list(reversed(name)).index('/')
        name = name[p + 1:]

    json_info, encod, rs, rsids, error = greedy_from_json(json_read)  # ,True) if verbose

    # if error == 0:
    #    print(name, "m:", minst, "g:", len(rs), "e:", error)
    # else:
    #    print(name, "m:", minst, "g:", 0, "e:", error)
    # assert(error != 0 or len(rs) >= minst)
    # exit(0)

    json_result = json.dumps(json_info)
    checker_name = ""
    output_name = ""
    if len(sys.argv) > 2:
        if os.path.isfile(sys.argv[2]):
            checker_name = sys.argv[2]
        else:
            output_name = sys.argv[2] + "/" + name
    if len(sys.argv) > 3:
        if checker_name == "":
            checker_name = sys.argv[3]
        else:
            output_name = sys.argv[3] + "/" + name
    if output_name != "":
        with open(output_name, 'w') as fw:
            fw.write(json_result)
    else:
        if error == 0:
            print(name, initial_size, len(rs))
            # print(rs)
            # print(rsids)
        else:
            print(name, initial_size, 0)
        # print(len(rs),rs,error)
        # print(json_result)
    if checker_name != "" and error == 0:
        print("generating files...")
        with open("auxtemp1.evm", 'w') as fw1:
            fw1.write(encod._original_instrs)
            fw1.close()
        with open("auxtemp2.evm", 'w') as fw2:
            for bc in rs:
                fw2.write(bc + "\n")
            fw2.close()
        os.system("python3 " + checker_name + " auxtemp1.evm auxtemp2.evm")
        os.system("rm -f auxtemp1.evm")
        os.system("rm -f auxtemp2.evm")
