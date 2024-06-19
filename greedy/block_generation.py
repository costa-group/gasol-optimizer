#!/usr/bin/env python3
import collections
import json
import os
import sys
import resource
from typing import List, Dict, Tuple, Any, Set, Union
import traceback

sys.path.append(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))

import itertools

var_T = str
id_T = str
disasm_T = str
instr_T = Dict[str, Any]
var_instr_map_T = Dict[var_T, instr_T]
opid_instr_map_T = Dict[var_T, instr_T]

VERBOSE = 0


def get_ops_map(instructions: List[Dict[str, Any]], op: id_T) -> Dict[var_T, id_T]:
    """
    Maps the output current_stack element from the instruction with op as a disasm to the corresponding id
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


def get_min_pos(o: id_T, deps: List[Tuple[id_T, id_T]], pos: Dict[id_T, int]) -> int:
    """
    Obtains the minimum position instruction o can appear according to deps. Stores the result in the dict pos
    """
    if o in pos:
        return pos[o]
    minpos = 0
    for p in deps:
        if o == p[1]:
            minpos = max(minpos, get_min_pos(p[0], deps, pos) + 1)
    pos[o] = minpos
    return minpos


def compute_min_pos(ops: List[id_T], deps: List[Tuple[id_T, id_T]]) -> Dict[id_T, int]:
    """
    Computes a dict to store the lowest position in which the ids in ops can appear according to deps
    """
    pos = {}
    for o in ops:
        get_min_pos(o, deps, pos)
    return pos


def get_max_pos_noSTORE(o: id_T, tmax: int, deps: List[Tuple[id_T, id_T]], pos: Dict[id_T, int]):
    """
    Get minimum position in which the no-Store operation can appear in a sequence
    """
    maxpos = tmax
    for p in deps:
        if o == p[0]:
            maxpos = min(maxpos, pos[p[1]] - 1)
    return maxpos


def compute_pos_ops(deps: List[Tuple[id_T, id_T]], pos: Dict[id_T, int]) -> Tuple[
    List[Tuple[int, List[id_T]]], List[Tuple[int, List[id_T]]]]:
    """
    Computes two dicts to associate each position with the set of variables that can appear in that position: one for
    store operations and another for other instructions (LOADs or KECCAKs)
    """
    poslops = collections.defaultdict(lambda: [])
    possops = collections.defaultdict(lambda: [])

    maxpos = max(pos.values(), default=0)

    # Condition: one of the instructions that appear in the last available position is a STORE instruction
    # TODO: ask Albert why you need to add one
    if len(list(filter(lambda x: 'STORE' in x[0], filter(lambda x: x[1] == maxpos, pos)))) > 0:
        maxpos += 1

    # Traverse the items in pos to associate a instruction to them
    for p in pos.items():
        if "STORE" not in p[0]:
            # TODO: ask Albert
            mpos = get_max_pos_noSTORE(p[0], maxpos, deps, pos)
            poslops[mpos] += [p[0]]
        else:
            possops[p[1]] = [p[0]] + possops[p[1]]

    poslops = list(poslops.items())
    poslops.sort(key=lambda x: x[0])
    possops = list(possops.items())
    possops.sort(key=lambda x: x[0])

    return possops, poslops


def compatible_order(possops: List[Tuple[int, List[id_T]]], poslops: List[Tuple[int, List[id_T]]],
                     deps: List[Tuple[id_T, id_T]], opid_instr_map: opid_instr_map_T,
                     var_instr_map: var_instr_map_T) -> Tuple[List[id_T], List[id_T]]:
    """
    Returns a compatible order to perform the memory operations (with their ids) and the list of no store operations
    """

    # Final order in which instructions must be performed
    opsord = []

    # Relative position to poslops and possops that is being considered
    cur = 0

    # Traverse all STORE instructions
    for sop in possops:
        if sop[0] == cur:
            opsord += sop[1]
            # If there are no LOAD operations, then increment the current counter
            if len(poslops) == 0 or poslops[0][0] != cur:
                cur += 1
        else:
            # Current index corresponds to the first element in poslops
            assert (poslops[0][0] == cur)

            # The following store instruction
            assert (sop[0] == cur + 1)

            # No store = Loads + Keccaks
            nostores = poslops[0][1]

            # Remove first element in poslops
            poslops.pop(0)

            # There is a no-store instruction whose position is cur + 1
            if len(poslops) > 0 and poslops[0][0] == cur + 1:
                cur += 1
            # TODO: STORE instructions is incremented by 2 at each step. Find out why
            else:
                cur += 2

            ldep = {}
            ldeps = {}

            # Traverse all the instructions whose position was current
            for so in sop[1]:
                ldep[so] = []
                ldeps[so] = []

            # Traverse all ids that are not stored from current
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

    return opsord, final_no_store


def sort_with_deps(elems: List[id_T], deps: List[Tuple[id_T, id_T]],
                   opid_instr_map: opid_instr_map_T, var_instr_map: var_instr_map_T):
    # Include all the ids in the list elems and that appear as part of the dependencies
    ops = sorted(list(set([e for p in deps for e in p] + elems)))
    pos = compute_min_pos(ops, deps)

    possops, poslops = compute_pos_ops(deps, pos)
    return compatible_order(possops, poslops, deps, opid_instr_map, var_instr_map)


def merge(morder, sorder, final_no_mstore, final_no_sstore, opid_instr_map: opid_instr_map_T,
          var_instr_map: var_instr_map_T):
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


def needed_list(v: Union[var_T, instr_T], lops: List[var_T], needed_set: Set[var_T], opid_instr_map: opid_instr_map_T,
                var_instr_map: var_instr_map_T) -> int:
    """
    Given a list of stack vars, returns how many of them are needed
    """
    n = 0
    for od in lops:
        n += needed_one(v, od, needed_set, opid_instr_map, var_instr_map)
    return n


def needed_one(v: var_T, od: var_T, needed_set: Set[var_T], opid_instr_map: opid_instr_map_T,
               var_instr_map: var_instr_map_T) -> int:
    """
    Checks the number of times od needs v, unless od is in needed_set or is a initial stack variable
    """
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


def computed(v: var_T, od: Union[var_T, id_T], opid_instr_map: opid_instr_map_T, var_instr_map: var_instr_map_T) -> int:
    """
    Checks if od needs v. od can be either a stack variable or a STORE instruction (i.e. instruction that produces
    no value)
    """
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


def remove_nostores_and_rename(torder, opid_instr_map: opid_instr_map_T, var_instr_map: var_instr_map_T):
    """

    """
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


def needed_nostores(msops: List[id_T], final_stack: List[var_T], opid_instr_map: opid_instr_map_T,
                    var_instr_map: var_instr_map_T):
    """
    Given a list of ids and the final stack, returns the no store operations that must be kept in the stack, as they
    must not be recomputed.
    """
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
            # For STORE operations
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


def add_needed_nostores_in_stack(nostores, torder, opid_instr_map: opid_instr_map_T, var_instr_map: var_instr_map_T,
                                 mem_order, sto_order):
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


def needed(p0: var_T, p1: var_T, var_instr_map: Dict[var_T, instr_T]):
    if p0 == p1:
        return True
    if p1 not in var_instr_map:
        return False
    for n in var_instr_map[p1]['inpt_sk']:
        if needed(p0, n, var_instr_map):
            return True
    return False


def _compute_var_total_uses(final_stack: List[var_T], user_instrs: List[instr_T]) -> Dict[var_T, int]:
    """
    Computes how many times each var appears either in the final stack, in the final locals or as a subterm
    of other terms.
    """
    var_uses = collections.defaultdict(lambda: 0)

    # Count vars in the final stack
    for var_stack in final_stack:
        var_uses[var_stack] += 1

    # Count vars as input of other instrs
    for instr in user_instrs:
        for subterm_var in instr['inpt_sk']:
            var_uses[subterm_var] += 1

    return var_uses


class SMSgreedy:

    def __init__(self, json_format):
        self._bs = json_format['max_sk_sz']
        self._user_instr = json_format['user_instrs']
        self._b0 = json_format["init_progr_len"]
        self._initial_stack = json_format['src_ws']
        self._final_stack = json_format['tgt_ws']
        self._variables = json_format['vars']
        self._current_cost = json_format['current_cost']
        self._mem_order = json_format['memory_dependences']
        self._sto_order = json_format['storage_dependences']
        self._original_instrs = json_format['original_instrs']

        # Maps vars to the corresponding instruction
        self._var_instr_map = {}
        for ins in self._user_instr:
            for var in ins['outpt_sk']:
                self._var_instr_map[var] = ins

        # Maps ids to the corresponding instruction
        self._opid_instr_map = {}
        for ins in self._user_instr:
            self._opid_instr_map[ins['id']] = ins

        # Maps variables to the number of times that are being used
        self._var_times_used = _compute_var_total_uses(self._final_stack, self._user_instr)
        self._needed_in_stack_map = {}

        # Dup stack ini: where the elements that are computed beforehand are placed
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

    def duplicate(self, o: var_T):
        """
        Given a stack element, returns True if such element must be duplicated.
        Cases: a LOAD instruction, initial stack elements, and terms that are not small zero ary or easy to
        compute
        """
        return o in self._forced_in_stack or o in self._initial_stack or not self.small_zeroary(
            o) or not self.easy_compute(o)

    def count_uses_one(self, o: var_T):
        """
        Annotates how many times an element
        """
        if o in self.uses:
            self.uses[o] += 1
        else:
            # If it must be duplicated, the number of uses is set to one initially
            # TODO: ask Albert
            if self.duplicate(o):
                self.uses[o] = 1
            if o in self._var_instr_map:

                # Recursively count how many times it must be computed
                for oi in self._var_instr_map[o]["inpt_sk"]:
                    self.count_uses_one(oi)

    def count_uses(self):
        """
        Counts how many times every element is being used
        """
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

    def precompute(self, final_stack: List[var_T], current_stack: List[var_T]) -> Tuple[
        List[str], List[id_T], List[var_T], List[var_T]]:
        """
        Given the initial and final stack, starts removing elements and swapping them bas much as possible (i.e. until
        an operation is forced to be chosen). Returns the list of opcodes, the list of ids, the positions that are solved
        and the current stack after performing such operations
        """
        opcode = []
        opcodeids = []

        # Try to perform as much operations as possible
        while len(current_stack) > 0:

            # Remove elements that are not needed and update needed in stack accordingly
            if current_stack[0] not in self._needed_in_stack_map or self._needed_in_stack_map[current_stack[0]] == 0:
                if current_stack[0] in self._needed_in_stack_map:
                    self._needed_in_stack_map.pop(current_stack[0], None)
                current_stack.pop(0)
                opcode += ['POP']
                opcodeids += ['POP']
                if VERBOSE > 0: print('POP', current_stack, len(current_stack))
            else:
                if len(current_stack) > len(final_stack) and current_stack[0] in final_stack:
                    pos = final_stack.index(current_stack[0]) - len(
                        final_stack)  # position from the end in current_stack
                elif len(current_stack) <= len(final_stack) and current_stack[0] in final_stack[-len(current_stack):]:
                    pos = final_stack[-len(current_stack):].index(current_stack[0]) - len(
                        current_stack)  # position from the end in current_stack
                else:
                    break
                pos_in_stack = len(current_stack) + pos  # position in current_stack
                assert (pos_in_stack >= 0)
                if pos_in_stack > 16:
                    break
                if pos_in_stack == 0:
                    break
                if pos_in_stack > 0:
                    opcode += ['SWAP' + str(pos_in_stack)]
                    opcodeids += ['SWAP' + str(pos_in_stack)]
                    current_stack = [current_stack[pos_in_stack]] + current_stack[1:pos_in_stack] + [
                        current_stack[0]] + current_stack[pos_in_stack + 1:]
                    if VERBOSE > 0: print('SWAP' + str(pos_in_stack), current_stack, len(current_stack))
        solved = []
        i = len(current_stack) - 1
        j = len(final_stack) - 1

        # Determine which operations are solved and update needed in stack accordingly
        while i >= 0 and j >= 0:
            if current_stack[i] == final_stack[j]:
                solved += [j]
                if current_stack[i] in self._needed_in_stack_map:
                    assert (self._needed_in_stack_map[current_stack[i]] > 0)
                    if self._needed_in_stack_map[current_stack[i]] == 1:
                        self._needed_in_stack_map.pop(current_stack[i], None)
                    else:
                        self._needed_in_stack_map[current_stack[i]] -= 1
            i -= 1
            j -= 1
        return opcode, opcodeids, solved, current_stack

    def must_reverse(self, o: Union[var_T, id_T], inpts: List[var_T], stack: List[var_T], needed_stack: Dict):
        """
        We only alter the order of the arguments (return False) if the operation o is commutative and
        (i) either computing the first argument requires an element too deep in the stack
        (ii) the second argument is a small nullary element and the first one isn't
        """
        # STORE operations have fixed order
        if o not in self._var_instr_map:
            return True
        # If it is not commutative, then we have a fixed order as well
        if not self._var_instr_map[o]['commutative']:
            return True
        #
        if self.needs_in_stack_too_far(inpts[0], stack, needed_stack) >= 16:
            return False

        # If it has a small nullary variable as the first element, then we keep the
        # same order
        if inpts[0] in self._var_instr_map and self.small_zeroary(inpts[0]):
            return True
        # If it has a small nullary variable as the second element, then we change the order
        if inpts[1] in self._var_instr_map and self.small_zeroary(inpts[1]):
            return False
        return True

    def compute_one_with_stack(self, o: Union[var_T, id_T], stack: List[var_T], needed_stack: Dict, solved: List[int],
                               max_to_swap: int):
        # print(o,current_stack,needed_stack,self._dup_stack_ini)
        if VERBOSE > 1:
            print("Compute one with stack")
            print(o, stack, needed_stack, solved)
            print("")

        # O produces an element
        if o in self._var_instr_map:

            # If it is a small zero ary, we just compute it directly
            if self.small_zeroary(o):
                if 'PUSH' in self._var_instr_map[o]['disasm'] and 'value' in self._var_instr_map[o]:
                    if 'tag' in self._var_instr_map[o]['disasm']:
                        tag = str(self._var_instr_map[o]['value'][0])
                        # tag = hex(self._var_instr_map[o]['value'][0])
                        # tag = tag[2:]
                        opcode = self._var_instr_map[o]['disasm']
                        opcodeid = self._var_instr_map[o]['id']
                        if VERBOSE > 0: print(opcode + ' ' + tag, [o] + stack, len([o] + stack))
                        self._dup_stack_ini += 1
                        return ([opcode + ' ' + tag], [opcodeid], [o] + stack)
                    else:
                        h = hex(self._var_instr_map[o]['value'][0])
                        h = h[2:]
                        n = (len(h) + 1) // 2
                        if VERBOSE > 0: print('PUSH' + str(n) + ' ' + h, [o] + stack, len([o] + stack))
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
                    if VERBOSE > 0: print('PUSH' + str(n) + ' ' + h, [o] + stack, len([o] + stack))
                    self._dup_stack_ini += 1
                    return (['PUSH' + str(n) + ' 0x' + h], ['PUSH' + str(n) + ' 0x' + h], [o] + stack)
                assert (len(self._var_instr_map[o]['inpt_sk']) == 0)
                opcode = self._var_instr_map[o]['disasm']
                opcodeid = self._var_instr_map[o]['id']
                self._dup_stack_ini += 1
                return ([opcode], [opcodeid], [o] + stack)

        # We try to clean the stack if there are too many elements to access o
        if not (o not in needed_stack or o in stack[:16]):
            if self._dup_stack_ini == 0:
                self.clean_stack(o, stack, needed_stack, solved)
        # if not (o not in needed_stack or o in current_stack[:16]):
        #    print(o,current_stack,needed_stack,solved,self._dup_stack_ini)
        assert (o not in needed_stack or o in stack[:16])
        # print(o,current_stack,needed_stack)

        # If the element o is already in the stack and is accessible
        if o in stack and stack.index(o) < 16:
            pos = stack.index(o)

            # o is only needed once more
            if o in needed_stack and needed_stack[o] == 1:

                # Ignore the one that has just been computed
                if pos < self._dup_stack_ini:
                    # it is just computed on top. Need to take the next one
                    # print(o,current_stack,self._dup_stack_ini,needed_stack)
                    pos = stack[self._dup_stack_ini:].index(o) + self._dup_stack_ini

                # Neither the top element nor current elements are solved
                if (len(self._final_stack) - len(stack)) not in solved and (
                        len(self._final_stack) + pos - len(stack)) not in solved:
                    if self._dup_stack_ini == 0:
                        if pos == 0:
                            self._dup_stack_ini += 1
                            return ([], [], stack)
                        assert (o == stack[pos])
                        needed_stack.pop(o, None)
                        #                        print("here")
                        swaps = ['SWAP' + str(pos)]
                        tstack = [stack[pos]] + stack[1:pos] + [stack[0]] + stack[pos + 1:]
                        if VERBOSE > 0: print('SWAP' + str(pos), tstack, len(tstack))
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
                                #                                print("here1")
                                swaps += ['SWAP' + str(i)]
                                tstack = [tstack[i]] + tstack[1:i] + [tstack[0]] + tstack[i + 1:]
                                if VERBOSE > 0: print('SWAP' + str(i), tstack, len(tstack))
                            for i in range(pos):
                                if len(self._final_stack) + i - len(stack) in solved:
                                    assert (False)
                                    solved.remove(len(self._final_stack) + i - len(stack))
                            self._dup_stack_ini += 1
                            return (swaps, swaps.copy(), tstack)

            # o must be kept in the stack
            if o in needed_stack:
                assert (1 <= needed_stack[o])
                needed_stack[o] -= 1
            else:
                for n in needed_stack:
                    if needed_stack[n] > 0:
                        nn = needed_one(n, o, set(needed_stack.keys()), self._opid_instr_map, self._var_instr_map)
                        assert (nn <= needed_stack[n])
                        needed_stack[n] -= nn
            if VERBOSE > 0:
                print('DUP' + str(stack.index(o) + 1), [o] + stack, len([o] + stack))

            self._dup_stack_ini += 1
            return ['DUP' + str(stack.index(o) + 1)], ['DUP' + str(stack.index(o) + 1)], [o] + stack

        elif isinstance(o, int):
            h = hex(o)
            h = h[2:]
            n = (len(h) + 1) // 2
            if VERBOSE > 0: print('PUSH' + str(n) + ' ' + h, [o] + stack, len([o] + stack))
            self._dup_stack_ini += 1
            return ['PUSH' + str(n) + ' 0x' + h], ['PUSH' + str(n) + ' 0x' + h], [o] + stack
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
                    if VERBOSE > 0: print(opcode + ' ' + tag, [o] + stack, len([o] + stack))
                    self._dup_stack_ini += 1
                    return ([opcode + ' ' + tag], [opcodeid], [o] + stack)
                else:
                    h = hex(self._var_instr_map[o]['value'][0])
                    h = h[2:]
                    n = (len(h) + 1) // 2
                    if VERBOSE > 0: print('PUSH' + str(n) + ' ' + h, [o] + stack, len([o] + stack))
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
                                if VERBOSE > 0: print(opcode, stack, len(stack))
                                return [opcode], [opcodeid], outs + stack[len(inpts):]
            if len(inpts) == 2 and len(stack) >= 1 and self._dup_stack_ini == 0:
                op = stack[0]
                pos0_in_final = len(self._final_stack) - len(stack)
                if pos0_in_final not in solved:
                    if o in self._var_instr_map and self._var_instr_map[o]['commutative'] and inpts[0] == op:
                        if op in needed_stack and needed_stack[op] == 1:
                            needed_stack.pop(op, None)
                            self._dup_stack_ini += 1
                            # print("Applied2!",opcodeid,inpts[1],current_stack)
                            (opcodes, opcodeids, stack) = self.compute_one_with_stack(inpts[1], stack, needed_stack,
                                                                                      solved, max_to_swap)
                            opcodes += [opcode]
                            opcodeids += [opcodeid]
                            self._dup_stack_ini -= len(inpts)
                            self._dup_stack_ini += len(outs)
                            stack = outs + stack[len(inpts):]
                            if VERBOSE > 0: print(opcode, stack, len(stack))
                            return (opcodes, opcodeids, stack)
            if o in self._var_instr_map and self._var_instr_map[o]['commutative']:
                inpts.reverse()
                (opcodes, opcodeids, stack) = self.compute_with_stack_permut(inpts, stack, needed_stack, solved,
                                                                             max_to_swap)
            else:
                if self.must_reverse(o, inpts, stack, needed_stack):
                    inpts.reverse()
                    (opcodes, opcodeids, stack) = self.compute_with_stack(inpts, stack, needed_stack, solved,
                                                                          max_to_swap)
                inpts.reverse()
                for i in range(len(inpts)):
                    assert (inpts[i] == stack[i])
            opcodes += [opcode]
            opcodeids += [opcodeid]
            stack = outs + stack[len(inpts):]
            self._dup_stack_ini -= len(inpts)
            self._dup_stack_ini += len(outs)
            if VERBOSE > 0: print(opcode, stack, len(stack))
            if (o in needed_stack and o not in stack[1:]):
                # first time computed inside the term --> ERROR
                assert (False)
            return (opcodes, opcodeids, stack)

    def compute_with_stack_permut(self, inpts, stack, needed_stack, solved, max_to_swap):
        if VERBOSE > 1:
            print("Compute with stack permut")
            print("Inputs", inpts)
            print("Stack", stack)
            print("Needed stack", needed_stack),
            print("Solved", solved)
            print("Dup stack ini", self._dup_stack_ini)
            print("")
        opcodes = []
        opcodeids = []
        i = 0
        while i < len(inpts):
            if self._dup_stack_ini == i and i < len(stack) and stack[i] in inpts[i:]:
                op = stack[i]
                p = inpts[i:].index(op)
                p += i
                i_in_final = len(self._final_stack) - len(stack) - i
                if i_in_final not in solved:
                    if op in needed_stack and needed_stack[op] == 1:
                        needed_stack.pop(op, None)
                        self._dup_stack_ini += 1
                        inpts[p] = inpts[i]
                        inpts[i] = op
                        i += 1
                        continue
            nopcodes, nopcodeids, stack = self.compute_one_with_stack(inpts[i], stack, needed_stack, solved,
                                                                      max_to_swap)
            opcodes += nopcodes
            opcodeids += nopcodeids
            i += 1
        return opcodes, opcodeids, stack

    def compute_with_stack(self, instr, stack, needed_stack, solved, max_to_swap):
        opcodes = []
        opcodeids = []
        for o in instr:
            (nopcodes, nopcodeids, stack) = self.compute_one_with_stack(o, stack, needed_stack, solved, max_to_swap)
            opcodes += nopcodes
            opcodeids += nopcodeids
        return (opcodes, opcodeids, stack)

    def choose_element(self, solved, cstack, needed_stack) -> Tuple[int, int]:
        """

        Glosary for cases:
        -> 0: current top of the stack is not solved and can be placed in their position. This position is expressed
          as a negative number.
        -> 1: choose an element in the final stack (pos)
        -> 2: there are no elements left in the stack to compute
        """
        # print(solved,cstack,self._final_stack)

        # Condition: there is an element in the stack and position 0 is not solved
        if len(cstack) > 0 and len(self._final_stack) - len(cstack) not in solved:
            # if cstack[0] (exists and) is not solved
            # Pos: traverses the final stack
            pos = len(self._final_stack) - 1
            posc = -1

            # Condition: there are enough elements in final stack to place the corresponding value
            while len(cstack) + posc >= 0 and pos >= 0:
                if pos not in solved:
                    if self._final_stack[pos] == cstack[0]:
                        # print("case 0",posc)
                        return 0, posc  # position in cstack (negative) SWAP if different
                pos -= 1
                posc -= 1
        # up_top_in_final = len(self._final_stack)-len(cstack)-1
        # if up_top_in_final> 0 and up_top_in_final not in solved and cstack.count(self._final_stack[up_top_in_final]) < self._final_stack.count(self._final_stack[up_top_in_final]):
        #    print("case 1",pos)
        #    return (1,up_top_in_final) #position in final_stack (positive): build and no need to swap
        pos = len(self._final_stack) - 1

        # Traversing the final stack (condition: there is at least one element to compute)
        while pos >= 0:
            # print(pos,self._final_stack[pos],cstack.count(self._final_stack[pos]),

            # Condition: current position is not solved and the corresponding stack element that must be placed has
            # not been computed the number needed of times
            if pos not in solved and cstack.count(self._final_stack[pos]) < self._final_stack.count(
                    self._final_stack[pos]):
                ns = self.needs_in_stack_too_far(self._final_stack[pos], cstack, needed_stack)
                pos1 = pos - 1
                while pos1 >= 0 and len(cstack) + pos1 - len(self._final_stack) >= 0:

                    # Same as the outer condition for pos1
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
        return 2, 0  # We are in the permutation case

    def stack_too_long(self, stack: List[var_T], mem: List[Union[var_T, id_T]], needed_stack: Set[var_T]):
        """
        Checks if there is an element in the stack (starting from the bottom) that must be used as part of a memory
        element and is inaccessible (considering the intermediate non-store operations in between take space as well)
        """
        i = len(stack) - 1
        num_no_store = 0

        # Count no STORE operations left to compute
        for o in mem:
            if "STORE" not in o:
                num_no_store += 1

        # Checks if there is an element deeper than 16,
        # considering that the non-store operations in between must be computed
        while i + num_no_store >= 15:
            num_no_store_aux = num_no_store
            j = len(mem) - 1
            while j > 0:
                # Substract one to the count of non-store operations
                if "STORE" not in mem[j]:
                    num_no_store_aux -= 1
                # TODO: this condition could be placed outside to avoid checking a concrete i
                # If there is a shallower element, then there is no problem
                if stack[i] not in stack[:i]:

                    # If the element in stack i needs mem[j], it means t
                    if needed_one(stack[i], mem[j], needed_stack, self._opid_instr_map, self._var_instr_map):
                        if i + num_no_store_aux >= 15:
                            # print("too long",current_stack[i],mem[j],current_stack,mem,needed_stack)
                            return True
                j -= 1
            i -= 1
        return False

    def needs_in_stack_too_far(self, o, stack, needed_stack) -> int:
        """
        Traverses the element in the stack to find the deepest element that o uses
        """
        i = len(stack) - 1
        while i >= 0:
            # Last time element stack[i] appears in the stack
            if stack[i] not in stack[:i]:
                # needed_one != 0 => stack[i] does not appear in o
                if needed_one(stack[i], o, needed_stack, self._opid_instr_map, self._var_instr_map):
                    return i + 1
            i -= 1
        return 0

    def clean_stack(self, o: Union[var_T, id_T], stack: List[var_T], needed_stack: Dict, solved: List[int]) -> Tuple[
        List[id_T], List[var_T], Dict]:
        """
        If the next operation requires an element that is too deep in the stack (> position 14), we traverse the stack to remove elements that are
        no longer needed.
        """
        ops = []
        i = 0

        # If the deepest element has distance up to 14, then we do not need to do changes
        if self.needs_in_stack_too_far(o, stack, needed_stack) <= 14:
            return [], stack, needed_stack

        # Traverse all the elements in the stack unless it reaches less than 10 elements at some points
        while i < len(stack) and len(stack) >= 10:

            # Search for an element that is not solved in the final stack
            while i < len(stack) and (len(self._final_stack) + i - len(stack)) not in solved:

                # Exit if the corresponding element is not needed anywhere else
                if stack[i] in needed_stack and needed_stack[stack[i]] == 0:
                    break
                i += 1

            # Condition: if the previous while has existed due to the if condition
            if i < len(stack) and (len(self._final_stack) + i - len(stack)) not in solved:
                opr = stack[i]
                # print("Enter:",opr,current_stack,needed_stack,solved)
                ops += ['SWAP' + str(i)]
                stack = [stack[i]] + stack[1:i] + [stack[0]] + stack[i + 1:]
                if VERBOSE > 0: print('SWAP' + str(i), stack, len(stack))
                ops += ['POP']
                stack.pop(0)
                if VERBOSE > 0: print('POP', stack, len(stack))
                needed_stack.pop(opr, None)
                # print("Exit:",opr,current_stack,needed_stack,solved)
            else:
                break
        return ops, stack, needed_stack

    def pre_compute_list(self, o: Union[var_T, id_T], cstack: List[var_T], cneeded_in_stack_map: Dict, lord: List):
        """
        Determines the subterms in o that are part of cneed_in_stack_map, in the corresponding order (deepest first)
        """
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

    def compute_pre_list(self, lord: List[var_T], cstack: List[var_T],
                         cneeded_in_stack_map: Dict, solved: List[int], max_to_swap: int):
        """
        Computes the list of elements in lord
        """
        opcodes = []
        opcodeids = []
        for op in lord:
            # print("computing:", op)

            # First we remove the elements that are no longer needed if the stack is too large
            ops, cstack, cneeded_in_stack_map = self.clean_stack(op, cstack, cneeded_in_stack_map, solved)
            opcodes += ops
            opcodeids += ops
            inpts = self._var_instr_map[op]['inpt_sk']
            opcode = self._var_instr_map[op]['disasm']
            opcodeid = self._var_instr_map[op]['id']
            outs = self._var_instr_map[op]['outpt_sk']

            # Elements can be reversed
            if self.must_reverse(op, inpts, cstack, cneeded_in_stack_map):
                inpts.reverse()
            self._dup_stack_ini = 0
            popcodes, popcodeids, cstack = self.compute_with_stack(inpts, cstack, cneeded_in_stack_map, solved,
                                                                   max_to_swap)
            inpts.reverse()
            for i in range(len(inpts)):
                assert (inpts[i] == cstack[i])
            opcodes += popcodes
            opcodes += [opcode]
            opcodeids += popcodeids
            opcodeids += [opcodeid]
            cstack = outs + cstack[len(inpts):]
            if VERBOSE > 0: print(opcode, cstack, len(cstack))
        return (opcodes, opcodeids, cstack)

    def compute_memory_op(self, o, cstack, cneeded_in_stack_map, solved, max_to_swap):
        """
        Compute a memory instruction
        """
        # print("memory",o)
        opcodes = []
        opcodeids = []
        lord = []

        # First we determine which subterms of o are needed to be used afterwards (i.e. are in cneeded_in_stack_map)
        self.pre_compute_list(o, cstack, cneeded_in_stack_map, lord)

        # We compute them before doing anything else
        (popcodes, popcodeids, cstack) = self.compute_pre_list(lord, cstack, cneeded_in_stack_map, solved, max_to_swap)
        opcodes += popcodes
        opcodeids += popcodeids
        if 'STORE' not in o:
            assert (lord[-1] == o)  # means o was not in current_stack before and now it's computed
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

    def compute_regular_op(self, o, cstack: List[var_T], cneeded_in_stack_map, solved: List[int], max_to_swap: int):
        """
        Compute a regular op (i.e. ignoring dependencies)
        """
        # print("regular",o,cstack)
        opcodes = []
        opcodeids = []
        lord = []
        self.pre_compute_list(o, cstack, cneeded_in_stack_map, lord)

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

    def compute(self, dependency_instrs: List[Union[id_T, var_T]], final_no_store: List[var_T], opcodes_ini: List[str],
                opcodeids_ini: List[str], solved: List[int], initial_stack: List[var_T], max_to_swap: int):
        # print(solved)
        # print('new initial current_stack:',initial)
        # print('final_stack:', self._final_stack)
        # print('store ops:',instr)
        # print(self._needed_in_stack_map)
        topcodes = []
        topcodeids = []
        cstack = initial_stack
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

            # Case POP: I can remove the corresponding element
            while len(cstack) > 0 and (cstack[0] not in cneeded_in_stack_map or cneeded_in_stack_map[cstack[0]] == 0):
                if (len(self._final_stack) - len(cstack)) in solved:
                    break
                topcodes += ['POP']
                topcodeids += ['POP']
                cstack.pop(0)
                if VERBOSE > 0:
                    print('POP', cstack, len(cstack))

            # Either the next element is a STORE instruction or the stack is too long to access case 3
            if (len(dependency_instrs) > 0 and "STORE" in dependency_instrs[0]) \
                    or self.stack_too_long(cstack, dependency_instrs, set(cneeded_in_stack_map.keys())):
                case = 3

            # Otherwise, we choose the case and pos from choose element
            else:
                case, pos = self.choose_element(solved, cstack, cneeded_in_stack_map)
                # print('case:', case, pos)
            # Case 0: current top of the stack is not solved and can be placed in their position.
            # This position is expressed as a negative number
            if case == 0:
                # pos in cstack (negative)
                if cstack[0] == cstack[pos]:
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
                    if VERBOSE > 0: print('SWAP' + str(pos_in_stack), cstack, len(cstack))
                    assert (lens == len(cstack))

            # Case 1: compute an element from the final stack in pos
            elif case == 1:
                before_store = False
                # pos in final_stack

                # Element that must be computed
                o = self._final_stack[pos]
                # print(o,"case1")
                i = len(dependency_instrs) - 1

                # Traverse the instructions with dependencies to check if there is a non-store element needed
                # to compute o
                while i >= 0:
                    if "STORE" not in dependency_instrs[i]:
                        if computed(dependency_instrs[i], o, self._opid_instr_map, self._var_instr_map):
                            break
                    i -= 1
                # Same condition as above but for final_no_store
                # TODO: why it is needed also for this case
                j = len(final_no_store) - 1
                while j >= 0:
                    if computed(final_no_store[j], o, self._opid_instr_map, self._var_instr_map):
                        break
                    j -= 1

                # If there is a non-store element needed to compute o
                if i >= 0 or j >= 0:
                    # print("in instr",o,i)
                    if j >= 0:
                        p = len(dependency_instrs)
                        final_no_store = []
                    else:
                        if dependency_instrs[i] == o:
                            p = i
                            for i in range(p, len(dependency_instrs)):
                                if "STORE" in dependency_instrs[i]:
                                    before_store = True
                                    break
                            dependency_instrs = dependency_instrs[:p] + dependency_instrs[
                                                                        p + 1:]  # remove the operation
                        else:
                            p = i + 1

                    # We need to compute all operations in between
                    for op in dependency_instrs[:p]:
                        # print("previous",op,cneeded_in_stack_map)
                        # print(cstack)
                        self._dup_stack_ini = 0
                        (opcodes, opcodeids, cstack) = self.compute_memory_op(op, cstack, cneeded_in_stack_map, solved,
                                                                              max_to_swap)
                        topcodes += opcodes
                        topcodeids += opcodeids

                    # Remove the instructions with dependencies that have been computed so far
                    dependency_instrs = dependency_instrs[p:]
                    if len(dependency_instrs) == 0:
                        final_no_store = []
                    # c print('current current_stack:',cstack)
                # now we perform the operation
                self._dup_stack_ini = 0
                # print("compute", o)

                # There is a store in between
                if before_store:
                    (opcodes, opcodeids, cstack) = self.compute_memory_op(o, cstack, cneeded_in_stack_map, solved,
                                                                          max_to_swap)
                else:
                    (opcodes, opcodeids, cstack) = self.compute_regular_op(o, cstack, cneeded_in_stack_map, solved,
                                                                           max_to_swap)
                # Update the corresponding position
                topcodes += opcodes
                topcodeids += opcodeids
                pos_in_stack = len(cstack) + pos - len(self._final_stack)

                # Can be placed in the position
                if not (pos_in_stack >= 0 and pos_in_stack <= 16):
                    print(pos_in_stack)
                    assert False
                solved += [pos]
                if pos_in_stack > 0:
                    topcodes += ['SWAP' + str(pos_in_stack)]
                    topcodeids += ['SWAP' + str(pos_in_stack)]
                    lens = len(cstack)
                    cstack = [cstack[pos_in_stack]] + cstack[1:pos_in_stack] + [cstack[0]] + cstack[pos_in_stack + 1:]
                    if VERBOSE > 0: print('SWAP' + str(pos_in_stack), cstack, len(cstack))
                    assert (lens == len(cstack))
            # Case 3: Next instruction in dependency instrs is a STORE or there is a memory instruction that uses
            # an inaccesible element in the stack
            elif case == 3:
                o = dependency_instrs.pop(0)
                # print(o)
                self._dup_stack_ini = 0
                (opcodes, opcodeids, cstack) = self.compute_memory_op(o, cstack, cneeded_in_stack_map, solved,
                                                                      max_to_swap)
                topcodes += opcodes
                topcodeids += opcodeids
            # Case 2: there are only memory instructions left to compute (i.e. all elements in the stack are computed)
            else:  # case 2
                # print("remaining:",instr)
                assert (len(dependency_instrs) == 0 or "STORE" in dependency_instrs[-1])
                # print("final:",instr)

                # TODO: Why? If you are performing all the store ops at this step (no?)
                if len(dependency_instrs) > 0:  # needs to continue after performing all store ops
                    case = 0

                # Compute the dependency instrs
                for o in dependency_instrs:
                    # print(o,cneeded_in_stack_map)
                    # print(cstack)
                    opcodes = []
                    opcodeids = []
                    self._dup_stack_ini = 0
                    (opcodes, opcodeids, cstack) = self.compute_memory_op(o, cstack, cneeded_in_stack_map, solved,
                                                                          max_to_swap)

                    # Remove stack variables that are not needed and can arise
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
                dependency_instrs = []
        # print('current current_stack:',cstack)
        # print('final current_stack:',self._final_stack)
        # print(solved)
        cstack, solved, permutation_opcodes, permutation_opcodesids = self.solve_permutation(cstack, solved)
        assert (cstack == self._final_stack)
        # print("end",cstack,cneeded_in_stack_map)
        return opcodes_ini + topcodes + permutation_opcodes, opcodeids_ini + topcodeids + permutation_opcodesids

    def solve_permutation(self, cstack: List[var_T], solved: List[int]):
        """
        Once every element has been computed the needed number of times, we perform a last step to
        sort the stack correctly. cstack and solved are modified accordingly. The list of opcodes and
        opcodes needed is returned
        """
        topcodes, topcodeids = [], []
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

        return cstack, solved, topcodes, topcodeids

    def target(self) -> Tuple[List[Union[id_T, var_T]], List[var_T]]:
        """
        Computes an order compatible with the dependencies in MEMORY and STORAGE. STORE operations are expressed
        using their ids and the remaning operations using the corresponding operation. Returns such order and the list of
        VARIABLES that are not store operations (SLOAD, MLOAD, KECCAK256) that appear in the SFS (TODO: Check if the ones with deps).
        Also, it computes how many times each variable must be computed
        """

        # First, we determine the id of the operations that are either MSTORE or SSTORE
        lmstore = get_ops_id(self._user_instr, 'MSTORE')
        lsstore = get_ops_id(self._user_instr, 'SSTORE')

        if VERBOSE > 3:
            print("MSTORE Operations")
            print(lmstore)

            print("SSTORE Operations")
            print(lsstore)

        # dep_target_mem = []
        # for e in self._final_stack:
        #    l = get_deps(e,self._var_instr_map,'MLOAD')
        #    dep_target_mem += list(map(lambda x: [mloadmap[x],e], l))
        # print("dep_target:",dep_target_mem)

        # Then, we obtain an order compatible with memory and storage separately
        morder, final_no_mstore = sort_with_deps(lmstore, self._mem_order, self._opid_instr_map, self._var_instr_map)
        sorder, final_no_sstore = sort_with_deps(lsstore, self._sto_order, self._opid_instr_map, self._var_instr_map)
        # dep_target_str = []
        # for e in self._final_stack:
        #    l = get_deps(e,self._var_instr_map,'SLOAD')
        #    dep_target_str += map(lambda x: [sloadmap[x],e], l)
        # print(dep_target_str)

        if VERBOSE > 3:
            print("Mem order initially:", self._mem_order)
            print("Inferred memory order", morder)
            print("No store operations in Memory", final_no_mstore)
            print()
            print("Storage order initially:", self._sto_order)
            print("Inferred storage order", sorder)
            print("No store operations in Storage", final_no_sstore)
            print()

        # Then we combine the dependencies to obtain a compatible order with all dependencies
        torder = merge(morder, sorder, final_no_mstore, final_no_sstore, self._opid_instr_map, self._var_instr_map)

        if VERBOSE > 3:
            print("Torder after merging:", torder)

        # The no store operations are the combination of the no store operations in memory and storage
        final_no_store = []
        for o in final_no_mstore + final_no_sstore:
            final_no_store += [self._opid_instr_map[o]['outpt_sk'][0]]

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

        # print('needed in current_stack:',self._needed_in_stack_map,final_ops_to_count)
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
        print(self._needed_in_stack_map)
        # print(self._needed_in_stack_map)
        # assert(sorted(list(self._needed_in_stack_map.items())) == sorted(list(self.uses.items())))
        # print('initial current_stack:  ', self._initial_stack)
        return torder, final_no_store

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
        """
        Checks if the list of ids that have been generated can be used for the SAT encoding.
        """
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
                        if self._var_times_used[arg1] == 1 and l[i - 1] != o1:
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
                            if self._var_times_used[arg1] == 1 and self._var_times_used[arg2] == 1:
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
                            if o2 != "" and (self.small_zeroary(arg2) or self._var_times_used[arg2] == 1):
                                if l[i - 2] != o2:
                                    # print("Cas9",l[i])
                                    return False
                        elif o1 != "" and self._var_times_used[arg1] == 1:
                            if l[i - 1] != o1:
                                # print("Cas10",l[i])
                                return False
        return True


def greedy_from_json(json_data: Dict[str, Any], verb=False) -> Tuple[
    Dict[str, Any], SMSgreedy, List[str], List[str], int]:
    encoding = SMSgreedy(json_data.copy())
    # print(encoding._var_instr_map)
    # print()
    # print(encoding._opid_instr_map)
    # print(encoding._mem_order)
    # print(encoding._sto_order)
    global verbose
    verbose = verb
    try:
        # Determine a compatible order and the operations that are needed
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
        _, _, tb = sys.exc_info()
        traceback.print_tb(tb)
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
