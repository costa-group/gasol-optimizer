from typing import List, Dict, Any


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


def get_ops_id(instructions: List[Dict[str, Any]], op: str) -> List[str]:
    """
    List of instruction ids who share the same disasm field
    """
    return [ins['id'] for ins in instructions if op in ins['disasm']]


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
