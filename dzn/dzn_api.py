import os
import re
import subprocess
import resource
import shlex
import tempfile
from typing import List, Tuple
from dzn.dzn_generation import SMSgreedy
from global_params.paths import mzn_path
from smt_encoding.block_optimizer import OptimizeOutcome


def run_command(cmd):
    solc_p = subprocess.Popen(shlex.split(cmd), stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE)
    out, err = solc_p.communicate()
    return out.decode() + '\n' + err.decode() if err is not None else ''


def run_and_measure_command(cmd):
    usage_start = resource.getrusage(resource.RUSAGE_CHILDREN)
    solution = run_command(cmd)
    usage_stop = resource.getrusage(resource.RUSAGE_CHILDREN)
    return solution, usage_stop.ru_utime + usage_stop.ru_stime - usage_start.ru_utime - usage_start.ru_stime


def mzn_id_to_instr_id(mzn_id: str) -> str:
    if mzn_id == 'POP' or mzn_id == 'NOP':
        return mzn_id
    dup_swap_re = re.match(re.compile('(DUP|SWAP)\((.+)\)'), mzn_id)
    if dup_swap_re is not None:
        return f'{dup_swap_re.group(1)}{dup_swap_re.group(2)}'
    other_op_match = re.match(re.compile('.+\((.+)\)'), mzn_id)
    if other_op_match is not None:
        return other_op_match.group(1)
    raise ValueError(f'{mzn_id} does not match any of the mzn id possibilities')


def find_best_seq(output: str) -> List[str]:
    rev_lines = reversed(output.splitlines())
    seq_re = re.compile('solution = \[(.*)]')
    for line in rev_lines:
        solution_mzn = re.match(seq_re, line)
        if solution_mzn is not None:
            mzn_ids = solution_mzn.group(1).split(', ')
            instr_ids = []
            for mzn_id in mzn_ids:
                instr_id = mzn_id_to_instr_id(mzn_id)
                if instr_id == 'NOP':
                    return instr_ids
                else:
                    instr_ids.append(instr_id)
            return instr_ids
    return []


def process_msg(msg: str) -> Tuple[List[str], OptimizeOutcome]:
    if '=====UNKNOWN=====' in msg:
        optimization_outcome = OptimizeOutcome.no_model
    elif 'Error' in msg:
        optimization_outcome = OptimizeOutcome.error
    elif '=====UNSATISFIABLE=====' in msg:
        optimization_outcome = OptimizeOutcome.unsat
    elif '% Time limit exceeded!' in msg:
        optimization_outcome = OptimizeOutcome.non_optimal
    else:
        optimization_outcome = OptimizeOutcome.optimal

    seq = find_best_seq(msg)
    print(msg)
    print(seq)

    return seq, optimization_outcome


def generate_flags_for_minizinc(bool_flags) -> str:
    flags = []
    if bool_flags.length_bound:
        flags.append('length_bound')
    if bool_flags.gcc_bounds:
        flags.append('gcc_bounds')
    if bool_flags.unary_shrink:
        flags.append('unary_shrink')
    if bool_flags.binary_shrink:
        flags.append('binary_shrink')
    if bool_flags.pop_unused:
        flags.append('pop_unused')

    return ' '.join([f'-D "{flag}=true"' for flag in flags])


def dzn_optimization_from_sms(sms, timeout, bool_flags, model_path="dzn/evmopt-generic.mzn") -> \
        Tuple[OptimizeOutcome, float, List[str]]:


    fd, tmp_file = tempfile.mkstemp('.dzn')
    os.close(fd)
    with open(tmp_file, 'w') as f:
        encoding = SMSgreedy(sms, f)
        encoding.generate_dzn()

    flag_str = generate_flags_for_minizinc(bool_flags)
    command = f"{mzn_path} --solver Chuffed --time-limit {timeout*1000} " \
              f"--output-time --intermediate-solutions -s {model_path} {flag_str} {tmp_file}"
    #stats -s needed to run analysis

    print(f"Command: {command}")
    output, total_time = run_and_measure_command(command)

    #os.remove(tmp_file)
    solver_ids, optimization_output = process_msg(output)
    return optimization_output, total_time, solver_ids
