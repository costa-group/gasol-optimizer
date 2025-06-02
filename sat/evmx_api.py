import os
import resource
import shlex
import sys
import json
import re
# from global_params.paths import evmx
from .bcode import ByteCode
from .enc import Encoding
from .options import Options
from .oracle import Optimizer
from typing import Dict, Any, Tuple, List
from multiprocessing import Process
from contextlib import redirect_stdout
import tempfile
import signal
import resource
import subprocess
from smt_encoding.block_optimizer import OptimizeOutcome



def run_command(cmd, timeout):
    FNULL = open(os.devnull, 'w')
    solc_p = subprocess.Popen(shlex.split(cmd), stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE)
    time_limit = False
    try:
        outs, err = solc_p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        solc_p.kill()
        outs, err = solc_p.communicate()
        time_limit = True
    return outs.decode() + '\n' + err.decode() if err is not None else '', time_limit


def run_and_measure_command(cmd, timeout):
    usage_start = resource.getrusage(resource.RUSAGE_CHILDREN)
    solution, timelimit = run_command(cmd, timeout)
    usage_stop = resource.getrusage(resource.RUSAGE_CHILDREN)
    return solution, timelimit, usage_stop.ru_utime + usage_stop.ru_stime - usage_start.ru_utime - usage_start.ru_stime


def initialize_options(params, language: str) -> Options:
    if language == "evm":
        # Assume the options correspond to the command line
        # python -u evmx.py -vvvv -o len -a sat -A -e pw -s g3 file.json
        # Last arg is empty, simulating the corresponding file name that is not needed
        if params.criteria == "size":
            crit_arg, sat_engine = 'size', 'rc2'
        elif params.criteria == "length":
            crit_arg, sat_engine = 'len', 'sat'
        else:
            crit_arg, sat_engine = 'gas', 'rc2'

        sat_engine = sat_engine if not params.external else 'nuwls-c'

        parsed_options = ['-vvv', '-o', crit_arg, '-a', sat_engine, '--config', params.config_sat, '-e', 'pw',
                          '-s', 'g3', '-i' if params.initial_sat or params.initial_block else '']
    elif language == "wasm":

        sat_engine = "sat" # if not parsed_args.external else 'nuwls-c'

        parsed_options = ['-vvv', '-o', 'len', '-a', sat_engine, '--config', params.config_sat, '-e', 'pw',
                          '-s', 'g3', '-w']
    else:
        raise ValueError(f"Stack language {language} not recognized")
    options = Options(parsed_options)

    return options


def run_optimizer(json_file, options, tmp_file):
    # parsing the input file
    bcode = ByteCode(options, from_dict=json_file)

    # updating the values of max len and stack size if required
    if options.mlen:
        bcode.mlen = options.mlen
    if options.sksz:
        bcode.sksz = options.sksz
    options.verbose = 0
    enc = Encoding(bcode, options)
    options.verbose = 3
    with open(tmp_file, 'w') as tmp, redirect_stdout(tmp), Optimizer(enc, enc.vpool, options) as opt:
        try:
            model = opt.compute()
        except BaseException as e:
            print(str(e), flush=True)


def evmx_with_json(json_file: Dict[str, Any], timeout: float, parsed_args, language: str) -> Tuple[str, float]:
    # read option configurations for initialize function
    options = initialize_options(parsed_args, language)

    fd, tmp_file = tempfile.mkstemp()

    try:
        usage_start = resource.getrusage(resource.RUSAGE_CHILDREN)
        p = Process(target=run_optimizer, args=(json_file, options, tmp_file))
        p.start()
        p.join(timeout)

        if p.is_alive():
            p.terminate()
            p.join()

        usage_stop = resource.getrusage(resource.RUSAGE_CHILDREN)
        total_time = usage_stop.ru_utime + usage_stop.ru_stime - usage_start.ru_utime - usage_start.ru_stime

        with open(tmp_file, 'r') as file:
            msg = file.read()

    finally:
        os.close(fd)
        os.remove(tmp_file)

    return msg, total_time


def find_best_seq(msg: str) -> List[str]:
    rev_lines = reversed(msg.splitlines())
    for line in rev_lines:
        seq_match = re.search(re.compile('c len \d* program: (.+)'), line)
        if seq_match is not None:
            return [elem for elem in seq_match.group(1).split(',') if elem != '']

    return []


def process_msg_process(msg: str) -> Tuple[List[str], str]:
    # Msg is initially assigned to ERROR. If it keeps that way or when reading, the file is empty an error have occurred.
    if msg == 'ERROR':
        return [], 'error'

    elif msg == '':
        return [], 'no_model'

    seq = find_best_seq(msg)

    # Unsat situation: exception caught with the error message:
    # local variable 'model' referenced before assignment
    if 'referenced before assignment' in msg:
        optimization_outcome = 'unsat'
    elif seq == []:
        optimization_outcome = 'no_model'
    elif 'Optimal' in msg:
        optimization_outcome = 'optimal'
    else:
        optimization_outcome = 'non_optimal'

    # No line contains a solution
    return seq, optimization_outcome


def process_msg_subprocess(msg: str, timelimit: bool) -> Tuple[List[str], str]:
    # Msg is initially assigned to ERROR. If it keeps that way or when reading, the file is empty an error have occurred.
    if msg == 'ERROR' or msg == '':
        return [], 'error'

    seq = find_best_seq(msg)

    # Unsat situation: exception caught with the error message:
    # local variable 'model' referenced before assignment
    if 'referenced before assignment' in msg:
        optimization_outcome = 'unsat'
    elif seq == []:
        optimization_outcome = 'no_model'
    elif timelimit:
        optimization_outcome = 'optimal'
    elif not timelimit:
        optimization_outcome = 'non_optimal'
    else:
        raise ValueError('Msg should contain either "Optimal" or "Not optimal"')

    # No line contains a solution
    return seq, optimization_outcome


# def evmx_from_sms_with_subprocess(json_file: Dict[str, Any], timeout: float) -> Tuple[List[str], str, float]:
#     # msg, final_time = evmx_with_json(json_file, timeout)
#     fd, tmp_file = tempfile.mkstemp('.json')
#     os.close(fd)
#     with open(tmp_file, 'w') as f:
#         f.write(json.dumps(json_file))
#     msg, timelimit, final_time = run_and_measure_command(f'python3 -u {evmx} -vvvv -o len -a sat -A -e pw -s g3 {tmp_file}', timeout)
#     os.remove(tmp_file)
#     return *process_msg_subprocess(msg, timelimit), final_time


def evmx_from_sms_with_process(json_file: Dict[str, Any], timeout: float, parsed_args, language: str) -> Tuple[List[str], str, float]:
    msg, final_time = evmx_with_json(json_file, timeout, parsed_args, language)
    return *process_msg_process(msg), final_time


def evmx_from_sms(json_file: Dict[str, Any], timeout: float, parsed_args, language: str) -> Tuple[List[str], str, float]:
    return evmx_from_sms_with_process(json_file, timeout, parsed_args, language)


def evmx_opt_outcome_to_gasol(opt_outcome: str) -> OptimizeOutcome:
    if opt_outcome == 'unsat':
        return OptimizeOutcome.unsat
    if opt_outcome == 'error':
        return OptimizeOutcome.error
    elif opt_outcome == 'no_model':
        return OptimizeOutcome.no_model
    elif opt_outcome == 'non_optimal':
        return OptimizeOutcome.non_optimal
    elif opt_outcome == 'optimal':
        return OptimizeOutcome.optimal
    raise ValueError(f'{opt_outcome} not recognized')


def evmx_to_gasol(sms, timeout: float, parsed_args) -> Tuple[OptimizeOutcome, float, List[str]]:
    # There was an error when initializing the optimizer
    id_seq, optimization_outcome, time = evmx_from_sms(sms, timeout, parsed_args, "evm")
    return evmx_opt_outcome_to_gasol(optimization_outcome), time, id_seq
