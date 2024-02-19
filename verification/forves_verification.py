import subprocess
import shlex
import tempfile
from pathlib import Path
import re
from typing import List, Union
import sys
import os
import global_params.paths as paths
import global_params.constants as constants
import traceback



def run_command(cmd):
    FNULL = open(os.devnull, 'w')
    solc_p = subprocess.Popen(shlex.split(cmd), stdout=subprocess.PIPE,
                              stderr=FNULL)
    return solc_p.communicate()[0].decode()


#
#
bytecode_vocab = ['ADD', 'MUL', 'NOT', 'SUB', 'DIV', 'SDIV', 'MOD', 'SMOD', 'ADDMOD', 'MULMOD', 'EXP', 'SIGNEXTEND',
                  'LT', 'GT', 'SLT', 'SGT', 'EQ', 'ISZERO', 'AND', 'OR', 'XOR', 'BYTE', 'SHL', 'SHR', 'SAR', 'SHA3',
                  'KECCAK256', 'ADDRESS', 'BALANCE', 'ORIGIN', 'CALLER', 'CALLVALUE', 'CALLDATALOAD', 'CALLDATASIZE ',
                  'CODESIZE', 'GASPRICE', 'EXTCODESIZE', 'RETURNDATASIZE', 'EXTCODEHASH', 'BLOCKHASH', 'COINBASE',
                  'TIMESTAMP', 'NUMBER', 'DIFFICULTY', 'GASLIMIT', 'CHAINID', 'SELFBALANCE', 'BASEFEE', 'SLOAD',
                  'MLOAD', 'MSTORE', 'MSTORE8', 'SSTORE', 'PC', 'MSIZE', 'GAS', 'CREATE', 'CREATE2', 'CALLDATASIZE',
                  'CALLDATALOAD', 'JUMPI', 'JUMPDEST', 'METAPUSH', 'PREVRANDAO',
                  'POP',
                  'DUP1', 'DUP2', 'DUP3', 'DUP4', 'DUP5', 'DUP6', 'DUP7', 'DUP8', 'DUP9', 'DUP10', 'DUP11', 'DUP12',
                  'DUP13', 'DUP14', 'DUP15', 'DUP16',
                  'SWAP1', 'SWAP2', 'SWAP3', 'SWAP4', 'SWAP5', 'SWAP6', 'SWAP7', 'SWAP8', 'SWAP9', 'SWAP10', 'SWAP11',
                  'SWAP12', 'SWAP13', 'SWAP14', 'SWAP15', 'SWAP16',
                  "JUMP", "JUMPI", "REVERT",
                  ]

#
#
def is_pseudo_keyword(opcode: str) -> bool:
    if opcode.find("tag") == -1 and opcode.find("#") == -1 and opcode.find("$") == -1 \
            and opcode.find("data") == -1:
        return False
    else:
        return True


def keyword_to_id(keyword):
    if keyword == "PUSHDEPLOYADDRESS":
        return 0
    elif keyword == "PUSHSIZE":
        return 1
    elif keyword == "PUSHLIB":
        return 2
    elif keyword == "PUSHIMMUTABLE":
        return 3
    elif keyword == "data":
        return 4
    elif keyword == "[tag]":
        return 5
    elif keyword == "[$]":
        return 6
    elif keyword == "#[$]":
        return 7
    else:
        raise Exception(f'uknown meta push keyword: {keyword}')


def split_bytecode(raw_instruction_str: str) -> List[Union[List[str], str]]:
    """
    We also split the bytecode by instructions that are not processed by GASOL and include them
    as a single string
    """
    ops = raw_instruction_str.split(' ')
    blocks_to_process = []
    opcodes = []
    i = 0
    operand = None
    meta_operand = None
    final_op = None
    while i < len(ops):
        op = ops[i]

        # JUMPDEST is removed from the block - later maybe we should support.
        # Ignore initial instructions
        if op in constants.end_block or op in constants.beginning_block or op in constants.split_block:
            # We append the opcodes we have so far
            if len(opcodes) > 0:
                blocks_to_process.append(opcodes)
            blocks_to_process.append(op)

        # if it does not start with PUSH, then its an opcode with no operands
        elif not op.startswith("PUSH"):
            final_op = op

        # op starts with PUSH
        else:
            if op == "PUSH0":
                final_op = "PUSH1"
                operand = f'0x0'
            # Just in case PUSHx instructions are included, we translate them to "PUSH x" name instead
            elif re.fullmatch("PUSH[0-9]", op) is not None:
                final_op = op
                operand = f'0x{ops[i + 1]}'
                i = i + 1
            elif op == "PUSHDEPLOYADDRESS" or op == "PUSHSIZE":
                final_op = "METAPUSH"
                meta_operand = f'{keyword_to_id(op)}'
                operand = f'0x0'
            elif op == "PUSHLIB" or op == "PUSHIMMUTABLE":
                final_op = "METAPUSH"
                meta_operand = f'{keyword_to_id(op)}'
                operand = f'0x{ops[i + 1]}'
                i = i + 1
            elif op == "PUSH" and is_pseudo_keyword(ops[i + 1]):
                final_op = "METAPUSH"
                meta_operand = f'{keyword_to_id(ops[i + 1])}'
                operand = f'0x{ops[i + 2]}'
                i = i + 2
            # A  PUSH
            elif op == "PUSH":
                n = (len(ops[i + 1]) + 1) // 2
                assert n >= 1 and n <= 32
                final_op = f'PUSH{n}'
                operand = f'0x{ops[i + 1]}'
                i = i + 1

            # Something that we don't handle, will just leave it and an exception will be thrown
            else:
                raise Exception("...")
        if final_op is not None:
            opcodes.append(final_op)
            final_op = None
        if meta_operand is not None:
            opcodes.append(meta_operand)
            meta_operand = None
        if operand is not None:
            opcodes.append(operand)
            operand = None

        i += 1
    if len(opcodes) > 0:
        blocks_to_process.append(opcodes)
    return blocks_to_process


def str_to_list(bytecode_str: str) -> List[List[str]]:
    bytecode_seqs = split_bytecode(bytecode_str)
    out_seqs = []
    out_seq = []
    for bytecode_seq in bytecode_seqs:
        # Isolated instructions are compared term to term separately
        if isinstance(bytecode_seq, str):
            out_seqs.append(bytecode_seq)

        else:
            i, n = 0, len(bytecode_seq)
            while i < n:
                instr = bytecode_seq[i]
                if re.fullmatch("PUSH([0-9]+)", instr) is not None:
                    out_seq.append(bytecode_seq[i])
                    out_seq.append(bytecode_seq[i + 1])
                    i = i + 2
                elif instr == "METAPUSH":
                    out_seq.append(bytecode_seq[i])
                    out_seq.append(bytecode_seq[i + 1])
                    out_seq.append(bytecode_seq[i + 2])
                    i = i + 3
                else:
                    idx = bytecode_vocab.index(instr)  # just check the instruction is supported
                    out_seq.append(instr)
                    i = i + 1
            out_seqs.append(out_seq)
    return out_seqs


def forves_format(seq1, seq2) -> str:
    try:
        initial_seqs = str_to_list(seq1)
        opt_seqs = str_to_list(seq2)
        if len(initial_seqs) != len(opt_seqs):
            raise ValueError(f"Resulting seqs have not the same size")

        forves_str = []
        for initial_seq, opt_seq in zip(initial_seqs, opt_seqs):
            # We must ensure that if either of the instructions is a string, both are string and match
            if isinstance(initial_seq, str) or isinstance(opt_seq, str):
                assert isinstance(opt_seq, str)
                assert isinstance(initial_seq, str)
                assert initial_seq == opt_seq
                continue

            bytecode = ' '.join(initial_seq)
            opt_bytecode = ' '.join(opt_seq)
            stack_size = 500

            words = ['#', opt_bytecode, bytecode, str(stack_size)]
            forves_str.append('\n'.join(words))
        return '\n'.join(forves_str)

    except Exception as e:
        traceback.print_exc()
        print(e, file=sys.stderr)


def compare_forves(previous_block: str, new_solution: str, criteria: str = "size"):
    criteria_flag = "all" if criteria == "gas" else "all_size"
    forves_input = forves_format(previous_block, new_solution)

    # If there is a simple JUMP to compare or a block with no opcodes to optimize, then we return true directly
    if forves_input == '':
        return "true"

    fd, tmp_file = tempfile.mkstemp()

    with open(tmp_file, 'w') as f:
        forves_input = forves_format(previous_block, new_solution)
        f.write(forves_input)

    command = f"{Path(paths.project_path).joinpath('bin/forves-checker')} -i {tmp_file} " \
              f"-opt_rep 20 -pipeline_rep 20 -opt {criteria_flag} -mu basic -su basic -ms basic -ss basic " \
              f"-ssv_c basic -mem_c po -strg_c po -sha3_c trivial "

    output = run_command(command)

    os.close(fd)
    os.remove(tmp_file)

    if "false" in output:
        return "false"
    elif "parsing error" in output:
        return "parsing"
    elif "true" in output:
        return "true"
    else:
        raise ValueError("Not recognized option in output:", output)


def compare_forves_csv_info(csv_info, criteria: str = "size"):
    return compare_forves(csv_info["previous_solution"], csv_info["solution_found"], criteria)
