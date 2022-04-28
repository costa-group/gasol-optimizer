import math

import sfs_generator.opcodes as opcodes


def toInt(a):
    elem = a.split("_")
    if len(elem)>1:
        return int(elem[0])
    else:
        return int(a)


def is_integer(num):
    try:
        val = int(num)
    except:
        val = -1

    return val
    
'''
It returns the id of a rbr_rule.
'''
def orderRBR(rbr):
    return str(rbr[0].get_Id())


def delete_dup(l):
    r = []
    for e in l:
        if e not in r:
            r.append(e)
    return r

def process_isolate_block(contract_name, in_stack = -1):
    
    f = open(contract_name,"r")
    if in_stack == -1:
        input_stack = f.readline().strip("\n")
    else:
        input_stack = in_stack


    print(input_stack)
        
    instructions = f.readline().strip()

    print(instructions)
    
    initial = 0
    final_sequence = []

    ops = instructions.split(" ")
    i = 0
    while(i<len(ops)):
        op = ops[i]
        if not op.startswith("PUSH"):
            final_sequence.append(op.strip())
        else:
            val = ops[i+1]
            final_sequence.append(op+" "+val)
            i=i+1
        i+=1

    f.close()
    
    return final_sequence,input_stack

def all_integers(variables):
    int_vals = []
    try:
        for v in variables:
            x = int(v)
            int_vals.append(x)
        return True, int_vals
    except:
        return False,variables

''' 
search_lsit contains the complete sequence of instructions that
appears in the corresponding rbr block (instrs+opcodes) 

pattern contains only the opcodes sequence

It returns the init and the end index of the pattern
'''
def find_sublist(search_list, pattern):
    cursor = 0
    init = 0
    fin = 0
    first = True
    found = []
    j = 0
    for i in search_list:
        if i.startswith("nop("):
            if i == pattern[cursor]:
                if first:
                    init = search_list.index(i)
                    first = False
                cursor += 1
                if cursor == len(pattern):
                    found.append(pattern)
                    fin = search_list.index(i,j)
                    cursor = 0
            else:
                first = True
                cursor = 0
        j+=1

    if search_list[init][4:-1].startswith("SWAP"):
        init = init-3
    else:
        init = init-1
    return init,fin

''' 
Given a sequence of evm instructions as a list, it returns the
minimum number of elements that needs to be located in the stack in
orde to execute the sequence 
'''

def compute_stack_size(evm_instructions):
    current_stack = 0
    init_stack = 0
    
    for op in evm_instructions:
        opcode_info = opcodes.get_opcode(op)

        consumed_elements = opcode_info[1]
        produced_elements = opcode_info[2]
            
        if consumed_elements > current_stack:
            diff = consumed_elements - current_stack
            init_stack +=diff
            current_stack = current_stack+diff-consumed_elements+produced_elements
        else:
            current_stack = current_stack-consumed_elements+produced_elements

    return init_stack


'''
Function that identifies the PUSH opcodes used in the yul translation that are not real evm opcodes.
(PUSH tag, PUSHDEPLOYADDRESS, PUSH data...)
'''
def isYulInstruction(opcode):
    if opcode.find("tag") ==-1 and opcode.find("#") ==-1 and opcode.find("$") ==-1 \
            and opcode.find("data") ==-1 and opcode.find("DEPLOY") ==-1 and opcode.find("SIZE")==-1 and opcode.find("IMMUTABLE")==-1:
        return False
    else:
        return True


# Returns true if opcode contains tag, #, $ or data, so that composed opcodes are identified
def isYulKeyword(opcode):
    if opcode.find("tag") ==-1 and opcode.find("#") ==-1 and opcode.find("$") ==-1 \
            and opcode.find("data") ==-1:
        return False
    else:
        return True


'''
It returns true if the instruction generates a constant value
'''

def is_constant_instruction(ins):
    constant = False
    if ins.find("DUP")!=-1 or ins.find("PUSH")!=-1:
        constant = True
    elif ins in ["ADDRESS","ORIGIN","CALLER","CALLVALUE","CALLDATASIZE","CODESIZE","GASPRICE","COINBASE","TIMESTAMP","NUMBER","DIFFICULTY","GASLIMIT","CHAINID","SELFBALANCE","PC","MSIZE","GAS","TXEXECGAS","STOP","RETURN","INVALID","REVERT"]:
        constant = True
    else:
        constant = False

    return constant


def isYulInstructionUpper(opcode):
    if opcode.find("TAG") == -1 and opcode.find("#") == -1 and opcode.find("$") == -1 \
            and opcode.find("DATA") == -1 and opcode.find("DEPLOY") == -1 and opcode.find("SIZE") == -1 and opcode.find("IMMUTABLE") == -1:
        return False
    else:
        return True


# Number encoding size following the implementation in Solidity compiler:
# https://github.com/ethereum/solidity/blob/develop/libsolutil/Numeric.h
def number_encoding_size(number):
    i = 0
    while number != 0:
        i += 1
        number = number >> 8
    return i


# Number of bytes necessary to encode an int value
def get_num_bytes_int(val):
    return max(1, number_encoding_size(val))


# Number of bytes necessary to encode a hex value. Matches the x in PUSHx opcodes
def get_push_number_hex(val):
    return get_num_bytes_int(int(val, 16))


# Taken directly from https://github.com/ethereum/solidity/blob/develop/libevmasm/AssemblyItem.cpp
# Address length: maximum address a tag can appear. By default 4 (as worst case for PushSubSize is 16 MB)
def get_ins_size(op_name, val = None, address_length = 4):
    if op_name == "ASSIGNIMMUTABLE":
        # Number of PushImmutable's with the same hash. Assume 1 (?)
        immutableOccurrences = 1

        # Just in case the behaviour is changed, following code corresponds to the byte size according to
        # immutable variable
        if immutableOccurrences == 0:
            return 2
        else:
            return (immutableOccurrences - 1) * (5 + 32) + (3 + 32)
    elif op_name == "PUSH":
        return 1 + get_num_bytes_int(val)
    elif op_name == "PUSH #[$]" or op_name == "PUSHSIZE":
        return 1 + 4
    elif op_name == "PUSH [tag]" or op_name == "PUSH data" or op_name == "PUSH [$]":
        return 1 + address_length
    elif op_name == "PUSHLIB" or op_name == "PUSHDEPLOYADDRESS":
        return 1 + 20
    elif op_name == "PUSHIMMUTABLE":
        return 1 + 32
    elif not op_name.startswith("PUSH") or op_name == "tag":
        return 1
    else:
        raise ValueError("Opcode not recognized", op_name)


# Given a sequence of opcodes in a str, returns the size associated. Note the yul operators must follow the
# corresponding convention: see sfs_generator.opcodes.opcode_internal_representation_to_assembly_item for
# the conversion between names
def get_ins_size_seq(instructions_disasm):
    instructions = list(filter(lambda x: x != '', instructions_disasm.split(' ')))
    i, bytes = 0, 0
    while i < len(instructions):
        if instructions[i] == "PUSH" and not(isYulKeyword(instructions[i+1])):
            bytes += get_ins_size("PUSH", int(instructions[i+1], 16))
            i += 2
        elif instructions[i] == "PUSH":
            bytes += get_ins_size(' '.join(instructions[i:i+2]), instructions[i+2])
            i += 3
        elif instructions[i] == "ASSIGNIMMUTABLE":
            bytes += get_ins_size(instructions[i], instructions[i+1])
            i += 2
        elif instructions[i].startswith("PUSH") and not instructions[i].startswith("PUSHDEPLOYADDRESS") \
                    and not instructions[i].startswith("PUSHSIZE"):
            bytes += get_ins_size(instructions[i], None)
            i += 2
        else:
            bytes += get_ins_size(instructions[i], None)
            i += 1
    return bytes
