import re
from typing import List

# list of all opcodes except the PUSHi and DUPi
# opcodes[name] has a list of [value (index), no. of items removed from stack, no. of items added to stack]
opcodes = {
    "STOP": [0x00, 0, 0],
    "ADD": [0x01, 2, 1],
    "MUL": [0x02, 2, 1],
    "SUB": [0x03, 2, 1],
    "DIV": [0x04, 2, 1],
    "SDIV": [0x05, 2, 1],
    "MOD": [0x06, 2, 1],
    "SMOD": [0x07, 2, 1],
    "ADDMOD": [0x08, 3, 1],
    "MULMOD": [0x09, 3, 1],
    "EXP": [0x0a, 2, 1],
    "SIGNEXTEND": [0x0b, 2, 1],
    "LT": [0x10, 2, 1],
    "GT": [0x11, 2, 1],
    "SLT": [0x12, 2, 1],
    "SGT": [0x13, 2, 1],
    "EQ": [0x14, 2, 1],
    "ISZERO": [0x15, 1, 1],
    "AND": [0x16, 2, 1],
    "OR": [0x17, 2, 1],
    "XOR": [0x18, 2, 1],
    "NOT": [0x19, 1, 1],
    "BYTE": [0x1a, 2, 1],
    "SHL": [0x1b,2,1],
    "SHR": [0x1c,2,1],
    "SAR": [0x1d,2,1],
    "SHA3": [0x20, 2, 1],
    "ADDRESS": [0x30, 0, 1],
    "BALANCE": [0x31, 1, 1],
    "ORIGIN": [0x32, 0, 1],
    "CALLER": [0x33, 0, 1],
    "CALLVALUE": [0x34, 0, 1],
    "CALLDATALOAD": [0x35, 1, 1],
    "CALLDATASIZE": [0x36, 0, 1],
    "CALLDATACOPY": [0x37, 3, 0],
    "CODESIZE": [0x38, 0, 1],
    "CODECOPY": [0x39, 3, 0],
    "GASPRICE": [0x3a, 0, 1],
    "EXTCODESIZE": [0x3b, 1, 1],
    "EXTCODECOPY": [0x3c, 4, 0],
    "MCOPY": [0x3d, 3, 0],
    "EXTCODEHASH":[0x3f,1,1],
    "BLOCKHASH": [0x40, 1, 1],
    "COINBASE": [0x41, 0, 1],
    "TIMESTAMP": [0x42, 0, 1],
    "NUMBER": [0x43, 0, 1],
    "DIFFICULTY": [0x44, 0, 1],
    "PREVRANDAO": [0x44, 0, 1],
    "GASLIMIT": [0x45, 0, 1],
    "CHAINID": [0x46,0,1],
    "SELFBALANCE": [0x47,0,1],
    "BASEFEE": [0x48,0,1],
    "POP": [0x50, 1, 0],
    "MLOAD": [0x51, 1, 1],
    "MSTORE": [0x52, 2, 0],
    "MSTORE8": [0x53, 2, 0],
    "SLOAD": [0x54, 1, 1],
    "SSTORE": [0x55, 2, 0],
    "JUMP": [0x56, 1, 0],
    "JUMPI": [0x57, 2, 0],
    "PC": [0x58, 0, 1],
    "MSIZE": [0x59, 0, 1],
    "GAS": [0x5a, 0, 1],
    "JUMPDEST": [0x5b, 0, 0],
    "SLOADEXT": [0x5c, 2, 1],
    "SSTOREEXT": [0x5d, 3, 0],
    "SLOADBYTESEXT": [0x5c, 4, 0],
    "SSTOREBYTESEXT": [0x5d, 4, 0],
    "LOG0": [0xa0, 2, 0],
    "LOG1": [0xa1, 3, 0],
    "LOG2": [0xa2, 4, 0],
    "LOG3": [0xa3, 5, 0],
    "LOG4": [0xa4, 6, 0],
    "CREATE": [0xf0, 3, 1],
    "CALL": [0xf1, 7, 1],
    "CALLCODE": [0xf2, 7, 1],
    "RETURN": [0xf3, 2, 0],
    "REVERT": [0xfd, 2, 0],
    "ASSERTFAIL": [0xfe, 0, 0],
    "DELEGATECALL": [0xf4, 6, 1],
    "CREATE2": [0xf5,4,1],
    "BREAKPOINT": [0xf5, 0, 0],
    "RNGSEED": [0xf6, 1, 1],
    "SSIZEEXT": [0xf7, 2, 1],
    "SLOADBYTES": [0xf8, 3, 0],
    "SSTOREBYTES": [0xf9, 3, 0],
    "SSIZE": [0xfa, 1, 1],
    "STATICCALL": [0xfa, 6, 1],
    "STATEROOT": [0xfb, 1, 1],
    "TXEXECGAS": [0xfc, 0, 1],
    "CALLSTATIC": [0xfd, 7, 1],
    "KECCAK256": [0x20, 2, 1], #For evm it is representes as SHA3, for solc as KECCAK256
    "INVALID": [0xfe, 0, 0],  # Not an opcode use to cause an exception
    "SUICIDE": [0xff, 1, 0],
    # See https://github.com/ethereum/solidity/blob/develop/libevmasm/Assembly.cpp for more information
    "ASSIGNIMMUTABLE": [0x00,2,0], #Yul opcode. Assembly Item: AssignImmutable
    "PUSH [tag]": [0x00,0,1], #Yul opcode. Assembly Item: PushTag
    "PUSHLIB": [0x00,0,1], #Yul opcode. Assembly Item: PushLib
    "PUSH #[$]": [0x00,0,1], #Yul opcode. Assembly Item: PushSubSize
    "PUSH [$]": [0x00,0,1], #Yul opcode. Assembly Item: PushSub
    "PUSHDEPLOYADDRESS": [0x00,0,1], #Yul opcode. AssemblyItem: PushDeployTimeAddress
    "PUSH data": [0x00,0,1], #Yul opcode. Assembly Item: PushData
    "PUSHSIZE": [0x00,0,1], #Yul opcode. Assembly Item: PushProgramSize
    "PUSHIMMUTABLE": [0x00,0,1], #Yul opcode. Assembly Item:PushImmutable
    "---END---": [0x00, 0, 0]
}

# Opcodes that have a blank character in their name are put together in our representation
opcode_internal_representation_to_assembly_item = {
    "PUSHTAG": "PUSH [tag]", #Yul opcode. Assembly Item: PushTag
    "PUSH#[$]": "PUSH #[$]", #Yul opcode. Assembly Item: PushSubSize
    "PUSH[$]": "PUSH [$]", #Yul opcode. Assembly Item: PushSub
    "PUSHDATA": "PUSH data", #Yul opcode. Assembly Item: PushData
}

# TO BE UPDATED IF ETHEREUM VM CHANGES their fee structure

GCOST = {
    "Gzero": 0,
    "Gbase": 2,
    "Gverylow": 3,
    "Glow": 5,
    "Gmid": 8,
    "Ghigh": 10,
    "Gextcode": 700,
    "Gextcodehash": 400,
    "Gbalance": 400,
    "Gsload": 700,
    "Gjumpdest": 1,
    "Gsset": 20000,
    "Gsreset": 5000,
    "Rsclear": 15000,
    "Rsuicide": 24000,
    "Gsuicide": 5000,
    "Gcreate": 32000,
    "Gcodedeposit": 200,
    "Gcall": 34700,
    "Gcallvalue": 9000,
    "Gcallstipend": 2300,
    "Gnewaccount": 25000,
    "Gexp": 10,
    "Gexpbyte": 50,
    "Gmemory": 3,
    "Gtxcreate": 32000,
    "Gtxdatazero": 4,
    "Gtxdatanonzero": 68,
    "Gtransaction": 21000,
    "Glog": 375,
    "Glogdata": 8,
    "Glogtopic": 375,
    "Gsha3": 30,
    "Gsha3word": 6,
    "Gcopy": 3,
    "Gblockhash": 20
}

Wzero = ("STOP", "RETURN", "REVERT", "ASSERTFAIL")

Wbase = ("ADDRESS", "ORIGIN", "CALLER", "CALLVALUE", "CALLDATASIZE",
         "CODESIZE", "GASPRICE", "COINBASE", "TIMESTAMP", "NUMBER",
         "DIFFICULTY", "PREVRANDAO", "BASEFEE", "GASLIMIT", "POP", "PC", "MSIZE", "GAS", "RETURNDATASIZE","CHAINID")

Wverylow = ("ADD", "SUB", "NOT", "LT", "GT", "SLT", "SGT", "EQ",
            "ISZERO", "AND", "OR", "XOR", "BYTE", "CALLDATALOAD",
            "MLOAD", "MSTORE", "MSTORE8", "PUSH", "DUP", "SWAP","SHL","SHR","SAR")

Wlow = ("MUL", "DIV", "SDIV", "MOD", "SMOD", "SIGNEXTEND","SELFBALANCE")

Wmid = ("ADDMOD", "MULMOD", "JUMP")

Whigh = ("JUMPI")

Wext = ("EXTCODESIZE")

Wextcodehash = ("EXTCODEHASH")

def get_opcode(opcode):
    if opcode in opcodes:
        return opcodes[opcode]

    #PG
    elif opcode == "RETURNDATASIZE":
        return [0x3d, 0, 1]

    elif opcode == "RETURNDATACOPY":
        return [0x3e, 3, 0]

    elif opcode.startswith("PUSH"):
    # # check PUSHi
    # for i in range(32):
    #     if opcode == 'PUSH' + str(i + 1):
        return [0x60, 0, 1]

    elif opcode.startswith("tag"):
        return [int(hex(0x00),16), 0, 0]
    
    # check PUSHi
    for i in range(32):
        if opcode == 'PUSH' + str(i + 1):
            return [int(hex(0x60 + i),16), 0, 1]

    # check DUPi
    for i in range(16):
        if opcode == 'DUP' + str(i + 1):
            return [int(hex(0x80 + i),16), i + 1, i + 2]

    # check SWAPi
    for i in range(16):
        if opcode == 'SWAP' + str(i + 1):
            return [int(hex(0x90 + i),16), i + 2, i + 2]
    raise ValueError('Bad Opcode ' + opcode)

def get_ins_cost(opcode,params=None):
    if opcode in Wzero:
        return GCOST["Gzero"]
    elif opcode in Wbase:
        return GCOST["Gbase"]
    elif opcode in Wverylow or opcode.startswith("PUSH") or opcode.startswith("DUP") or opcode.startswith("SWAP"):
        return GCOST["Gverylow"]
    elif opcode in Wlow:
        return GCOST["Glow"]
    elif opcode in Wmid:
        return GCOST["Gmid"]
    elif opcode in Whigh:
        return GCOST["Ghigh"]
    elif opcode in Wext:
        return GCOST["Gextcode"]
    elif opcode in Wextcodehash:
        return GCOST["Gextcodehash"]
    elif opcode == "SLOAD":
        return GCOST["Gsload"]
    elif opcode == "JUMPDEST":
        return GCOST["Gjumpdest"]
    elif opcode == "CREATE":
        return GCOST["Gcreate"]
    elif opcode == "CREATE2":
        return GCOST["Gcreate"]
    elif opcode in ("CALL", "CALLCODE","DELEGATECALL","STATICCALL"):
        return GCOST["Gcall"]
    elif opcode in ("LOG0", "LOG1", "LOG2", "LOG3", "LOG4"):
        num_topics = int(opcode[3:])
        return GCOST["Glog"] + num_topics * GCOST["Glogtopic"]
    elif opcode in ("CALLDATACOPY", "CODECOPY","RETURNDATACOPY"):
        return GCOST["Gverylow"]
    elif opcode == "BALANCE":
        return GCOST["Gbalance"]
    elif opcode == "BLOCKHASH":
        return GCOST["Gblockhash"]
    elif opcode == "EXP":
        return 60
    elif opcode == "SHA3":
        return GCOST["Gsha3"]
    elif opcode == "SSTORE":
        return 5000
    elif opcode == "KECCAK256":
        return GCOST["Gsha3"]
    return 0
    

def is_push_instr(opcode):
    return opcode.startswith("PUSH")

def is_memory_read_instr(opcode):
    return opcode.startswith("MLOAD")

def is_memory_write_instr(opcode):
    return opcode.startswith("MSTORE")

def is_memory_instr(opcode):
    return is_memory_read_instr(opcode) or is_memory_write_instr(opcode)

def is_store_read_instr(opcode):
    return opcode.startswith("SLOAD")

def is_store_write_instr(opcode):
    return opcode.startswith("SSTORE")

def is_store_instr(opcode):
    return is_store_read_instr(opcode) or is_store_write_instr(opcode)

def is_comm_instr(opcode):
    return opcode in [ 'ADD', 'MUL', 'AND', 'OR', 'XOR' ]



def is_dup_instr(opcode):
    return re.fullmatch("DUP([0-9]+)", opcode) != None

def is_swap_instr(opcode):
    return re.fullmatch("SWAP([0-9]+)", opcode) != None



vocab = ['ADD', 'MUL', 'SUB', 'DIV', 'SDIV', 'MOD', 'SMOD', 'ADDMOD', 'ADDMOD', 'MULMOD', 'EXP', 'SIGNEXTEND', 'LT', 'GT', 'SLT', 'SGT', 'EQ', 'ISZERO', 'AND', 'OR', 'XOR', 'NOT', 'BYTE', 'SHL', 'SHR', 'SAR', 'ADDRESS', 'BALANCE', 'ORIGIN', 'CALLER', 'CALLVALUE', 'CALLDATALOAD', 'CALLDATASIZE', 'CODESIZE', 'GASPRICE', 'EXTCODESIZE', 'EXTCODEHASH', 'BLOCKHASH', 'COINBASE', 'TIMESTAMP', 'NUMBER', 'DIFFICULTY', 'PREVRANDAO', 'GASLIMIT', 'CHAINID', 'SELFBALANCE', 'BASEFEE', 'POP', 'MLOAD', 'MSTORE', 'MSTORE8', 'SLOAD', 'SSTORE', 'PC', 'GAS', 'KECCAK256', 'PUSH [tag]', 'PUSHLIB', 'PUSH #[$]', 'PUSH [$]', 'PUSHDEPLOYADDRESS', 'PUSH data', 'PUSHSIZE', 'PUSHIMMUTABLE', 'RETURNDATASIZE', 'RETURNDATACOPY', 'PUSH', 'DUP1', 'DUP2', 'DUP3', 'DUP4', 'DUP5', 'DUP6', 'DUP7', 'DUP8', 'DUP9', 'DUP10', 'DUP11', 'DUP12', 'DUP13', 'DUP14', 'DUP15', 'DUP16', 'SWAP1', 'SWAP2', 'SWAP3', 'SWAP4', 'SWAP5', 'SWAP6', 'SWAP7', 'SWAP8', 'SWAP9', 'SWAP10', 'SWAP11', 'SWAP12', 'SWAP13', 'SWAP14', 'SWAP15', 'SWAP16']



vocab_ = ['ADD', 'MUL', 'SUB', 'DIV', 'SDIV', 'MOD', 'SMOD', 'ADDMOD', 'ADDMOD', 'MULMOD', 'EXP', 'SIGNEXTEND', 'LT', 'GT', 'SLT', 'SGT', 'EQ', 'ISZERO', 'AND', 'OR', 'XOR', 'NOT', 'BYTE', 'SHL', 'SHR', 'SAR', 'ADDRESS', 'BALANCE', 'ORIGIN', 'CALLER', 'CALLVALUE', 'CALLDATALOAD', 'CALLDATASIZE', 'CODESIZE', 'GASPRICE', 'EXTCODESIZE', 'EXTCODEHASH', 'BLOCKHASH', 'COINBASE', 'TIMESTAMP', 'NUMBER', 'DIFFICULTY', 'PREVRANDAO', 'GASLIMIT', 'CHAINID', 'SELFBALANCE', 'BASEFEE', 'POP', 'MLOAD', 'MSTORE', 'MSTORE8', 'SLOAD', 'SSTORE', 'PC', 'GAS', 'KECCAK256', 'PUSH [tag]', 'PUSHLIB', 'PUSH #[$]', 'PUSH [$]', 'PUSHDEPLOYADDRESS', 'PUSH data', 'PUSHSIZE', 'PUSHIMMUTABLE', 'RETURNDATASIZE', 'RETURNDATACOPY', 'PUSH1', 'PUSH2', 'PUSH3', 'PUSH4', 'PUSH5', 'PUSH6', 'PUSH7', 'PUSH8', 'PUSH9', 'PUSH10', 'PUSH11', 'PUSH12', 'PUSH13', 'PUSH14', 'PUSH15', 'PUSH16', 'PUSH17', 'PUSH18', 'PUSH19', 'PUSH20', 'PUSH21', 'PUSH22', 'PUSH23', 'PUSH24', 'PUSH25', 'PUSH26', 'PUSH27', 'PUSH28', 'PUSH29', 'PUSH30', 'PUSH31', 'PUSH32', 'DUP1', 'DUP2', 'DUP3', 'DUP4', 'DUP5', 'DUP6', 'DUP7', 'DUP8', 'DUP9', 'DUP10', 'DUP11', 'DUP12', 'DUP13', 'DUP14', 'DUP15', 'DUP16', 'SWAP1', 'SWAP2', 'SWAP3', 'SWAP4', 'SWAP5', 'SWAP6', 'SWAP7', 'SWAP8', 'SWAP9', 'SWAP10', 'SWAP11', 'SWAP12', 'SWAP13', 'SWAP14', 'SWAP15', 'SWAP16']


vocab_sfs = ['ADD', 'MUL', 'SUB', 'DIV', 'SDIV', 'MOD', 'SMOD', 'ADDMOD', 'ADDMOD', 'MULMOD', 'EXP', 'SIGNEXTEND', 'LT', 'GT', 'SLT', 'SGT', 'EQ', 'ISZERO', 'AND', 'OR', 'XOR', 'NOT', 'BYTE', 'SHL', 'SHR', 'SAR', 'ADDRESS', 'BALANCE', 'ORIGIN', 'CALLER', 'CALLVALUE', 'CALLDATALOAD', 'CALLDATASIZE', 'CODESIZE', 'GASPRICE', 'EXTCODESIZE', 'EXTCODEHASH', 'BLOCKHASH', 'COINBASE', 'TIMESTAMP', 'NUMBER', 'DIFFICULTY', 'PREVRANDAO', 'GASLIMIT', 'CHAINID', 'SELFBALANCE', 'BASEFEE', 'MLOAD', 'MSTORE', 'MSTORE8', 'SLOAD', 'SSTORE', 'PC', 'GAS', 'KECCAK256', 'PUSH [tag]', 'PUSHLIB', 'PUSH #[$]', 'PUSH [$]', 'PUSHDEPLOYADDRESS', 'PUSH data', 'PUSHSIZE', 'PUSHIMMUTABLE', 'RETURNDATASIZE', 'RETURNDATACOPY', 'PUSH']



vocab_sfs_ = ['ADD', 'MUL', 'SUB', 'DIV', 'SDIV', 'MOD', 'SMOD', 'ADDMOD', 'ADDMOD', 'MULMOD', 'EXP', 'SIGNEXTEND', 'LT', 'GT', 'SLT', 'SGT', 'EQ', 'ISZERO', 'AND', 'OR', 'XOR', 'NOT', 'BYTE', 'SHL', 'SHR', 'SAR', 'ADDRESS', 'BALANCE', 'ORIGIN', 'CALLER', 'CALLVALUE', 'CALLDATALOAD', 'CALLDATASIZE', 'CODESIZE', 'GASPRICE', 'EXTCODESIZE', 'EXTCODEHASH', 'BLOCKHASH', 'COINBASE', 'TIMESTAMP', 'NUMBER', 'DIFFICULTY', 'PREVRANDAO', 'GASLIMIT', 'CHAINID', 'SELFBALANCE', 'BASEFEE', 'MLOAD', 'MSTORE', 'MSTORE8', 'SLOAD', 'SSTORE', 'PC', 'GAS', 'KECCAK256', 'PUSH [tag]', 'PUSHLIB', 'PUSH #[$]', 'PUSH [$]', 'PUSHDEPLOYADDRESS', 'PUSH data', 'PUSHSIZE', 'PUSHIMMUTABLE', 'RETURNDATASIZE', 'RETURNDATACOPY', 'PUSH1', 'PUSH2', 'PUSH3', 'PUSH4', 'PUSH5', 'PUSH6', 'PUSH7', 'PUSH8', 'PUSH9', 'PUSH10', 'PUSH11', 'PUSH12', 'PUSH13', 'PUSH14', 'PUSH15', 'PUSH16', 'PUSH17', 'PUSH18', 'PUSH19', 'PUSH20', 'PUSH21', 'PUSH22', 'PUSH23', 'PUSH24', 'PUSH25', 'PUSH26', 'PUSH27', 'PUSH28', 'PUSH29', 'PUSH30', 'PUSH31', 'PUSH32']


def is_pseudo_keyword(opcode: str) -> bool:
    if opcode.find("tag") ==-1 and opcode.find("#") ==-1 and opcode.find("$") ==-1 \
            and opcode.find("data") ==-1:
        return False
    else:
        return True


def split_bytecode(raw_instruction_str: str) -> List[str]:
    ops = raw_instruction_str.split(' ')
    opcodes = []
    i = 0

    while i < len(ops):
        op = ops[i]

        # In theory, they should not appear inside a block, as they are removed beforehand.
        # Nevertheless, we include them just in case
        if op.startswith("ASSIGNIMMUTABLE") or op.startswith("tag"):
            opcodes.append(op)
            i += 1
        elif not op.startswith("PUSH"):
            opcodes.append(op)
        else:
            # PUSH0 instructions are treated as PUSH0
            if op == "PUSH0":
                final_op = "PUSH 0"

            # PUSHDEPLOYADDRESS and PUSHSIZE has no value associated
            elif op.find("DEPLOYADDRESS") != -1 or op.find("SIZE") != -1:
                final_op = op

            # Just in case PUSHx instructions are included, we assign to them PUSH name instead
            elif re.fullmatch("PUSH([0-9]+)", op) is not None:
                final_op = "PUSH"
                i = i + 1

            # If position t+1 is a Yul Keyword, then it means we either have a simple PUSH instruction or one of the
            # pseudo PUSH that include a value as a second parameter
            elif not is_pseudo_keyword(ops[i + 1]):
                final_op = op
                i = i + 1
            # Otherwise, the opcode name is composed
            else:
                name_keyword = ops[i + 1]
                final_op = f'{op} {name_keyword}'
                i += 2
            opcodes.append(final_op)

        i += 1

    return opcodes

# this one keeps the 'i' in PUSHi and also its operand
#
def split_bytecode_(raw_instruction_str: str) -> List[str]:
    ops = raw_instruction_str.split(' ')
    opcodes = []
    i = 0
    operand = None
    size = None
    while i < len(ops):
        op = ops[i]
        # In theory, they should not appear inside a block, as they are removed beforehand.
        # Nevertheless, we include them just in case
        if op.startswith("ASSIGNIMMUTABLE") or op.startswith("tag"): # or op.startswith("PUSHIMMUTABLE"):
            opcodes.append(op)
            i += 1
        elif not op.startswith("PUSH"):
            opcodes.append(op)
        else:
            # PUSH0 instructions are treated as PUSH0
            # TODO: alternative representation depending on whether PUSH0 is considered as an opcode or not
            if op == "PUSH0":
                final_op = "PUSH1"
                operand = f'#0'

            # PUSHDEPLOYADDRESS and PUSHSIZE has no value associated
            elif op.find("DEPLOYADDRESS") != -1 or op.find("SIZE") != -1:
                final_op = op

            # Just in case PUSHx instructions are included, we assign to them PUSH name instead
            elif re.fullmatch("PUSH([0-9]+)", op) is not None:
                match = re.fullmatch("PUSH([0-9]+)", op)
                final_op = op
                operand = f'#{ops[i+1]}'
                i = i + 1
            # If position t+1 is a Yul Keyword, then it means we either have a simple PUSH instruction or one of the
            # pseudo PUSH that include a value as a second parameter
            elif not is_pseudo_keyword(ops[i + 1]):
                if op == "PUSH":
                    n =  (len(ops[i+1])+1) // 2
                    assert n >= 1 and n <= 32
                    final_op = f'PUSH{n}'
                    operand = f'#{ops[i+1]}'
                    i = i + 1
                else:
                    final_op = op
                    i = i + 1
            # Otherwise, the opcode name is composed
            else:
                name_keyword = ops[i + 1]
                final_op = f'{op} {name_keyword}'
                operand = f'#{ops[i+2]}'
                i += 2
            
            opcodes.append(final_op)
            if operand is not None:
                opcodes.append(operand)
                operand=None

        i += 1

    return opcodes


if __name__ == "__main__":
    test1 = "DUP2 ADD SWAP1 PUSH 40 PUSH1 40 DUP2 DUP4 SUB SLT PUSH [tag] 11 PUSHSIZE PUSH4 2222"
    test2 = "PUSH 20 SWAP1 MLOAD PUSH FF PUSHIMMUTABLE 921 AND DUP2 MSTORE PUSH #[$] 23"
    print(split_bytecode_(test1))
    print(split_bytecode_(test2))
