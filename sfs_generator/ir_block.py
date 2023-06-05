#Pablo Gordillo

import os
import traceback
from timeit import default_timer as dtimer

import global_params.paths as paths
from sfs_generator.gasol_optimization import smt_translate_block
from sfs_generator.rbr_rule import RBRRule
from sfs_generator.utils import get_push_number_hex, isYulInstruction

'''
It initialize the globals variables. 
-List opcodeX contains the evm bytecodes from set X.
-current_local_var has the max index of the local variables created.
-rbr_blocks is a mapping rbr_id->list of rbr rules (jumps contains 2 rules per rbr_id).
-stack_index is a mapping block_id->[stack_height_begin, stack_heigh_end].
-max_field_list keeps the id of the known fields accessed during the execution.
-bc_in_use keeps the contract data used during the execution.
-new fid keeps the index of the new fresh variable.
'''
def init_globals():
    
    global opcodes0
    opcodes0 = ["STOP", "ADD", "MUL", "SUB", "DIV", "SDIV", "MOD",
                "SMOD", "ADDMOD", "MULMOD", "EXP", "SIGNEXTEND"]

    global opcodes10
    opcodes10 = ["LT", "GT", "SLT", "SGT", "EQ", "ISZERO", "AND", "OR",
                 "XOR", "NOT", "BYTE","SHL","SHR","SAR"]

    global opcodes20
    opcodes20 = ["SHA3","KECCAK256"]

    global opcodes30
    opcodes30 = ["ADDRESS", "BALANCE", "ORIGIN", "CALLER",
                 "CALLVALUE", "CALLDATALOAD", "CALLDATASIZE",
                 "CALLDATACOPY", "CODESIZE", "CODECOPY", "GASPRICE",
                 "EXTCODESIZE", "EXTCODECOPY", "MCOPY","EXTCODEHASH"]

    global opcodes40
    opcodes40 = ["BLOCKHASH", "COINBASE", "TIMESTAMP", "NUMBER",
                 "DIFFICULTY", "PREVRANDAO", "GASLIMIT","SELFBALANCE","CHAINID","BASEFEE"]

    global opcodes50
    opcodes50 = ["POP", "MLOAD", "MSTORE", "MSTORE8", "SLOAD",
                 "SSTORE", "JUMP", "JUMPI", "PC", "MSIZE", "GAS", "JUMPDEST",
                 "SLOADEXT", "SSTOREEXT", "SLOADBYTESEXT", "SSTOREBYTESEXT"]

    global opcodes60
    opcodes60 = ["PUSH"]

    global opcodes80
    opcodes80 = ["DUP"]

    global opcodes90
    opcodes90 = ["SWAP"]

    global opcodesA
    opcodesA = ["LOG0", "LOG1", "LOG2", "LOG3", "LOG4"]

    global opcodesF
    opcodesF = ["CREATE", "CALL", "CALLCODE", "RETURN", "REVERT",
                "ASSERTFAIL", "DELEGATECALL", "BREAKPOINT", "RNGSEED", "SSIZEEXT",
                "SLOADBYTES", "SSTOREBYTES", "SSIZE", "STATEROOT", "TXEXECGAS",
                "CALLSTATIC", "INVALID", "SUICIDE","STATICCALL","CREATE2"]

    global opcodesZ
    opcodesZ = ["RETURNDATACOPY","RETURNDATASIZE"]

    global opcodesYul
    opcodesYul = ["PUSH [tag]","PUSH #[$]","PUSH [$]", "PUSH data", "PUSHDEPLOYADDRESS", "ASSIGNIMMUTABLE","PUSHSIZE","PUSHIMMUTABLE","PUSHLIB"]
    
    global current_local_var
    current_local_var = 0
        
    global rbr_blocks
    rbr_blocks = {}

    global stack_index
    stack_index = {}

    global top_index
    top_index = 0

    global blockhash_cont
    blockhash_cont = 0

    global pc_cont
    pc_cont = 0

    global mload_counter
    mload_counter = 0
    
    global sload_counter
    sload_counter = 0

    global gas_counter
    gas_counter = 0

    global hash_counter
    hash_counter = 0

    global timestamp_counter
    timestamp_counter = 0

    global assignImmutable_counter
    assignImmutable_counter = 0

    global assignImmutable_dict
    assignImmutable_dict = {}


'''
Given a block it returns a list containingn the height of its
stack when arriving and leaving the block.
-bock:block start address. int.
-It returns a list with 2 elements. [int, int].
'''
def get_stack_index(block):
    try:
        return stack_index[block]
    
    except:
        return [0,0]


def update_top_index(val):
    global top_index

    if top_index < val:
        top_index = val
        

'''
It is used when a bytecode consume stack variables. It returns the
current stack variable (the top most one) and after that update the variable index.
index_variables contains the index of current stack variable.
-index_variables: int.
-It returns a tuple (stack variable, top stack index). (string, int).
'''
def get_consume_variable(index_variables):
    current = index_variables
    if current >= 0 :
        variable = "s(" + str(current) + ")"
        current = current-1
        
    return  variable, current


'''
It returns the next fresh stack variable and updates the current
index.
-index_variables: int.
-It returns a tuple (stack variable, top stack index). (string, int).
'''
def get_new_variable(index_variables):
    new_current = index_variables + 1
    update_top_index(new_current)
    return "s(" + str(new_current) + ")", new_current


'''
It returns the variable palced in the top of stack.
-index_variables: int.
variable: stack variable returned. string.
'''
def get_current_variable(index_variables):
    current = index_variables
    if current >= 0 :
        variable = "s(" + str(current) + ")"

    return variable

'''
It returns a list that contains all the stack variables which are "active".
It goes from current to 0. 
s_vars: [string].
'''
def get_stack_variables(index_variables):
    current = index_variables
    s_vars = []
    for i in range(current,-1,-1):
        s_vars.append("s("+str(i)+")")

    return s_vars


'''
It returns the posth variable.
index_variables: top stack index. int.
pos: position of the variable required. int.
variable: stack variable returned. string.
'''
def get_ith_variable(index_variables, pos):
    current = index_variables
    if (current >= pos):
        idx = current-pos
        variable = "s(" + str(idx) + ")"
        
    return variable
                
'''
It simulates the execution of evm bytecodes.  It consumes or
generates variables depending on the bytecode and returns the
corresponding translated instruction and the variables's index
updated. It also updated the corresponding global variables.
'''
def translateOpcodes0(opcode,index_variables):
    if opcode == "ADD":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_new_variable(updated_variables)
        instr = v3+" = " + v1 + "+" + v2
    elif opcode == "MUL":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_new_variable(updated_variables)
        instr = v3+" = " + v1 + "*" + v2
    elif opcode == "SUB":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_new_variable(updated_variables)
        instr = v3+" = " + v1 + "-" + v2
    elif opcode == "DIV":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_new_variable(updated_variables)
        instr = v3+" = " + v1 + "/" + v2
    elif opcode == "SDIV":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_new_variable(updated_variables)
        instr = v3+" = " + v1 + "/" + v2
    elif opcode == "MOD":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_new_variable(updated_variables)
        instr = v3+" = " + v1 + "%" + v2
    elif opcode == "SMOD":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_new_variable(updated_variables)
        instr = v3+" = " + v1 + "%" + v2
    elif opcode == "ADDMOD":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_consume_variable(updated_variables)
        v4, updated_variables = get_new_variable(updated_variables)
        instr = v4+" = addmod(" + v1 + "," + v2 + ", " + v3+")"
    elif opcode == "MULMOD":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_consume_variable(updated_variables)
        v4, updated_variables = get_new_variable(updated_variables)
        instr = v4+" = mulmod(" + v1 + "," + v2 + ","  + v3+")"
    elif opcode == "EXP":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_new_variable(updated_variables)
        instr = v3+" = " + v1 + "^" + v2
    elif opcode == "SIGNEXTEND":
        v0_aux, updated_variables = get_consume_variable(index_variables)
        v0, updated_variables = get_consume_variable(updated_variables)
        v1, updated_variables = get_new_variable(updated_variables)

        instr = v1+" = signextend("+v0_aux+","+v0+")"

    elif opcode == "STOP":
        instr = "stop(s("+str(index_variables)+"))"
        updated_variables = index_variables

    else:
        instr = "Error opcodes0: "+opcode
        updated_variables = index_variables

    return instr, updated_variables


'''
It simulates the execution of evm bytecodes.  It consumes or
generates variables depending on the bytecode and returns the
corresponding translated instruction and the variables's index
updated. It also updated the corresponding global variables.
'''
def translateOpcodes10(opcode, index_variables,cond):
    if opcode == "LT":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3 , updated_variables = get_new_variable(updated_variables)
        if cond :
            instr = v3+ " = lt(" + v1 + ", "+v2+")"
        else :
            instr = "lt(" + v1 + ", "+v2+")"
        
    elif opcode == "GT":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3 , updated_variables = get_new_variable(updated_variables)
        if cond :
            instr = v3+ " = gt(" + v1 + ", "+v2+")"
        else :
            instr = "gt(" + v1 + ", "+v2+")"


    elif opcode == "SLT":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3 , updated_variables = get_new_variable(updated_variables)
        if cond :
            instr = v3+ " = slt(" + v1 + ", "+v2+")"
        else :
            instr = "slt(" + v1 + ", "+v2+")"

    elif opcode == "SGT":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3 , updated_variables = get_new_variable(updated_variables)
        if cond :
            instr = v3+ " = sgt(" + v1 + ", "+v2+")"
        else :
            instr = "sgt(" + v1 + ", "+v2+")"

    elif opcode == "EQ":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3 , updated_variables = get_new_variable(updated_variables)
        if cond:
            instr = v3+ "= eq(" + v1 + ", "+v2+")"
        else:
            instr = "eq(" + v1 + ", "+v2+")"

    elif opcode == "ISZERO":
        v1, updated_variables = get_consume_variable(index_variables)
        v2 , updated_variables = get_new_variable(updated_variables)
        if cond:
            instr = v2+ "= eq(" + v1 + ", 0)"
        else:
            instr = "eq(" + v1 + ", 0)"

    elif opcode == "AND":
            v1, updated_variables = get_consume_variable(index_variables)
            v2, updated_variables = get_consume_variable(updated_variables)
            v3, updated_variables = get_new_variable(updated_variables)
            instr = v3+" = and(" + v1 + ", " + v2+")"

    elif opcode == "OR":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_new_variable(updated_variables)
        instr = v3+" = or(" + v1 + ", " + v2+")"

    elif opcode == "XOR":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_new_variable(updated_variables)
        instr = v3+" = xor(" + v1 + ", " + v2+")"

    elif opcode == "NOT":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_new_variable(updated_variables)
        instr = v2+" = not(" + v1 + ")"

    elif opcode == "BYTE":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)
        v2, updated_variables = get_new_variable(updated_variables)
        instr = v2+" = byte(" + v0 + " , " + v1 + ")"

    elif opcode == "SHL":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)
        v2, updated_variables = get_new_variable(updated_variables)
        instr = v2+" = shl(" + v0 + " , " + v1 + ")" 

    elif opcode == "SHR":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)
        v2, updated_variables = get_new_variable(updated_variables)
        instr = v2+" = shr(" + v0 + " , " + v1 + ")" 

    elif opcode == "SAR":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)
        v2, updated_variables = get_new_variable(updated_variables)
        instr = v2+" = sar(" + v0 + " , " + v1 + ")" 

    else:    
        instr = "Error opcodes10: "+ opcode
        updated_variables = index_variables

    return instr, updated_variables


'''
It simulates the execution of evm bytecodes.  It consumes or
generates variables depending on the bytecode and returns the
corresponding translated instruction and the variables's index
updated. It also updated the corresponding global variables.
'''
def translateOpcodes20(opcode, index_variables):
    global hash_counter

    if opcode == "SHA3":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_new_variable(updated_variables)
        instr = v3+" = sha3+"+str(hash_counter)+"("+ v1+", "+v2+")"
        hash_counter+=1
    elif opcode == "KECCAK256":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_new_variable(updated_variables)
        instr = v3+" = keccak256"+str(hash_counter)+"("+ v1+", "+v2+")"
        hash_counter+=1
    else:
        instr = "Error opcodes20: "+opcode
        updated_variables = index_variables
    
    return instr, updated_variables

'''
It simulates the execution of evm bytecodes.  It consumes or
generates variables depending on the bytecode and returns the
corresponding translated instruction and the variables's index
updated. It also updated the corresponding global variables.
'''
def translateOpcodes30(opcode, value, index_variables):
    
    if opcode == "ADDRESS":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = address"

    elif opcode == "BALANCE":
        _, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_new_variable(updated_variables)
        instr = v1+" = balance"

    elif opcode == "ORIGIN":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = origin"

    elif opcode == "CALLER":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = caller"

    elif opcode == "CALLVALUE":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = callvalue"

    elif opcode == "CALLDATALOAD":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_new_variable(updated_variables)

        instr = v1+" = calldataload"

            
    elif opcode == "CALLDATASIZE":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = calldatasize"

    elif opcode == "CALLDATACOPY":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)
        v2, updated_variables = get_consume_variable(updated_variables)

        instr = "calldatacopy("+v0+","+v1+","+v2+")"
        
    elif opcode == "CODESIZE":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = codesize"

    elif opcode == "CODECOPY":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)
        v2, updated_variables = get_consume_variable(updated_variables)

        instr = "calldatacopy("+v0+","+v1+","+v2+")"  
        
    elif opcode == "GASPRICE":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = gasprice"

    elif opcode == "EXTCODESIZE":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_new_variable(updated_variables)
        instr = v1+" = extcodesize"

    elif opcode == "EXTCODECOPY":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_consume_variable(updated_variables)

        instr = "extcodecopy("+v0+","+v1+","+v2+","+v3+")"

    elif opcode == "EXTCODEHASH":
        _, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_new_variable(updated_variables)
        instr = v1+" = extcodehash("+v1+")"  
        
    elif opcode == "MCOPY":
        pass
    else:
        instr = "Error opcodes30: "+opcode
        updated_variables = index_variables

    return instr, updated_variables


'''
It simulates the execution of evm bytecodes.  It consumes or
generates variables depending on the bytecode and returns the
corresponding translated instruction and the variables's index
updated. It also updated the corresponding global variables.
'''
def translateOpcodes40(opcode, index_variables):
    global blockhash_cont
    global timestamp_counter
    
    if opcode == "BLOCKHASH":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_new_variable(updated_variables)
        instr = v1+" = blockhash_"+str(blockhash_cont)

        blockhash_cont +=1
    elif opcode == "COINBASE":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = coinbase"

    elif opcode == "TIMESTAMP":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = timestamp"+str(timestamp_counter)
        timestamp_counter+=1

    elif opcode == "NUMBER":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = number"

    elif opcode == "DIFFICULTY":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = difficulty"

    elif opcode == "PREVRANDAO":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = prevrandao"

    elif opcode == "BASEFEE":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = basefee"

        
    elif opcode == "GASLIMIT":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = gaslimit"

    elif opcode == "SELFBALANCE":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = selfbalance"

    elif opcode == "CHAINID":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = chainid"


    else:
        instr = "Error opcodes40: "+opcode
        updated_variables = index_variables

    return instr, updated_variables


'''
It simulates the execution of evm bytecodes.  It consumes or
generates variables depending on the bytecode and returns the
corresponding translated instruction and the variables's index
updated. It also updated the corresponding global variables.
'''
def translateOpcodes50(opcode, value, index_variables):
    global pc_cont
    global sload_counter
    global mload_counter
    global gas_counter
    
    if opcode == "POP":        
        v1, updated_variables = get_consume_variable(index_variables)
        instr=""
    elif opcode == "MLOAD":
        _ , updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_new_variable(updated_variables)

        instr = v1+" = mload"+str(mload_counter)+"("+v1+")"
        mload_counter+=1
        
    elif opcode == "MSTORE":
        v0 , updated_variables = get_consume_variable(index_variables)
        v1 , updated_variables = get_consume_variable(updated_variables)

        instr = "mstore("+v0+","+v1+")"
            
    elif opcode == "MSTORE8":
        v0 , updated_variables = get_consume_variable(index_variables)
        v1 , updated_variables = get_consume_variable(updated_variables)
        
        instr = "mstore8("+v0+","+v1+")"

    elif opcode == "SLOAD":
        _ , updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_new_variable(updated_variables)

        instr = v1+" = sload"+str(sload_counter)+"("+v1+")"
        sload_counter+=1

    elif opcode == "SSTORE":
        v0 , updated_variables = get_consume_variable(index_variables)
        v1 , updated_variables = get_consume_variable(updated_variables)

        instr = "sstore("+v0+","+v1+")"

    elif opcode == "PC":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1 + " = pc"+str(pc_cont)
        pc_cont+=1

    elif opcode == "MSIZE":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1 + " = msize"

    elif opcode == "GAS":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = "+"gas"+str(gas_counter)
        gas_counter+=1
    elif opcode == "JUMPDEST":
        instr = ""
        updated_variables = index_variables
    # elif opcode == "SLOADEXT":
    #     pass
    # elif opcode == "SSTOREEXT":
    #     pass
    # elif opcode == "SLOADBYTESEXT":
    #     pass
    # elif opcode == "SSTOREBYTESEXT":
    #     pass
    else:
        instr = "Error opcodes50: "+ opcode
        updated_variables = index_variables

    return instr, updated_variables
'''
It simulates the execution of evm bytecodes.  It consumes or
generates variables depending on the bytecode and returns the
corresponding translated instruction and the variables's index
updated. It also updated the corresponding global variables.
They corresponds to LOGS opcodes.
'''
def translateOpcodesA(opcode, index_variables):

    if opcode == "LOG0":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)

        instr = "log0("+v0+","+v1+")"  

    elif opcode == "LOG1":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)
        v2, updated_variables = get_consume_variable(updated_variables)

        instr = "log1("+v0+","+v1+","+v2+")"  

    elif opcode == "LOG2":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_consume_variable(updated_variables)

        instr = "log2("+v0+","+v1+","+v2+","+v3+")"  

    elif opcode == "LOG3":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_consume_variable(updated_variables)
        v4, updated_variables = get_consume_variable(updated_variables)

        instr = "log3("+v0+","+v1+","+v2+","+v3+","+v4+")"  
        
    elif opcode == "LOG4":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_consume_variable(updated_variables)
        v4, updated_variables = get_consume_variable(updated_variables)
        v5, updated_variables = get_consume_variable(updated_variables)

        instr = "log4("+v0+","+v1+","+v2+","+v3+","+v4+","+v5+")"  
        
    else:
        instr = "Error opcodesA: "+ opcode
    
    return instr, updated_variables


'''
It simulates the execution of evm bytecodes.  It consumes or
generates variables depending on the bytecode and returns the
corresponding translated instruction and the variables's index
updated. It also updated the corresponding global variables.
'''
def translateOpcodesF(opcode, index_variables, addr):
    if opcode == "CREATE":
        v00, updated_variables = get_consume_variable(index_variables)
        v01, updated_variables = get_consume_variable(updated_variables)
        v02, updated_variables = get_consume_variable(updated_variables)
        v1, updated_variables = get_new_variable(updated_variables)

        instr = v1+" = create("+v00+","+v01+","+v02+")"

    elif opcode == "CREATE2":
        v00, updated_variables = get_consume_variable(index_variables)
        v01, updated_variables = get_consume_variable(updated_variables)
        v02, updated_variables = get_consume_variable(updated_variables)
        v03, updated_variables = get_consume_variable(updated_variables)
        v1, updated_variables = get_new_variable(updated_variables)

        val = " = create2("+v00+","+v01+","+v02+","+v03+")"

        instr = v1+" = "+val
            
    elif opcode == "CALL": #Suppose that all the calls are executed without errors
        v00, updated_variables = get_consume_variable(index_variables)
        v01, updated_variables = get_consume_variable(updated_variables)
        v02, updated_variables = get_consume_variable(updated_variables)
        v03, updated_variables = get_consume_variable(updated_variables)
        v04, updated_variables = get_consume_variable(updated_variables)
        v05, updated_variables = get_consume_variable(updated_variables)
        v06, updated_variables = get_consume_variable(updated_variables)
        v1, updated_variables = get_new_variable(updated_variables)

        instr = v1+" = call("+v00+","+v01+","+v02+","+v03+","+v04+","+v05+","+v06+")"  
        
    elif opcode == "CALLCODE":
        v00, updated_variables = get_consume_variable(index_variables)
        v01, updated_variables = get_consume_variable(updated_variables)
        v02, updated_variables = get_consume_variable(updated_variables)
        v03, updated_variables = get_consume_variable(updated_variables)
        v04, updated_variables = get_consume_variable(updated_variables)
        v05, updated_variables = get_consume_variable(updated_variables)
        v06, updated_variables = get_consume_variable(updated_variables)
        v1, updated_variables = get_new_variable(updated_variables)

        instr = v1+" = callcode("+v00+","+v01+","+v02+","+v03+","+v04+","+v05+","+v06+")"  
        
    elif opcode == "RETURN":

        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)

        instr = "return("+v0+","+v1+")"

    elif opcode == "REVERT":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)

        instr = "revert("+v0+","+v1+")"

    elif opcode == "ASSERTFAIL":

        instr = "assertfail(s("+str(index_variables)+"))"

        updated_variables = index_variables
    elif opcode == "DELEGATECALL":
        v00, updated_variables = get_consume_variable(index_variables)
        v01, updated_variables = get_consume_variable(updated_variables)
        v02, updated_variables = get_consume_variable(updated_variables)
        v03, updated_variables = get_consume_variable(updated_variables)
        v04, updated_variables = get_consume_variable(updated_variables)
        v05, updated_variables = get_consume_variable(updated_variables)
        v1, updated_variables = get_new_variable(updated_variables)

        instr = v1+" = delegatecall("+v00+","+v01+","+v02+","+v03+","+v04+","+v05+")"  


    elif opcode == "STATICCALL":
        v00, updated_variables = get_consume_variable(index_variables)
        v01, updated_variables = get_consume_variable(updated_variables)
        v02, updated_variables = get_consume_variable(updated_variables)
        v03, updated_variables = get_consume_variable(updated_variables)
        v04, updated_variables = get_consume_variable(updated_variables)
        v05, updated_variables = get_consume_variable(updated_variables)
        v1, updated_variables = get_new_variable(updated_variables)

        instr = v1+" = staticcall("+v00+","+v01+","+v02+","+v03+","+v04+","+v05+")"  

    elif opcode == "CALLSTATIC":
        v00, updated_variables = get_consume_variable(index_variables)
        v01, updated_variables = get_consume_variable(updated_variables)
        v02, updated_variables = get_consume_variable(updated_variables)
        v03, updated_variables = get_consume_variable(updated_variables)
        v04, updated_variables = get_consume_variable(updated_variables)
        v05, updated_variables = get_consume_variable(updated_variables)
        v06, updated_variables = get_consume_variable(updated_variables)
        v1, updated_variables = get_new_variable(updated_variables)

        instr = v1+" = callstatic("+v00+","+v01+","+v02+","+v03+","+v04+","+v05+","+v06+")"  

    elif opcode == "SUICIDE":
        v0, updated_variables = get_consume_variable(index_variables)
        
        instr = "suicide("+v0+")"

    else:
        instr = "Error opcodesF: "+opcode
        updated_variables = index_variables

    return instr, updated_variables

        
'''
It simulates the execution of evm bytecodes.  It consumes or
generates variables depending on the bytecode and returns the
corresponding translated instruction and the variables's index
updated. It also updated the corresponding global variables.
-value is astring that contains the number pushed to the stack.
'''
def translateOpcodes60(opcode, value, index_variables):

    if opcode.startswith("PUSH0"):
        v1,updated_variables = get_new_variable(index_variables)
        instr = v1+" = 0"
    
    elif opcode.startswith("PUSH"):
        v1,updated_variables = get_new_variable(index_variables)
        dec_value = int(value,16)
        instr = v1+" = " + str(dec_value)
    else:
        instr = "Error opcodes60: "+opcode
        updated_variables = index_variables

    return instr, updated_variables


'''
It simulates the execution of dup bytecode.
It simulates the execution of evm bytecodes.  It consumes or
generates variables depending on the bytecode and returns the
corresponding translated instruction and the variables's index
updated. It also updated the corresponding global variables.

It duplicates what is stored in the stack at pos value (when
value == 1, it duplicates the top of the stack) .
-value refers to the position to be duplicated. string.
'''
def translateOpcodes80(opcode, value, index_variables):
    if opcode == "DUP":
        v1 = get_ith_variable(index_variables,int(value)-1)
        v2, updated_variables= get_new_variable(index_variables)
        instr = v2+" = "+v1
    else:
        instr = "Error opcodes80: "+opcode
        updated_variables = index_variables

    return instr, updated_variables


'''
It simulates the execution of swap bytecode.
It simulates the execution of evm bytecodes.  It consumes or
generates variables depending on the bytecode and returns the
corresponding translated instruction and the variables's index
updated. It also updated the corresponding global variables.
-value refers to the position involved in the swap. string.
'''
def translateOpcodes90(opcode, value, index_variables):
    if opcode == "SWAP":
        v1 = get_ith_variable(index_variables,int(value))
        v2 = get_current_variable(index_variables)
        v3,_ = get_new_variable(index_variables)
        instr1 = v3 + " = " + v1
        instr2 = v1 + " = " + v2
        instr3 = v2 + " = " + v3
        instr = [instr1,instr2,instr3]
    else:
        instr = "Error opcodes90: "+opcode

    return instr, index_variables

'''
It simulates the execution of evm bytecodes.  It consumes or
generates variables depending on the bytecode and returns the
corresponding translated instruction and the variables's index
updated. It also updated the corresponding global variables.
Unclassified opcodes.
'''
def translateOpcodesZ(opcode, index_variables):
    if opcode == "RETURNDATASIZE":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = returndatasize"

    elif opcode == "RETURNDATACOPY":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        
        instr = "returndatacopy("+v0+","+v1+","+v2+")"

    else:
        instr = "Error opcodesZ: "+opcode

    return instr, updated_variables

def translateYulOpcodes(opcode, value, index_variables):
    global assignImmutable_dict
    global assignImmutable_counter
    
    if opcode == "ASSIGNIMMUTABLE":
        v0 , updated_variables = get_consume_variable(index_variables)
        v1 , updated_variables = get_consume_variable(updated_variables)


        #It is treated as a special mstore. The value is stored in a
        #mapping bounded to a unique identifier. It is used when
        #reconstructing the opcode in gasol_optimizer.py
        
        #instr = "assignimmutable("+v0+","+v1+","+value+")"

        instr = "mstoreImmutable"+str(assignImmutable_counter)+"("+v0+","+v1+")"
        assignImmutable_dict[assignImmutable_counter] = value
        assignImmutable_counter+=1

        
    elif opcode == "PUSHDEPLOYADDRESS":
        v1,updated_variables = get_new_variable(index_variables)
        instr = v1+" = pushdeployaddress"

    elif opcode == "PUSHSIZE":
        v1,updated_variables = get_new_variable(index_variables)
        instr = v1+" = pushsize"

        
    else:
        v1,updated_variables = get_new_variable(index_variables)
        dec_value = int(value,16)

        if opcode == "PUSH [tag]":
            instr = v1+" = pushtag(" + str(value)+")"

        elif opcode == "PUSH #[$]":
            instr = v1+" = push#[$](" + str(dec_value)+")"

        elif opcode == "PUSH [$]":
            instr = v1+" = push[$](" + str(dec_value)+")"
            
        elif opcode == "PUSH data":
            instr = v1+" = pushdata(" + str(dec_value)+")"

        elif opcode == "PUSHIMMUTABLE":
            instr = v1+" = pushimmutable(" + str(dec_value)+")"

        elif opcode == "PUSHLIB":
            instr = v1+" = pushlib(" + str(dec_value)+")"

    return instr, updated_variables

'''
It translates the bytecode corresponding to evm_opcode.
We mantain some empty instructions to insert the evm bytecodes.
They are remove when displaying.
-rule refers to the rule that is being built. rbr_rule instance.
-evm_opcode is the bytecode to be translated. string.
-list_jumps contains the addresses of next blocks.
-cond is True if the conditional statemnt refers to a guard. False otherwise.
-nop is True when generating nop annotations with the opcode. False otherwise.
-index_variables refers to the top stack index. int.
'''
def compile_instr(rule,evm_opcode,variables,list_jumps,cond):
    opcode = evm_opcode.split(" ")

    if len(opcode) > 1:
        opcode_name = ' '.join(opcode[:-1])
        opcode_rest = opcode[-1]
    else:
        opcode_name = opcode[0]
        opcode_rest = ""

    # print(opcode_name, opcode_rest)

    if opcode_name in opcodes0:
        value, index_variables = translateOpcodes0(opcode_name, variables)
        rule.add_instr(value)
    elif opcode_name in opcodes10:
        value, index_variables = translateOpcodes10(opcode_name, variables,cond)
        rule.add_instr(value)
    elif opcode_name in opcodes20:
        value, index_variables = translateOpcodes20(opcode_name, variables)
        rule.add_instr(value)
    elif opcode_name in opcodes30:
        value, index_variables = translateOpcodes30(opcode_name,opcode_rest,variables)
        rule.add_instr(value)
    elif opcode_name in opcodes40:
        value, index_variables = translateOpcodes40(opcode_name,variables)
        rule.add_instr(value)
    elif opcode_name in opcodes50:
        value, index_variables = translateOpcodes50(opcode_name, opcode_rest, variables)
        if type(value) is list:
            for ins in value:
                rule.add_instr(ins)
        else:
            rule.add_instr(value)
    elif opcode_name[:4] in opcodes60 and not isYulInstruction(opcode_name):
        if opcode_name.startswith("PUSH0"):
            opcode_rest = "0"
            
        value, index_variables = translateOpcodes60(opcode_name, opcode_rest, variables)
        pushid = get_push_number_hex(opcode_rest)
        rule.add_instr(value)
    elif opcode_name[:3] in opcodes80:
        value, index_variables = translateOpcodes80(opcode_name[:3], opcode_name[3:], variables)
        rule.add_instr(value)
    elif opcode_name[:4] in opcodes90:
        value, index_variables = translateOpcodes90(opcode_name[:4], opcode_name[4:], variables)

        for ins in value: #SWAP returns a list (it is translated into 3 instructions)
            rule.add_instr(ins)
            
    elif opcode_name in opcodesA:
        value, index_variables = translateOpcodesA(opcode_name, variables)
        rule.add_instr(value)
    elif opcode_name in opcodesF:
        value, index_variables = translateOpcodesF(opcode_name,variables,opcode_rest)
        #RETURN
        rule.add_instr(value)
    elif opcode_name in opcodesZ:
        value, index_variables = translateOpcodesZ(opcode_name,variables)
        rule.add_instr(value)
    elif opcode_name in opcodesYul:
        value, index_variables = translateYulOpcodes(opcode_name,opcode_rest,variables)
        rule.add_instr(value)
        if evm_opcode.startswith("ASSIGNIMMUTABLE"):
            evm_opcode = "ASSIGNIMMUTABLE"
    else:
        value = "Error. No opcode matchs"
        index_variables = variables
        rule.add_instr(value)

    rule.add_instr("nop("+evm_opcode+")")
    return index_variables

    
'''
It generates the rbr rules corresponding to a block from the CFG.
index_variables points to the corresponding top stack index.
The stack could be reconstructed as [s(ith)...s(0)].
'''
def compile_block(instrs,input_stack,block_id):
    global rbr_blocks
    global top_index

    cont = 0
    top_index = 0
    finish = False
    
    index_variables = input_stack-1
    rule = RBRRule(block_id, "block",False)

    rule.set_index_input(input_stack)
    l_instr = instrs

    
    while not(finish) and cont< len(l_instr):
        # if l_instr[cont].find("KECCAK")!=-1 and l_instr[cont-1].find("MSTORE")!=-1:
        #     #print("KECCYES")
        index_variables = compile_instr(rule,l_instr[cont],index_variables,[],True)        
        cont+=1

    rule.set_fresh_index(top_index)

    return rule


'''
It creates a file with the rbr rules generated for the programa
analyzed. If it contains more than 1 smart contract it creates a file
for each smart contract.
-rbr is a list containing instances of rbr_rule.
-executions refers to the number of smart contract that has been translated. int.
'''
def write_rbr(rule,block_name):
    if paths.gasol_folder not in os.listdir(paths.tmp_path):
        os.mkdir(paths.gasol_path)

    name = paths.gasol_path+block_name+".rbr"
        
    with open(name,"w") as f:
        f.write(rule.rule2string()+"\n")

    f.close()
        
            
'''
Main function that build the rbr representation from the CFG of a solidity file.
-blocks_input contains a list with the blocks of the CFG. basicblock.py instances.
-stack_info is a mapping block_id => height of the stack.
-block_unbuild is a list that contains the id of the blocks that have not been considered yet. [string].
-nop_opcodes is True if it has to annotate the evm bytecodes.
-saco_rbr is True if it has to generate the RBR in SACO syntax.
-exe refers to the number of smart contracts analyzed.
'''
def evm2rbr_compiler(file_name = None,block = None, block_id = -1, block_name = "",simplification = True, storage = False, size = False, part = False, pop = False, push = False, revert = False, debug_info = False):
    global rbr_blocks
    
    init_globals()
    
    begin = dtimer()

    try:
        instructions = block["instructions"]
        input_stack = int(block["input"])
        
        rule = compile_block(instructions,input_stack,block_id)

        has_sto = has_storage_ins(instructions)

        write_rbr(rule,block_name)

        # print(preffix)
        
        end = dtimer()
        ethir_time = end-begin
        #print("Build RBR: "+str(ethir_time)+"s")

        subblocks = smt_translate_block(rule,file_name,block_name,assignImmutable_dict,simplification,storage, size, part, pop, push, revert,debug_info)
                
        return 0, subblocks
        
    except Exception as e:
        traceback.print_exc()
        raise Exception("Error in RBR generation",4)
            

def has_storage_ins(instructions):
    if "MSTORE" in instructions or "SSTORE" in instructions or "MSTORE8" in instructions:
        return True
    else:
        return False
