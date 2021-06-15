#Pablo Gordillo
import re

from rbr_rule import RBRRule
import opcodes as opcodes
from basicblock import Tree
from utils import getKey, orderRBR, getLevel, store_times
import os
# import saco
# import c_translation
# import c_utranslation
from timeit import default_timer as dtimer
from graph_scc import get_entry_scc
import traceback

from syrup_optimization import smt_translate_isolate
from global_params import costabs_path, tmp_path, costabs_folder


# costabs_path = "/tmp/costabs/" 
# tmp_path = "/tmp/"

'''
It initialize the globals variables. 
-List opcodeX contains the evm bytecodes from set X.
-current_local_var has the max index of the local variables created.
-local_variables is a mapping address->local_variable if known.
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
    opcodes20 = ["SHA3"]

    global opcodes30
    opcodes30 = ["ADDRESS", "BALANCE", "ORIGIN", "CALLER",
                 "CALLVALUE", "CALLDATALOAD", "CALLDATASIZE",
                 "CALLDATACOPY", "CODESIZE", "CODECOPY", "GASPRICE",
                 "EXTCODESIZE", "EXTCODECOPY", "MCOPY","EXTCODEHASH"]

    global opcodes40
    opcodes40 = ["BLOCKHASH", "COINBASE", "TIMESTAMP", "NUMBER",
                 "DIFFICULTY", "GASLIMIT","SELFBALANCE","CHAINID"]

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
    opcodesYul = ["PUSHTAG","PUSH#[$]","PUSH[$]","ASSIGNINMUTABLE"]
    
    global current_local_var
    current_local_var = 0

    global local_variables
    local_variables = {}
    
    global lvariables_per_block
    lvariables_per_block = {}
    
    global rbr_blocks
    rbr_blocks = {}

    global stack_index
    stack_index = {}
    
    # global max_field_list
    # max_field_list = []

    # global bc_in_use
    # bc_in_use = []

    global bc_per_block
    bc_per_block = {}

    global top_index
    top_index = 0

    global new_fid
    new_fid = 0

    global fields_per_block
    fields_per_block = {}

    global cloned_blocks
    cloned_blocks = []

    global vertices
    vertices = {}

    global all_state_vars
    all_state_vars = []


    # global unknown_mstore
    # unknown_mstore = False

    global blockhash_cont
    blockhash_cont = 0

    global pc_cont
    pc_cont = 0
    
    global c_trans
    c_trans = False

    global c_words
    c_words = ["char","for","index","y1","log","rindex","round","exp"]

    global syrup_flag
    syrup_flag = False

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
It returns the local variable bound to argument address.  If it
does not exist, the method creates and store it in the dictionary
local_variables.
-address: memory address. string.
-var: new local variable. string.
'''
def get_local_variable(address):
    global current_local_var
    global local_variables
    
    try:
        idx = local_variables[int(address)]
        #var = "l(" + str(idx) + ")"
        return idx
    except KeyError:
        local_variables[int(address)] = current_local_var
        #var = "l(" + str(current_local_var) + ")"
        current_local_var += 1
        return current_local_var-1

'''
It adds to the list max_field_list the index of the field used.
-value: index_field. int.
'''
def update_field_index(value,block):
#    global max_field_list
    global fields_per_block

    if block not in fields_per_block:
        fields_per_block[block]=[value]
    elif value not in fields_per_block[block]:
        fields_per_block[block].append(value)
        
    # if value not in max_field_list:
    #     max_field_list.append(value)
        
'''
It adds to the list bc_in_use the name of the contract variable used.
-value: contract variable name. string.
'''
def update_bc_in_use(value,block):
    # global bc_in_use
    global bc_per_block


    if block not in bc_per_block:
        bc_per_block[block]=[value]
    elif value not in bc_per_block[block]:
        bc_per_block[block].append(value)
    
    # if value not in bc_in_use:
    #     bc_in_use.append(value)

def update_local_variables(value,block):
    global lvariables_per_block

    if block not in lvariables_per_block:
        lvariables_per_block[block]=[value]
    elif value not in lvariables_per_block[block]:
        lvariables_per_block[block].append(value)
        
def process_tops(top1,top2):
    top1_aux = 0 if top1 == float("inf") else top1
    top2_aux = 0 if top2 == float("inf") else top2

    return top1_aux, top2_aux

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
        instr = v4+" = (" + v1 + "+" + v2 + ") % " + v3
    elif opcode == "MULMOD":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_consume_variable(updated_variables)
        v4, updated_variables = get_new_variable(updated_variables)
        instr = v4+" = (" + v1 + "*" + v2 + ") % " + v3
    elif opcode == "EXP":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_new_variable(updated_variables)
        instr = v3+" = " + v1 + "^" + v2
    elif opcode == "SIGNEXTEND":
        v0_aux, updated_variables = get_consume_variable(index_variables)
        v0, updated_variables = get_consume_variable(updated_variables)
        v1, updated_variables = get_new_variable(updated_variables)
        if syrup_flag:
            instr = v1+" = signextend("+v0_aux+","+v0+")"
        else:
            instr = v1+" = "+v0
    elif opcode == "STOP":
        if syrup_flag:
            instr = "stop(s("+str(index_variables)+"))"
        else:
            instr = "skip"
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
    if opcode == "SHA3":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_new_variable(updated_variables)
        instr = v3+" = sha3("+ v1+", "+v2+")"
    if opcode == "KECCAK256":
        v1, updated_variables = get_consume_variable(index_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_new_variable(updated_variables)
        instr = v3+" = keccak256("+ v1+", "+v2+")"
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
def translateOpcodes30(opcode, value, index_variables,block):
    
    if opcode == "ADDRESS":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = address"
        update_bc_in_use("address",block)
    elif opcode == "BALANCE":
        _, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_new_variable(updated_variables)
        instr = v1+" = balance"
        update_bc_in_use("balance",block)
    elif opcode == "ORIGIN":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = origin"
        update_bc_in_use("origin",block)
    elif opcode == "CALLER":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = caller"
        update_bc_in_use("caller",block)
    elif opcode == "CALLVALUE":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = callvalue"
        update_bc_in_use("callvalue",block)
    elif opcode == "CALLDATALOAD":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_new_variable(updated_variables)
        val = str(value).split("_")
        if val[0] == "Id" or syrup_flag:
            instr = v1+" = calldataload"
            update_bc_in_use("calldataload",block)
        elif str(value).startswith("/*"):
            val = str(value).strip("/*").strip("*/")
            instr = v1+" = "+val
            update_bc_in_use(val,block)
        else:
            if not c_trans:
                instr = v1+" = "+str(value).strip("_")
                update_bc_in_use(str(value).strip("_"),block)
            else:
                if str(value) in c_words:
                    val_end = str(value)+"_sol"
                else:
                    val_end = str(value)
                instr = v1+" = "+val_end
                update_bc_in_use(val_end,block)
    elif opcode == "CALLDATASIZE":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = calldatasize"
        update_bc_in_use("calldatasize",block)
    elif opcode == "CALLDATACOPY":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)
        v2, updated_variables = get_consume_variable(updated_variables)

        if syrup_flag:
            instr = "calldatacopy("+v0+","+v1+","+v2+")"  
        else:
            instr = ""
    elif opcode == "CODESIZE":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = codesize"
        update_bc_in_use("codesize",block)
    elif opcode == "CODECOPY":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)
        v2, updated_variables = get_consume_variable(updated_variables)

        if syrup_flag:
            instr = "calldatacopy("+v0+","+v1+","+v2+")"  
        else:
            instr = ""
        
    elif opcode == "GASPRICE":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = gasprice"
        update_bc_in_use("gasprice",block)
    elif opcode == "EXTCODESIZE":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_new_variable(updated_variables)
        instr = v1+" = extcodesize"
        update_bc_in_use("extcodesize",block)
    elif opcode == "EXTCODECOPY":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_consume_variable(updated_variables)

        if syrup_flag:
            instr = "extcodecopy("+v0+","+v1+","+v2++","+v3+")"  
        else:
            instr = ""
            
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
def translateOpcodes40(opcode, index_variables,block):
    global blockhash_cont
    
    if opcode == "BLOCKHASH":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_new_variable(updated_variables)
        instr = v1+" = blockhash_"+str(blockhash_cont)
        update_bc_in_use("blockhash_"+str(blockhash_cont),block)
        blockhash_cont +=1
    elif opcode == "COINBASE":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = coinbase"
        update_bc_in_use("coinbase",block)
    elif opcode == "TIMESTAMP":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = timestamp"
        update_bc_in_use("timestamp",block)
    elif opcode == "NUMBER":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = number"
        update_bc_in_use("number",block)
    elif opcode == "DIFFICULTY":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = difficulty"
        update_bc_in_use("difficulty",block)
    elif opcode == "GASLIMIT":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = gaslimit"
        update_bc_in_use("gaslimit",block)
    elif opcode == "SELFBALANCE":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = selfbalance"
        update_bc_in_use("selfbalance",block)
    elif opcode == "CHAINID":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = chainid"
        update_bc_in_use("chainid",block)

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
def translateOpcodes50(opcode, value, index_variables,block,state_names):
    global new_fid
    global pc_cont
    # global unknown_mstore
    
    if opcode == "POP":        
        v1, updated_variables = get_consume_variable(index_variables)
        instr=""
    elif opcode == "MLOAD":
        _ , updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_new_variable(updated_variables)
        if syrup_flag:
            instr = v1+" = mload("+v1+")"
        else:
            try:
                l_idx = get_local_variable(value)
                instr = v1+ " = " + "l(l"+str(l_idx)+")"
                update_local_variables(l_idx,block)
            except ValueError:
                instr = ["ll = " + v1, v1 + " = fresh("+str(new_fid)+")"]
                new_fid+=1
             
    elif opcode == "MSTORE":
        v0 , updated_variables = get_consume_variable(index_variables)
        v1 , updated_variables = get_consume_variable(updated_variables)

        if syrup_flag:
            instr = "mstore("+v0+","+v1+")"
        else:
            try:
                l_idx = get_local_variable(value)
                instr = "l(l"+str(l_idx)+") = "+ v1
                update_local_variables(l_idx,block)
            except ValueError:
                instr = ["ls(1) = "+ v1, "ls(2) = "+v0]
                # if vertices[block].is_mstore_unknown():
                #     unknown_mstore = True
            
    elif opcode == "MSTORE8":
        v0 , updated_variables = get_consume_variable(index_variables)
        v1 , updated_variables = get_consume_variable(updated_variables)

        if syrup_flag:
            instr = "mstore8("+v0+","+v1+")"
        else:
            try:
                l_idx = get_local_variable(value)
                instr = "l(l"+str(l_idx)+") = "+ v1
                update_local_variables(l_idx,block)
            except ValueError:
                instr = ["ls(1) = "+ v1, "ls(2) = "+v0]

    elif opcode == "SLOAD":
        _ , updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_new_variable(updated_variables)
        if syrup_flag:
            instr = v1+" = sload("+v1+")"
        else:
            try:
                val = value.split("_")
                if len(val)==1:
                    int(value)
                    idx = value
                else:
                    idx = value
                var_name = state_names.get(idx,idx)
                instr = v1+" = " + "g(" + str(var_name) + ")"
                update_field_index(str(var_name),block)
            except ValueError:
                instr = ["gl = " + v1, v1 + " = fresh("+str(new_fid)+")"]
                new_fid+=1
    elif opcode == "SSTORE":
        v0 , updated_variables = get_consume_variable(index_variables)
        v1 , updated_variables = get_consume_variable(updated_variables)
        if syrup_flag:
            instr = "sstore("+v0+","+v1+")"
        else:

            try:
                val = value.split("_")
                if len(val)==1:
                    int(value)
                    idx = value
                else:
                    idx = value
                var_name = state_names.get(idx,idx)
                instr = "g(" + str(var_name) + ") = " + v1
                update_field_index(str(var_name),block)
            except ValueError:
                instr = ["gs(1) = "+ v0, "gs(2) = "+v1]
    # elif opcode == "JUMP":
    #     pass
    # elif opcode == "JUMPI":
    #     pass
    elif opcode == "PC":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1 + " = pc"+str(pc_cont)
        pc_cont+=1
        update_bc_in_use("pc"+str(pc_cont),block)
    elif opcode == "MSIZE":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1 + " = msize"
        update_bc_in_use("msize",block)
    elif opcode == "GAS":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = "+"gas"
        update_bc_in_use("gas",block)
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

        if syrup_flag:
          instr = "log0("+v0+","+v1+")"  
        else:
            instr = ""
    elif opcode == "LOG1":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)
        v2, updated_variables = get_consume_variable(updated_variables)

        if syrup_flag:
          instr = "log1("+v0+","+v1+","+v2+")"  
        else:
            instr = ""

    elif opcode == "LOG2":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_consume_variable(updated_variables)

        if syrup_flag:
          instr = "log2("+v0+","+v1+","+v2+","+v3+")"  
        else:
            instr = ""

    elif opcode == "LOG3":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_consume_variable(updated_variables)
        v4, updated_variables = get_consume_variable(updated_variables)

        if syrup_flag:
          instr = "log3("+v0+","+v1+","+v2+","+v3+","+v4+")"  
        else:
            instr = ""
        
    elif opcode == "LOG4":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        v3, updated_variables = get_consume_variable(updated_variables)
        v4, updated_variables = get_consume_variable(updated_variables)
        v5, updated_variables = get_consume_variable(updated_variables)

        if syrup_flag:
          instr = "log4("+v0+","+v1+","+v2+","+v3+","+v4+","+v5+")"  
        else:
            instr = ""
        
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
        if syrup_flag:
            instr = v1+" = create("+v00+","+v01+","+v02+")"
        else:
            instr=""


    elif opcode == "CREATE2":
        v00, updated_variables = get_consume_variable(index_variables)
        v01, updated_variables = get_consume_variable(updated_variables)
        v02, updated_variables = get_consume_variable(updated_variables)
        v03, updated_variables = get_consume_variable(updated_variables)
        v1, updated_variables = get_new_variable(updated_variables)

        val = " = create2("+v00+","+v01+","+v02+","+v03+")"

        if syrup_flag:
            instr = v1+" = "+val
        else:
            instr= ""

            
    elif opcode == "CALL": #Suppose that all the calls are executed without errors
        v00, updated_variables = get_consume_variable(index_variables)
        v01, updated_variables = get_consume_variable(updated_variables)
        v02, updated_variables = get_consume_variable(updated_variables)
        v03, updated_variables = get_consume_variable(updated_variables)
        v04, updated_variables = get_consume_variable(updated_variables)
        v05, updated_variables = get_consume_variable(updated_variables)
        v06, updated_variables = get_consume_variable(updated_variables)
        v1, updated_variables = get_new_variable(updated_variables)

        if syrup_flag:
            instr = v1+" = call("+v00+","+v01+","+v02+","+v03+","+v04+","+v05+","+v06+")"  
        else:
            instr = v1 +" = 1"
        
    elif opcode == "CALLCODE":
        v00, updated_variables = get_consume_variable(index_variables)
        v01, updated_variables = get_consume_variable(updated_variables)
        v02, updated_variables = get_consume_variable(updated_variables)
        v03, updated_variables = get_consume_variable(updated_variables)
        v04, updated_variables = get_consume_variable(updated_variables)
        v05, updated_variables = get_consume_variable(updated_variables)
        v06, updated_variables = get_consume_variable(updated_variables)
        v1, updated_variables = get_new_variable(updated_variables)

        if syrup_flag:
            instr = v1+" = callcode("+v00+","+v01+","+v02+","+v03+","+v04+","+v05+","+v06+")"  
        else:
            instr = v1 +" = 1"

        
    elif opcode == "RETURN":
        # var = get_local_variable(addr)
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)
        if syrup_flag:
            instr = "return("+v0+","+v1+")"
        # instr = "r "+var
        else:
            instr = ""
    elif opcode == "REVERT":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)
        if syrup_flag:
            instr = "revert("+v0+","+v1+")"
        else:
            instr = ""
    elif opcode == "ASSERTFAIL":
        if syrup_flag:
            instr = "assertfail(s("+str(index_variables)+"))"
        else:
            instr = ""
        updated_variables = index_variables
    elif opcode == "DELEGATECALL":
        v00, updated_variables = get_consume_variable(index_variables)
        v01, updated_variables = get_consume_variable(updated_variables)
        v02, updated_variables = get_consume_variable(updated_variables)
        v03, updated_variables = get_consume_variable(updated_variables)
        v04, updated_variables = get_consume_variable(updated_variables)
        v05, updated_variables = get_consume_variable(updated_variables)
        v1, updated_variables = get_new_variable(updated_variables)

        if syrup_flag :
            instr = v1+" = delegatecall("+v00+","+v01+","+v02+","+v03+","+v04+","+v05+")"  
        else:
            instr = v1 +" = 1"

    elif opcode == "STATICCALL":
        v00, updated_variables = get_consume_variable(index_variables)
        v01, updated_variables = get_consume_variable(updated_variables)
        v02, updated_variables = get_consume_variable(updated_variables)
        v03, updated_variables = get_consume_variable(updated_variables)
        v04, updated_variables = get_consume_variable(updated_variables)
        v05, updated_variables = get_consume_variable(updated_variables)
        v1, updated_variables = get_new_variable(updated_variables)

        if syrup_flag :
            instr = v1+" = staticcall("+v00+","+v01+","+v02+","+v03+","+v04+","+v05+")"  
        else:
            instr = v1 +" = 1"


            
    # elif opcode == "BREAKPOINT":
    #     pass
    # elif opcode == "RNGSEED":
    #     pass
    # elif opcode == "SSIZEEXT":
    #     pass
    # elif opcode == "SLOADBYTES":
    #     pass
    # elif opcode == "SSTOREBYTES":
    #     pass
    # elif opcode == "SSIZE":
    #     pass
    # elif opcode == "STATEROOT":
    #     pass
    # elif opcode == "TXEXECGAS":
    #     pass
    elif opcode == "CALLSTATIC":
        v00, updated_variables = get_consume_variable(index_variables)
        v01, updated_variables = get_consume_variable(updated_variables)
        v02, updated_variables = get_consume_variable(updated_variables)
        v03, updated_variables = get_consume_variable(updated_variables)
        v04, updated_variables = get_consume_variable(updated_variables)
        v05, updated_variables = get_consume_variable(updated_variables)
        v06, updated_variables = get_consume_variable(updated_variables)
        v1, updated_variables = get_new_variable(updated_variables)

        if syrup_flag:
            instr = v1+" = callstatic("+v00+","+v01+","+v02+","+v03+","+v04+","+v05+","+v06+")"  
        else:
            instr = v1 +" = 1"

    # elif opcode == "INVALID":
    #     pass
    elif opcode == "SUICIDE":
        v0, updated_variables = get_consume_variable(index_variables)
        
        if syrup_flag:
            instr = "suicide("+v0+")"
        else:
            instr = ""
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
    
    if opcode == "PUSH":
        v1,updated_variables = get_new_variable(index_variables)
        try:
            dec_value = int(value)
        except:
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
def translateOpcodesZ(opcode, index_variables,block):
    if opcode == "RETURNDATASIZE":
        v1, updated_variables = get_new_variable(index_variables)
        instr = v1+" = returndatasize"
        update_bc_in_use("returndatasize",block)
    elif opcode == "RETURNDATACOPY":
        v0, updated_variables = get_consume_variable(index_variables)
        v1, updated_variables = get_consume_variable(updated_variables)
        v2, updated_variables = get_consume_variable(updated_variables)
        if syrup_flag:
            instr = "returndatacopy("+v0+","+v1+","+v2+")"
        else:
            instr = ""
    else:
        instr = "Error opcodesZ: "+opcode

    return instr, updated_variables


def translateYulOpcodes(opcode, value, index_variables):

    if opcode == "ASSIGNINMUTABLE":
        v0 , updated_variables = get_consume_variable(index_variables)
        v1 , updated_variables = get_consume_variable(updated_variables)

        instr = "assigninmutable("+v0+","+v1+")"
        
    else:
        v1,updated_variables = get_new_variable(index_variables)
        try:
            dec_value = int(value)
        except:
            dec_value = int(value,16)

        if opcode == "PUSHTAG":
            instr = v1+" = pushtag(" + str(dec_value)+")"

        elif opcode == "PUSH#[$]":
            instr = v1+" = push#[$](" + str(dec_value)+")"

        elif opcode == "PUSH[$]":
            instr = v1+" = push[$](" + str(dec_value)+")"

        
    return instr, updated_variables

'''
It checks if the list instr contains the element to generated a
guard,i.e., just conditional statements, push and ended with a jump
intruction.
-instr is a list with instructions.
-It returns a boolean.
'''
def is_conditional(instr):
    valid = True
    i = 1
    if instr[0] in ["LT","GT","EQ","ISZERO"] and instr[-1] in ["JUMP","JUMPI"]:
        while(i<len(instr)-2 and valid):
            ins = instr[i].split()
            if(ins[0] not in ["ISZERO","PUSH"]):
                valid = False
            i+=1
    else:
        valid = False

    return valid

'''
It returns the opposite guard of the one given as parameter.
-guard is the guard to be "reversed". string.
-opposit = not(guard). string.
'''     
def get_opposite_guard(guard):
    if guard[:2] == "lt":
        opposite = "geq"+guard[2:]
    elif guard[:3] == "leq":
        opposite = "gt"+guard[3:]
    elif guard[:2] == "gt":
        opposite = "leq"+guard[2:]
    elif guard[:3] == "geq":
        opposite = "lt"+guard[3:]
    elif guard == "slt":
        opposite = "geq"+guard[3:]
    elif guard == "sgt":
        opposite = "leq"+guard[3:]
    elif guard[:2] == "eq":
        opposite = "neq"+guard[2:]
    elif guard[:3] == "neq":
        opposite = "eq"+guard[3:]
    # elif guard[:6] == "isZero":
    #     opposite = "notZero"+guard[6:]
    # elif guard[:7] == "notZero":
    #     opposite = "isZero"+guard[7:]
    else:
        opposite = None
    return opposite


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
def compile_instr(rule,evm_opcode,variables,list_jumps,cond,state_vars):
    opcode = evm_opcode.split(" ")
    opcode_name = opcode[0]
    opcode_rest = ""

    if len(opcode) > 1:
        opcode_rest = opcode[1]

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
        value, index_variables = translateOpcodes30(opcode_name,opcode_rest,variables,rule.get_Id())
        rule.add_instr(value)
    elif opcode_name in opcodes40:
        value, index_variables = translateOpcodes40(opcode_name,variables,rule.get_Id())
        rule.add_instr(value)
    elif opcode_name in opcodes50:
        value, index_variables = translateOpcodes50(opcode_name, opcode_rest, variables,rule.get_Id(),state_vars)
        if type(value) is list:
            for ins in value:
                rule.add_instr(ins)
        else:
            rule.add_instr(value)
    elif opcode_name[:4] in opcodes60 and not isYulInstruction(opcode_name):
        value, index_variables = translateOpcodes60(opcode_name[:4], opcode_rest, variables)
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
        value, index_variables = translateOpcodesZ(opcode_name,variables,rule.get_Id())
        rule.add_instr(value)
    elif opcode_name in opcodesYul:
        value, index_variables = translateYulOpcodes(opcode_name,opcode_rest,variables)
        rule.add_instr(value)
    else:
        value = "Error. No opcode matchs"
        index_variables = variables
        rule.add_instr(value)

    rule.add_instr("nop("+opcode_name+")")
    
    return index_variables


def isYulInstruction(opcode):
    if opcode.find("tag") == -1 and opcode.find("#") == -1 and opcode.find("$") == -1 \
            and opcode.find("data") == -1 and opcode.find("DEPLOY") == -1:
        return False
    else:
        return True

'''
It creates the call to next block when the type of the current one is falls_to.
-index_variables refers to the top stack index. int.
-falls_to contains the address of the next block. int.
-instr contains the call instruction generated. string.
'''
def process_falls_to_blocks(index_variables, falls_to):
    top = get_stack_index(falls_to)[0]
    stack_variables = get_stack_variables(index_variables)[:top]
    if(len(stack_variables)!=0):
        p_vars = ",".join(stack_variables)+","
    else:
        p_vars = ""
        
    instr = "call(block"+str(falls_to)+"("+p_vars+"globals, bc))"
    return instr

'''
It translates the jump instruction. 
If the len(jumps)==1, it corresponds to a uncondtional jump.
Otherwise we have to convert it into a conditional jump. 
-block_id refers to the id of the current block. int. 
-variables refers to the top stack index. int.
-jumps is a list with the addresses of the next blocks. 
-It returns a tuple (rule1, rule2, instr) where rule1 and rule2 
 are rule_rbr instances corresponding to the guarded jump rules
 (if it is the case), and instr is the called instruction to the
 jump rule generated. If it is a jump, rule1 = rule2 = None.
'''
def create_uncond_jump(block_id,variables,jumps):
    if (len(jumps)>1):
        rule1, rule2 = create_uncond_jumpBlock(block_id,variables,jumps)
        stack_variables = get_stack_variables(variables)
        head = "jump"+str(block_id)

        in_vars = len(stack_variables)
        rule1.set_index_input(in_vars)
        rule2.set_index_input(in_vars)

    else:
        _ , updated_variables = get_consume_variable(variables)
        
        stack_variables = get_stack_variables(updated_variables)
        top = get_stack_index(jumps[0])[0]
        stack_variables = stack_variables[:top]
        head = "block"+str(jumps[0])
        rule1 = rule2 = None

    if (len(stack_variables)!=0):
        p_vars = ",".join(stack_variables)+","
    else:
        p_vars = ""

        
    instr = "call("+ head +"("+p_vars+"globals, bc))"
    return rule1,rule2,instr

'''
It generates the new two jump blocks (if it is the case).
-block_id is the address of jump blocks. int.
-variables refers to the top stack index when starting the rule. int.
-jumps is a list with the addresses of the next blocks.
- rule1 and rule2 are rbr_rule instances containing the jump rules.
'''
def create_uncond_jumpBlock(block_id,variables,jumps):
    v1, index_variables = get_consume_variable(variables)
    guard = "eq("+ v1 + ","+ str(jumps[0])+")"

    stack_variables = get_stack_variables(index_variables)

    top1 = get_stack_index(jumps[0])[0]
    top2 = get_stack_index(jumps[1])[0]
    
    if (len(stack_variables)!=0):
        p1_vars = ", ".join(stack_variables[:top1])+","
        p2_vars = ", ".join(stack_variables[:top2])+","
    else:
        p1_vars = p2_vars = ""
    
    rule1 = RBRRule(block_id,"jump",False,all_state_vars)
    rule1.set_guard(guard)
    instr = "call(block"+str(jumps[0])+"("+p1_vars+"globals,bc))"
    rule1.add_instr(instr)
    rule1.set_call_to(str(jumps[0]))

    rule2 = RBRRule(block_id,"jump",False,all_state_vars)
    guard = get_opposite_guard(guard)
    rule2.set_guard(guard)
    instr = "call(block"+str(jumps[1])+"("+p2_vars+"globals,bc))"
    rule2.add_instr(instr)
    rule2.set_call_to(str(jumps[1]))
    
    return rule1, rule2

'''
It translates the jumpi instruction.  
-block_id refers to the id of the current block. int.
-l_instr contains the instructions involved in the generation of the jump. 
-variables refers to the top stack index. int.
-jumps is a list with the addresses of the next blocks. [int].
- falls_to is the address of one of the next blocks. int.
-nop is True when generating nop annotations with the opcode. False otherwise.
-guard is true if we have to generate the guard. Otherwise we have to compare
 it he top variable is equal to 1.
-It returns a tuple (rule1, rule2, instr) where rule1 and rule2 
 are rule_rbr instances corresponding to the guarded jump rules,
 and instr is the called instruction to the jump rule generated.
'''
def create_cond_jump(block_id,l_instr,variables,jumps,falls_to,guard = None):

    rule1, rule2 = create_cond_jumpBlock(block_id,l_instr,variables,jumps,falls_to,guard)
    consume = 1 if l_instr[0] == "ISZERO" else 2
    stack_variables = get_stack_variables(variables)

    if (len(stack_variables)!=0):
        p_vars = ",".join(stack_variables)+","
    else:
        p_vars = ""


    in_vars = len(stack_variables)
    rule1.set_index_input(in_vars)
    rule2.set_index_input(in_vars)
    
    instr = "call(jump"+str(block_id)+"("+p_vars+"globals,bc))"
    
    return rule1, rule2, instr

'''
-l_instr contains the instructions involved in the generation of the jump. 
-variables refers to the top stack index. int.
-jumps is a list with the addresses of the next blocks. [int].
- falls_to is the address of one of the next blocks. int.
-nop is True when generating nop annotations with the opcode. False otherwise.
-guard is true if we have to generate the guard. Otherwise we have to compare
 it he top variable is equal to 1.
- rule1 and rule2 are rbr_rule instances containing the jump rules.
'''
def create_cond_jumpBlock(block_id,l_instr,variables,jumps,falls_to,guard):
    if guard:
        guard, index_variables = translateOpcodes10(l_instr[0], variables,False)
    else:
        _ , index_variables = get_consume_variable(variables)
        v1, index_variables = get_consume_variable(index_variables)
        guard = "eq("+v1+", 1 )"
    
    for elem in l_instr[1:]:
        if elem == "ISZERO":
            guard = get_opposite_guard(guard)
        elif elem[:4] == "PUSH":
            _, index_variables = get_new_variable(index_variables)
        elif elem == "JUMPI":
            _, index_variables = get_consume_variable(index_variables)
            _, index_variables = get_consume_variable(index_variables)
        else:
            guard = "Error while creating the jump"
    
    stack_variables = get_stack_variables(index_variables)

    top1 = get_stack_index(jumps[0])[0]
    top2 = get_stack_index(falls_to)[0]
    top1, top2 = process_tops(top1, top2)

    if (len(stack_variables)!=0):
        p1_vars = ", ".join(stack_variables[:top1])+"," if top1 !=0 else ""
        p2_vars = ", ".join(stack_variables[:top2])+"," if top2 != 0 else ""
    else:
        p1_vars = p2_vars = ""


    rule1 = RBRRule(block_id,"jump",False,all_state_vars)
    rule1.set_guard(guard)
    instr = "call(block"+str(jumps[0])+"("+p1_vars+"globals,bc))"
    rule1.add_instr(instr)
    rule1.set_call_to(str(jumps[0]))

    rule2 = RBRRule(block_id,"jump",False,all_state_vars)
    guard = get_opposite_guard(guard)
    rule2.set_guard(guard)
    instr = "call(block"+str(falls_to)+"("+p2_vars+"globals,bc))"
    rule2.add_instr(instr)
    rule2.set_call_to(str(falls_to))
    
    return rule1, rule2

'''
It returns true if the opcode ASSERTFAIL appears in the list of
intructions of the block
'''
def block_has_invalid(block):
    instr = block.get_instructions()
    comes_from_getter = block.get_assertfail_in_getter()
    array_access = block.get_access_array()
    div0_invalid = block.get_div_invalid_pattern()
    
    if "ASSERTFAIL" in instr and (not comes_from_getter):
        if array_access:
            t = "array"
        elif div0_invalid:
            t = "div0"
        else:
            t = "other"
                
        return (True,t)
    else:
        return (False, "no")
    
def block_access_array(block):
    return (block.get_access_array(), "array")

def block_div_invalid(block):
    return (block.get_div_invalid_pattern(), "div0")


'''
It generates the rbr rules corresponding to a block from the CFG.
index_variables points to the corresponding top stack index.
The stack could be reconstructed as [s(ith)...s(0)].
'''
def compile_block(instrs,input_stack,blockId):
    global rbr_blocks
    global top_index
    global new_fid
    
    cont = 0
    top_index = 0
    new_fid = 0
    finish = False
    
    index_variables = input_stack-1
    if blockId !=-1:
        block_id = blockId
    else:
        block_id = 0
    rule = RBRRule(block_id, "block",False,all_state_vars)
    rule.set_index_input(input_stack)
    l_instr = instrs

    
    while not(finish) and cont< len(l_instr):
        index_variables = compile_instr(rule,l_instr[cont],index_variables,[],True,all_state_vars)        
        cont+=1

    rule.set_fresh_index(top_index)

    # #    inv = block_has_invalid(l_instr)
    # inv = block_access_array(block)
    # if inv:
    #     rule.activate_invalid()

    return rule


'''
It creates a file with the rbr rules generated for the programa
analyzed. If it contains more than 1 smart contract it creates a file
for each smart contract.
-rbr is a list containing instances of rbr_rule.
-executions refers to the number of smart contract that has been translated. int.
'''
def write_rbr(rule,block_id,cname = None):
    if costabs_folder not in os.listdir(tmp_path):
        os.mkdir(costabs_path)

    if block_id !=-1:
        name = costabs_path+cname+"block"+str(block_id)+".rbr"
    else:
        name = costabs_path+cname+".rbr"
        
    with open(name,"w") as f:
        f.write(rule.rule2string()+"\n")

    f.close()
        
def component_update_fields_block(block,data):
    fields, bc, local = data #local
    rule = rbr_blocks.get("block"+str(block),-1)
    if rule != -1:
        rule[0].update_global_arg(fields)
        rule[0].update_bc(bc)
        rule[0].update_local_arg(local)

    rule = rbr_blocks.get("jump"+str(block),-1)
    if rule != -1:
        rule[0].update_global_arg(fields)
        rule[1].update_global_arg(fields)
        rule[0].update_bc(bc)
        rule[1].update_bc(bc)
        rule[0].update_local_arg(local)
        rule[1].update_local_arg(local)

    
def component_update_fields(rule,component):
    
    block = rule.get_Id()
    
    fields = fields_per_block.get(block,[])
    bc = bc_per_block.get(block,[])
    local = lvariables_per_block.get(block,[])
    
    if fields != [] or bc !=[] or local !=[]:
        rule.update_global_arg(fields)
        rule.update_bc(bc)
        rule.update_local_arg(local)
        
        # if rule.get_type() == "block":
        #         rule = rbr_blocks.get("jump"+str(block),-1)
        #         if rule != -1:
        #             print "JUMP"
        #             rule[0].update_global_arg(fields)
        #             rule[1].update_global_arg(fields)
        # print "COMPONENT_OF"
        # print component[block]
        for elem_c in component[block]:
            component_update_fields_block(elem_c,(fields,bc,local))#local)


def check_invalid_options(block,invalid_options):
    if invalid_options == "all":
        inv = block_has_invalid(block)
    elif invalid_options == "array":
        inv = block_access_array(block)
    elif invalid_options == "div":
        inv = block_div_invalid(block)
    else:
        inv = (False, "no")

    return inv
            
'''
Main function that build the rbr representation from the CFG of a solidity file.
-blocks_input contains a list with the blocks of the CFG. basicblock.py instances.
-stack_info is a mapping block_id => height of the stack.
-block_unbuild is a list that contains the id of the blocks that have not been considered yet. [string].
-nop_opcodes is True if it has to annotate the evm bytecodes.
-saco_rbr is True if it has to generate the RBR in SACO syntax.
-exe refers to the number of smart contracts analyzed.
'''
def evm2rbr_compiler(contract_name = None, syrup = None,block = None, sto = False, block_id = -1):
    global rbr_blocks
    global syrup_flag
    
    init_globals()
    
    begin = dtimer()

    syrup_flag = syrup
    
    try:
        instructions = block["instructions"]
        input_stack = int(block["input"])
        # print(instructions)
        # print(input_stack)
        
        rule = compile_block(instructions,input_stack,block_id)

            
        write_rbr(rule,block_id,contract_name)
        
        end = dtimer()
        ethir_time = end-begin
        print("Build RBR: "+str(ethir_time)+"s")
               

        if syrup:
            smt_translate_isolate(rule,contract_name,sto)
                
            # if saco_rbr:
            #     saco.rbr2saco(rbr,exe,contract_name)
            # if c_rbr == "int":
            #     c_translation.rbr2c(rbr,exe,contract_name,scc,svc_labels,gotos,fbm)
            # elif c_rbr == "uint":
            #     c_utranslation.rbr2c(rbr,exe,contract_name,scc,svc_labels,gotos,fbm)
            # print("*************************************************************")

            return 0
        
    except Exception as e:
        traceback.print_exc()
        if len(e.args)>1:
            arg = e[1]
            if arg == 5:
                raise Exception("Error in SACO translation",5)
            elif arg == 6:
                raise Exception("Error in C translation",6)
        else:    
            raise Exception("Error in RBR generation",4)
            
def write_info_lines(rbr,source_map,contract_name):
    final_path = costabs_path + "/" + contract_name + "_lines.pl"
    f = open (final_path, "w")

    for rules in rbr:
            for rule in rules:
                if 'block' in rule.get_rule_name(): 
                    cont_rbr = 0
                    offset=0
                    i = 0
                    nBq = rule.get_Id()
                    bq=''
                    if '_' in str(nBq): #Caso con _X
                        while nBq[i] != '_' :
                            bq = bq + nBq[i]
                            i = i+1
                        nBq = bq

                    for inst in rule.get_instructions(): 
                        if not('nop' in inst):
                            continue

                        pc = int(nBq)+offset
                        
                        try:
                            nLineCom = source_map.get_init_pos(pc)
                            nLineFin = source_map.get_end_pos(pc)
                            nLine = source_map.get_location(pc)['begin']['line']
                            nLine = nLine+1
                            # bloque = rule.get_rule_name()[5:]
                            f.write("solidityline(" + str(rule.get_rule_name()) + "," + str(cont_rbr) + "," + str(nLine) + "," + str(nLineCom)  + "," + str(nLineFin) + ").  " + " % " + str(offset) + " " + str(inst) + "	\n")  

                        except:
                           continue

                        if 'nop'in inst:
                            offset = offset + get_inc_offset(inst)
                                
                        cont_rbr = cont_rbr + 1
    f.close()


   
def get_inc_offset(op): 
    if 'PUSH' in op: # nop(PUSH1)
        n=op[8:-1]
        return int(n)+1
    return 1