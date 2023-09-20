import copy
import json
import math
import os
from timeit import default_timer as dtimer
import re

import global_params.constants as constants
import global_params.paths as paths
import sfs_generator.opcodes as opcodes
from sfs_generator.utils import (all_integers, find_sublist, get_num_bytes_int,
                                 is_integer, isYulInstructionUpper, get_ins_size,check_and_print_debug_info)
from typing import Optional
from smt_encoding.json_with_dependencies import extended_json_with_minlength
from typing import Optional, List, Tuple
import networkx as nx

terminate_block = ["ASSERTFAIL","RETURN","REVERT","SUICIDE","STOP"]

pre_defined_functions = ["PUSH","POP","SWAP","DUP"]

zero_ary = ["origin","caller","callvalue","address","number","gasprice","difficulty","prevrandao","basefee","coinbase","timestamp","codesize","gaslimit","gas","calldatasize","returndatasize","msize","selfbalance","chainid","pushdeployaddress","pushsize"]

commutative_bytecodes = ["ADD","MUL","EQ","AND","OR","XOR"]

max_bound = 22

global original_opcodes
original_opcodes = []

global gas_t
gas_t = 0

global compute_gast
compute_gast = True

global int_not0
int_not0 = []

global source_name
source_name = ""

global cname
cname = ""

global saved_push
saved_push = 0

global gas_saved_op
gas_saved_op = 0

global gas_store_op
gas_store_op = 0

global gas_memory_op
gas_memory_op = 0

global blocks_json_dict
blocks_json_dict = {}

global sfs_contracts
sfs_contracts = {}

global split_sto
split_sto = False

global mem40_pattern
mem40_pattern = False

global original_ins
original_ins = []

global max_l
max_l = 0

global size_flag
size_flag = False

global pop_flag
pop_flag = False

global push_flag
push_flag = False

global revert_flag
revert_flag = False

global assignImm_values
assignImm_values = {}

global debug
debug = False

global push_rebuilt
push_rebuilt = dict()


def init_globals():
    
    global u_counter
    u_counter = 0

    global u_dict
    u_dict = {}
    
    global s_counter
    s_counter = 0

    global s_dict
    s_dict = {}

    global variable_content
    variable_content = {}
    
    global user_defins
    user_defins = []

    global user_def_counter
    user_def_counter = {}

    global already_defined_userdef
    already_defined_userdef = []
    
    global max_instr_size
    max_instr_size = 0

    global max_stack_size
    max_stack_size = 0

    global num_pops
    num_pops = 0

    global discount_op
    discount_op = 0

    global already_considered
    already_considered = []

    global sstore_seq
    sstore_seq = []

    global sstore_v_counter
    sstore_v_counter = 0

    global mstore_seq
    mstore_seq = []

    global mstore_v_counter
    mstore_v_counter = 0

    global storage_dep
    storage_dep = []

    global memory_dep
    memory_dep = []

    global memory_opt
    memory_opt = [False,False,False]

    global storage_opt
    storage_opt = [False, False, False]

    global mem_delete_pos
    mem_delete_pos = []

    global sto_delete_pos
    sto_delete_pos = []

    global rule_applied
    rule_applied = False

    global modified_userdef_vals
    modified_userdef_vals = {}

    global rules_applied
    rules_applied = []

    global rule
    rule = ""

    global extra_dep_info
    extra_dep_info = {}

    global useless_info
    useless_info = []

    
    
def process_extra_dependences_info(info,location="memory"):
    global extra_dep_info

    if location == "storage":
        equal_pairs = info.get_equal_pairs_storage()
        nonequal_pairs = info.get_nonequal_pairs_storage()
    elif location == "memory":
        equal_pairs = info.get_equal_pairs_memory()
        nonequal_pairs = info.get_nonequal_pairs_memory()
    else:
        raise Exception("Unknown location")
    
    # extra_dep_info["mstore_useless"] = info.get("mstore_useless",[])
    # extra_dep_info["sstore_useless"] = info.get("sstore_useless",[])
    offset = 0
    if "JUMPDEST" in info.get_instructions():
        offset = 1

    list(map(lambda x: x.order(),equal_pairs))
    list(map(lambda x: x.set_values(x.get_first()-offset,x.get_second()-offset),equal_pairs))

    if location == "memory":
        extra_dep_info["memory_deps_eqs"] = equal_pairs    
    else:
        extra_dep_info["storage_deps_eqs"] = equal_pairs


        
    list(map(lambda x: x.order(), nonequal_pairs))
    list(map(lambda x: x.set_values(x.get_first()-offset,x.get_second()-offset), nonequal_pairs))
    
    if location == "memory":
        extra_dep_info["memory_deps_noneqs"] =  nonequal_pairs
    else:
        extra_dep_info["storage_deps_noneqs"] =  nonequal_pairs

    
        
    # extra_dep_info["storage_deps"] = info.get("storage_deps",[])
    # raise Exception
    check_and_print_debug_info(debug, extra_dep_info)

def process_useless_info(info):
    global useless_info

    offset = 0
    if "JUMPDEST" in info.get_instructions():
        offset = 1

    l = info.get_useless_info()
    useless_info = list(map(lambda x: x-offset,l))
           
    # extra_dep_info["storage_deps"] = info.get("storage_deps",[])
    # raise Exception
    check_and_print_debug_info(debug, useless_info)
    
    
def filter_opcodes(rule):
    instructions = rule.get_instructions()
    rbr_ins_aux = list(filter(lambda x: x.find("nop(")==-1, instructions))
    rbr_ins = list(filter(lambda x: x!="" and x.find("skip")==-1, rbr_ins_aux))
    return rbr_ins

def get_opcodes(rule):
    instructions = rule.get_instructions()
    instrs = list(filter(lambda x: x.startswith("nop("),instructions))
    return instrs

def get_jumpi_opcodes(rule):
    instructions = rule.get_instructions()[::-1]
    is_nop = True
    i = 0
    guard_opcodes = []
    while(i<len(instructions) and is_nop):
        instr = instructions[i]
        if instr.find("nop(")==-1:
            is_nop = False
        else:
            guard_opcodes.append(instr)
        i = i+1
    return guard_opcodes

def get_numguard_variables(instrs):
    jump_instr = instrs.pop(0)

    return len(instrs)

def output_stack_rule(call_instr):
    stack_index = call_instr.find("s(")
    args = call_instr[stack_index:]
    vars_in = args.split(",")

    stack_vars = []
    
    for e in vars_in:
        if e.strip().startswith("s("):
            stack_vars.append(e.strip())

    return stack_vars

def output_stack_block(stack,guard_variables):
    output_rule = len(stack)
    return output_rule - guard_variables


def get_stack_variables(rule):
    index = rule.get_index_invars()
    return index

def generate_target_stack_idx(input_elems,list_opcodes):
    init_val = 0
    
    for op in list_opcodes:
        opcode = op[4:-1].strip()
        if opcode.startswith("PUSH"):
            vals = [0,0,1]
        elif opcode.startswith("ASSIGNIMMUTABLE"):
            vals = [0,2,0]
        else:
            vals = opcodes.get_opcode(opcode)
        init_val = init_val-vals[1]+vals[2]
    
    seq = range(0,input_elems+init_val) # if input_elems !=-1 else range(0,input_elems+init_val+1)
    target_vars = list(map(lambda x: "s("+str(x)+")",seq))
    return target_vars
    
def generate_vars_target_stack(guard_instrs, call,opcodes):
    stack_rule = output_stack_rule(call)
    #num_target_stack = output_stack_block(stack_rule,guard_instrs)
    if call.find("call(block")!=-1 and "nop(JUMP)" in opcodes:
        num_target_stack = len(stack_rule)+1
    else:
        num_target_stack = len(stack_rule)
    seq = range(0,num_target_stack)
    target_vars = list(map(lambda x: "s("+str(x)+")",seq))
    return target_vars

def contained_in_source_stack(v,instructions,source_stack):
    contained = True
    i = 0

    if v not in source_stack:
        return False
    
    if instructions == []:
        contained = True
    else:
        while(i<len(instructions)):
            pos_var = instructions[i].find(v)

            if pos_var!=-1:
                pos_equals = instructions[i].find("=")
                if pos_equals != -1 and  pos_var < pos_equals:
                    return False
            i+=1

    return contained

#Here instructions = instrs+nops
def get_encoding_init_block(instructions,source_stack):
    global s_dict
    global u_dict

    sstore_count = 0
    mstore_count = 0
    mstore8_count = 0
    mstoreImm_count = 0
    
    old_sdict = dict(s_dict)
    old_u_dict = dict(u_dict)
    
    i = 0
    opcodes = []
    push_values = []
    
    while(i<len(instructions)):
        if instructions[i].startswith("nop("):
            instr = instructions[i][4:-1].strip()
            if instr.startswith("DUP") or instr.startswith("SWAP") or instr.startswith("PUSH") or instr.startswith("POP"):
                if instr.startswith("PUSH") and instr.find("DEPLOYADDRESS") == -1 and instr.find("SIZE") ==-1:
                    value = instructions[i-1].split("=")[-1].strip()
                    if value.find("pushtag")!=-1 or value.find("push#[$]")!=-1 or value.find("push[$]")!=-1 or value.find("pushdata")!=-1 or value.find("pushimmutable")!=-1 or value.find("pushlib")!=-1:
                        pos = value.find("(")
                        int_val = value[pos+1:-1]
                        push_values.append(int_val)

                        var = instructions[i-1].split("=")[0].strip()
                        instructions_without_nop = list(filter(lambda x: not x.startswith("nop("), instructions[:i]))
                        instructions_reverse = instructions_without_nop[::-1]
                        search_for_value(var,instructions_reverse, source_stack, False)
                        opcodes.append((s_dict[var],u_dict[s_dict[var]]))
                    else:
                        opcodes.append(instr)
                        push_values.append(value) #normal push
                elif instr.startswith("PUSH") and (instr.find("DEPLOYADDRESS") !=-1 or instr.find("SIZE") !=-1):
                    var = instructions[i-1].split("=")[0].strip()

                    instructions_without_nop = list(filter(lambda x: not x.startswith("nop("), instructions[:i]))
                    instructions_reverse = instructions_without_nop[::-1]
                    search_for_value(var,instructions_reverse, source_stack, False)
                    opcodes.append((s_dict[var],u_dict[s_dict[var]]))
                    
                else: #DUP SWAP POP
                    opcodes.append(instr)
            else:
                #non-interpreted function
                if instructions[i-1].find("=")!=-1:
                    var = instructions[i-1].split("=")[0].strip()

                    instructions_without_nop = list(filter(lambda x: not x.startswith("nop("), instructions[:i]))
                    instructions_reverse = instructions_without_nop[::-1]
                    search_for_value(var,instructions_reverse, source_stack, False)
                    opcodes.append((s_dict[var],u_dict[s_dict[var]]))
                    
                else:
                    exp = generate_sstore_mstore(instructions[i-1],instructions[i-2::-1],source_stack,len(instructions)-(i-1))
                    if exp[0][-1] == "sstore":
                        instr = "SSTORE_"+str(sstore_count)
                        sstore_count+=1
                    elif exp[0][-1] == "mstore":
                        instr = "MSTORE_"+str(mstore_count)
                        mstore_count+=1
                    elif exp[0][-1] == "mstore8":
                        instr = "MSTORE8_"+str(mstore8_count)
                        mstore8_count+=1
                    elif exp[0][-1].startswith("mstoreImmutable"):
                        instr = exp[0][-1].upper()
                        mstore8_count+=1
                        

                    opcodes.append(instr)
        i+=1
        
    new_opcodes = []
    init_user_def = []
    for i in range(len(opcodes)):
        if isinstance(opcodes[i],tuple):
            instruction = opcodes[i]

            u_var = instruction[0]
            args_exp = instruction[1][0]
            arity_exp = instruction[1][1]
            
            user_def = build_initblock_userdef(u_var,args_exp,arity_exp)
            for u in user_def:
                if u not in init_user_def:
                    init_user_def.append(u)

            for e in user_def:
                new_opcodes.append(e["id"])
        else:
            new_opcodes.append(opcodes[i])

    init_info = {}
    init_info["opcodes_seq"] = new_opcodes
    init_info["non_inter"] = init_user_def
    init_info["push_vals"] = list(map(lambda x: int(x),push_values))

    return init_info



def search_for_value(var, instructions,source_stack,evaluate = True):
    global s_counter
    global s_dict
    
    search_for_value_aux(var,instructions,source_stack,0,evaluate)
    
def search_for_value_aux(var, instructions,source_stack,level,evaluate = True):
    global s_counter
    global s_dict
    global u_counter
    global u_dict
    global rule_applied
    global rules_applied
    global rule
    
    i = 0
    found = False
    vars_instr = " "
    
    while(i<len(instructions) and not(found)):

        instr = instructions[i]
        vars_instr = instr.split("=")
        if vars_instr[0].strip().startswith(var):
            found = True
           
        i+=1
    level+=i

    if found:
        value = vars_instr[1].strip()
    else:
        value = var.strip()
        
    new_vars, funct = get_involved_vars(value,vars_instr[0])

    if len(new_vars) == 1:
        
        in_sourcestack = contained_in_source_stack(new_vars[0],instructions[i:],source_stack)
    
        if in_sourcestack or is_integer(new_vars[0])!=-1:
            if is_integer(new_vars[0])!=-1:
                val = int(new_vars[0])
            else:
                val = new_vars[0]

            update_unary_func(funct,var,new_vars[0],evaluate)
            if rule_applied:
                rules_applied.append(rule)
                rule = ""
        else:

            if new_vars[0] not in zero_ary and new_vars[0].find("gas")==-1 and new_vars[0].find("timestamp")==-1:
                search_for_value_aux(new_vars[0],instructions[i:],source_stack,level,evaluate)
                val = s_dict[new_vars[0]]
            else:
                val = new_vars[0]
            update_unary_func(funct,var,val,evaluate)
            if rule_applied:
                rules_applied.append(rule)
                rule = ""
    else:
    
        u_var = create_new_svar()
        s_dict_old = dict(s_dict)

        values = {}

        for v in new_vars:

            search_for_value_aux(v,instructions[i:],source_stack,level,evaluate)
    
            values[v] = s_dict[v]

        exp_join = rebuild_expression(new_vars,funct,values,level,evaluate)
        r = exp_join[0]
        exp = (exp_join[1],exp_join[2])

        if r:
            rules_applied.append(rule)
            rule = ""
            s_dict[var] = exp[0]

        else:

            new_u, defined = is_already_defined(exp)
            if defined:
                u_var = new_u
            else:
                u_dict[u_var] = exp

            s_dict = s_dict_old
        
            s_dict[var] = u_var

            
def generate_sstore_mstore(store_ins,instructions,source_stack,pos,simp):
    level = 0
    new_vars, funct = get_involved_vars(store_ins,"")
    
    values = {}

    pre = already_considered 

    for v in new_vars:
        search_for_value_aux(v,instructions,source_stack,pos,simp)
        
        values[v] = s_dict[v]


    exp_join = rebuild_expression(new_vars,funct,values,level,simp)

    
    return exp_join[1],exp_join[2]


def generate_sload_mload(load_ins,instructions,source_stack,pos,simp):

    level = pos

    if load_ins.find("=")!=-1:
        load_ins = load_ins.split("=")[-1].strip()

    
    new_vars, funct = get_involved_vars(load_ins,"")
    
    in_sourcestack = contained_in_source_stack(new_vars[0],instructions,source_stack)
    
    if in_sourcestack or is_integer(new_vars[0])!=-1:
        if is_integer(new_vars[0])!=-1:
            val = int(new_vars[0])
        else:
            val = new_vars[0]
            #update_unary_func(funct,var,new_vars[0])

        elem = ((new_vars[0],funct),1)
        new_uvar, defined = is_already_defined(elem)
        return new_uvar,elem
            
    else:
        if new_vars[0] not in zero_ary and new_vars[0].find("gas")==-1 and new_vars[0].find("timestamp")==-1:
            search_for_value_aux(new_vars[0],instructions,source_stack,level,simp)
            val = s_dict[new_vars[0]]
        else:
            val = new_vars[0]
        #update_unary_func(funct,var,val)

        elem = ((val,funct),1)
        new_uvar, defined = is_already_defined(elem)
        return new_uvar,elem


def generate_instruction(load_ins,instructions,source_stack,pos,simp):

    level = pos

    if load_ins.find("=")!=-1:
        load_ins = load_ins.split("=")[-1].strip()

    
    new_vars, funct = get_involved_vars(load_ins,"")
    
    values = {}

    pre = already_considered 

    for v in new_vars:
        search_for_value_aux(v,instructions,source_stack,pos,simp)
    
        values[v] = s_dict[v]

    exp_join = rebuild_expression(new_vars,funct,values,level,simp)

    return exp_join[1],exp_join[2]
    

def is_already_defined(elem):
    for u_var in u_dict.keys():
        if elem == u_dict[u_var]:
            return u_var, True

    return -1, False

def is_already_defined_storage(elem,location):

    if location == "storage":
        for var in sstore_vars.keys():
            if elem == sstore_vars[var]:
                return var, True

    elif location == "memory":
        for var in mstore_vars.keys():
            if elem == mstore_vars[var]:
                return var, True

    return -1, False

def update_unary_func(func,var,val,evaluate):
    global s_dict
    global u_dict
    global gas_saved_op    
    global rule_applied
    global rule
    
    if func != "":

        if is_integer(val)!=-1 and (func=="not" or func=="iszero") and evaluate:
            if func == "not":
                val_end = ~(int(val))+2**256

                if size_flag:

                    v0 = int(val)

                    bytes_v0 = get_num_bytes_int(v0)
                    bytes_sol = get_num_bytes_int(val_end)
                                
                    if bytes_sol <= bytes_v0+1:
                        s_dict[var] = val_end
                        gas_saved_op+=3
                        rule_applied = True
                        rule = "NOT(X)"
                    else:
                        u_var = create_new_svar()

                        if val in zero_ary or val.find("gas")!=-1 or val.find("timestamp")!=-1:
                            arity = 0
                        else:
                            arity = 1

                        elem = ((val,func),arity)
                        new_uvar, defined = is_already_defined(elem)
                        if defined:
                            s_dict[var] = new_uvar
                 
                        else:
                            u_dict[u_var] = elem
                            s_dict[var] = u_var
                else:
                    gas_saved_op+=3
                    s_dict[var] = val_end
                    rule = "NOT(X)"
                    rule_applied = True

            elif func == "iszero":
                aux = int(val)
                val_end = 1 if aux == 0 else 0
                gas_saved_op+=3
                rule = "EVAL(ISZERO("+str(val_end)+"))"
                s_dict[var] = val_end
                rule_applied = True

                
        else:
            u_var = create_new_svar()

            if val in zero_ary or val.find("gas")!=-1 or val.find("timestamp")!=-1:
                arity = 0
            else:
                arity = 1

            elem = ((val,func),arity)

            new_uvar, defined = is_already_defined(elem)
            if defined:
                s_dict[var] = new_uvar
                
            else:
                u_dict[u_var] = elem
                s_dict[var] = u_var
                
    else:
        s_dict[var] = val

def get_involved_vars(instr,var):
    var_list = []
    funct = ""
    
    if instr.find("mload")!=-1:
        instr_new = instr.strip("\n")
        pos = instr_new.find("(")
        arg0 = instr_new[pos+1:-1]
        var0 = arg0.strip()
        var_list.append(var0)

        if not split_sto:
            funct = instr_new[:pos]
        else:
            funct = "mload"

    elif instr.find("sload")!=-1:
        instr_new = instr.strip("\n")

        pos = instr_new.find("(")
        arg0 = instr_new[pos+1:-1]
        var0 = arg0.strip()
        var_list.append(var0)

        if not split_sto: 
            funct = instr_new[:pos]
        else:
            funct = "sload"
            
    elif instr.find("sstore(")!=-1:
        instr_new = instr.strip("\n")
        pos = instr_new.find("sstore(")
        arg01 = instr[pos+7:-1]
        var01 = arg01.split(",")
        var0 = var01[0].strip()
        var1 = var01[1].strip()
        var_list.append(var0)
        var_list.append(var1)

        funct = "sstore"

    elif instr.find("mstore(")!=-1:
        instr_new = instr.strip("\n")
        pos = instr_new.find("mstore(")
        arg01 = instr[pos+7:-1]
        var01 = arg01.split(",")
        var0 = var01[0].strip()
        var1 = var01[1].strip()
        var_list.append(var0)
        var_list.append(var1)

        funct = "mstore"

    elif instr.find("mstore8(")!=-1:
        instr_new = instr.strip("\n")
        pos = instr_new.find("mstore8(")
        arg01 = instr[pos+8:-1]
        var01 = arg01.split(",")
        var0 = var01[0].strip()
        var1 = var01[1].strip()
        var_list.append(var0)
        var_list.append(var1)

        funct = "mstore8"
        
    elif instr.find("timestamp")!=-1:
        var_list.append(instr)
        funct =  instr

    elif instr.find("prevrandao")!=-1:
        var_list.append("prevrandao")
        funct =  "prevrandao"

    elif instr.find("msize")!=-1:
        var_list.append("msize")
        funct =  "msize"

    elif instr.find("sha3",0)!=-1:
        instr_new = instr.strip("\n")
        pos = instr_new.find("(")
        arg01 = instr[pos+1:-1]
        var01 = arg01.split(",")
        var0 = var01[0].strip()
        var1 = var01[1].strip()
        var_list.append(var0)
        var_list.append(var1)

        if not split_sto:
            funct = instr_new[:pos]
        else:
            funct = "sha3"
            
    elif instr.find("keccak256",0)!=-1:
        
        instr_new = instr.strip("\n")
        pos = instr_new.find("(")
        arg01 = instr[pos+1:-1]
        var01 = arg01.split(",")
        var0 = var01[0].strip()
        var1 = var01[1].strip()
        var_list.append(var0)
        var_list.append(var1)

        
        if not split_sto: 
            funct = instr_new[:pos]
        else:
            funct = "keccak256"
        
    elif instr.find("signextend(",0)!=-1:
        instr_new = instr.strip("\n")
        pos = instr_new.find("signextend(")
        arg01 = instr[pos+11:-1]
        var01 = arg01.split(",")
        var0 = var01[0].strip()
        var1 = var01[1].strip()
        var_list.append(var0)
        var_list.append(var1)
        funct = "signextend"

    elif instr.find("create(",0)!=-1:
        instr_new = instr.strip("\n")
        pos = instr_new.find("create(")
        arg012 = instr[pos+7:-1]
        var012 = arg012.split(",")
        var0 = var012[0].strip()
        var1 = var012[1].strip()
        var2 = var012[2].strip()
        var_list.append(var0)
        var_list.append(var1)
        var_list.append(var2)
        funct = "create"

    elif instr.find("create2(",0)!=-1:
        instr_new = instr.strip("\n")
        pos = instr_new.find("create2(")
        arg0123 = instr[pos+8:-1]
        var0123 = arg0123.split(",")
        var0 = var0123[0].strip()
        var1 = var0123[1].strip()
        var2 = var0123[2].strip()
        var3 = var0123[3].strip()
        var_list.append(var0)
        var_list.append(var1)
        var_list.append(var2)
        var_list.append(var3)
        funct = "create2"

    elif instr.find("extcodesize",0)!=-1:
        var0 = var.strip()
        var_list.append(var0)
        funct = "extcodesize"

    elif instr.find("extcodehash",0)!=-1:
        var0 = var.strip()
        var_list.append(var0)
        funct = "extcodehash"

    elif instr.find("returndatasize",0)!=-1:
        var_list.append("returndatasize")
        funct = "returndatasize"

    elif instr.find("and(",0)!=-1:
        instr_new = instr.strip("\n")
        pos = instr_new.find("and(")
        arg01 = instr[pos+4:-1]
        var01 = arg01.split(",")
        var0 = var01[0].strip()
        var1 = var01[1].strip()
        var_list.append(var0)
        var_list.append(var1)

        funct = "and"
        
    elif instr.find("not(",0)!=-1:
        instr_new = instr.strip("\n")
        pos = instr_new.find("not(")
        arg0 = instr[pos+4:-1]
        var0 = arg0.strip()
        var_list.append(var0)

        funct = "not"
        
    elif instr.find("xor(",0)!=-1:
        instr_new = instr.strip("\n")
        pos = instr_new.find("xor(")
        arg01 = instr[pos+4:-1]
        var01 = arg01.split(",")
        var0 = var01[0].strip()
        var1 = var01[1].strip()
        var_list.append(var0)
        var_list.append(var1)

        funct = "xor"

    elif instr.find("or(",0)!=-1:
        instr_new = instr.strip("\n")
        pos = instr_new.find("or(")
        arg01 = instr[pos+3:-1]
        var01 = arg01.split(",")
        var0 = var01[0].strip()
        var1 = var01[1].strip()
        var_list.append(var0)
        var_list.append(var1)

        funct = "or"
    
    elif instr.startswith("eq("):
        instr_new = instr.strip("\n")
        pos = instr_new.find("eq(")
        arg01 = instr[pos+3:-1]
        var01 = arg01.split(",")
        var0 = var01[0].strip()
        var1 = var01[1].strip()
        if var1 =="0":
            
            var_list.append(var0)
            funct = "iszero"
        else:
            var_list.append(var0)
            var_list.append(var1)
            funct = "eq"
    
    elif instr.startswith("lt("):
        instr_new = instr.strip("\n")
        pos = instr_new.find("lt(")
        arg01 = instr[pos+3:-1]
        var01 = arg01.split(",")
        var0 = var01[0].strip()
        var1 = var01[1].strip()
        var_list.append(var0)
        var_list.append(var1)

        funct = "lt"

    elif instr.startswith("slt("):
        instr_new = instr.strip("\n")
        pos = instr_new.find("slt(")
        arg01 = instr[pos+4:-1]
        var01 = arg01.split(",")
        var0 = var01[0].strip()
        var1 = var01[1].strip()
        var_list.append(var0)
        var_list.append(var1)

        funct = "slt"
    
    elif instr.startswith("gt("):
        instr_new = instr.strip("\n")
        pos = instr_new.find("gt(")
        arg01 = instr[pos+3:-1]
        var01 = arg01.split(",")
        var0 = var01[0].strip()
        var1 = var01[1].strip()
        var_list.append(var0)
        var_list.append(var1)

        funct = "gt"

    elif instr.startswith("sgt("):
        instr_new = instr.strip("\n")
        pos = instr_new.find("sgt(")
        arg01 = instr[pos+4:-1]
        var01 = arg01.split(",")
        var0 = var01[0].strip()
        var1 = var01[1].strip()
        var_list.append(var0)
        var_list.append(var1)

        funct = "sgt"

    elif instr.startswith("byte("):
        instr_new = instr.strip("\n")
        pos = instr_new.find("byte(")
        arg01 = instr[pos+5:-1]
        var01 = arg01.split(",")
        var0 = var01[0].strip()
        var1 = var01[1].strip()
        var_list.append(var0)
        var_list.append(var1)

        funct = "byte"

    elif instr.find("mulmod(")!=-1:
        
        instr_new = instr.strip("\n")
        pos = instr_new.find("mulmod(")
        args012 = instr_new[pos+7:-1]
        var012 = args012.split(",")

        var0 = var012[0].strip()
        var1 = var012[1].strip()
        var2 = var012[2].strip()
        
        var_list.append(var0)
        var_list.append(var1)
        var_list.append(var2)

        funct = "mulmod"
            
    elif instr.find("*")!=-1: #MUL

        instr_new = instr.strip("\n")
        var01 = instr_new.split("*")
        var0 = var01[0].strip()
        var1 = var01[1].strip()
        var_list.append(var0)
        var_list.append(var1)

        funct = "*"
            
    elif instr.find("addmod(")!=-1:

        instr_new = instr.strip("\n")
        pos = instr_new.find("addmod(")
        args012 = instr_new[pos+7:-1]
        var012 = args012.split(",")

        var0 = var012[0].strip()
        var1 = var012[1].strip()
        var2 = var012[2].strip()
        
        var_list.append(var0)
        var_list.append(var1)
        var_list.append(var2)

        funct = "addmod"
            
    elif instr.find("+")!=-1: #ADD
        instr_new = instr.strip("\n")
        var01 = instr_new.split("+")
        var0 = var01[0].strip()
        var1 = var01[1].strip()
        var_list.append(var0)
        var_list.append(var1)

        funct = "+"

    elif instr.find("-")!=-1:
        instr_new = instr.strip("\n")
        var01 = instr_new.split("-")
        var0 = var01[0].strip()
        var1 = var01[1].strip()
        var_list.append(var0)
        var_list.append(var1)

        funct = "-"

    elif instr.find("/")!=-1:
        instr_new = instr.strip("\n")
        var01 = instr_new.split("/")

        var0 = var01[0].strip()
        var1 = var01[1].strip()
        var_list.append(var0)
        var_list.append(var1)

        funct = "/"

    elif instr.find("^")!=-1:
        instr_new = instr.strip("\n")
        var01 = instr_new.split("^")
        var0 = var01[0].strip()
        var1 = var01[1].strip()
        var_list.append(var0)
        var_list.append(var1)

        funct = "^"

    elif instr.find("%")!=-1:
        instr_new = instr.strip("\n")
        var01 = instr_new.split("%")
        var0 = var01[0].strip()
        var1 = var01[1].strip()
        var_list.append(var0)
        var_list.append(var1)

        funct = "%"


    elif instr.startswith("shr("):
        instr_new = instr.strip("\n")
        pos = instr_new.find("shr(")
        arg01 = instr[pos+4:-1]
        var01 = arg01.split(",")
        var0 = var01[0].strip()
        var1 = var01[1].strip()
        var_list.append(var0)
        var_list.append(var1)

        funct = "shr"

    # pushlib must come before shl to avoid overlapping
    elif instr.startswith("pushlib("):
        instr_new = instr.strip("\n")
        pos = instr_new.find("pushlib(")
        arg0 = instr[pos+8:-1]
        var0 = arg0.strip()
        var_list.append(var0)

        funct = "pushlib"

    elif instr.startswith("shl("):
        instr_new = instr.strip("\n")
        pos = instr_new.find("shl(")
        arg01 = instr[pos+4:-1]
        var01 = arg01.split(",")
        var0 = var01[0].strip()
        var1 = var01[1].strip()
        var_list.append(var0)
        var_list.append(var1)

        funct = "shl"

    elif instr.startswith("sar("):
        instr_new = instr.strip("\n")
        pos = instr_new.find("sar(")
        arg01 = instr[pos+4:-1]
        var01 = arg01.split(",")
        var0 = var01[0].strip()
        var1 = var01[1].strip()
        var_list.append(var0)
        var_list.append(var1)

        funct = "sar"
        
    elif instr.find("pushdeployaddress")!=-1:
        var_list.append("pushdeployaddress")
        funct =  "pushdeployaddress"

    elif instr.find("pushsize")!=-1:
        var_list.append("pushsize")
        funct =  "pushsize"

        
    elif instr.find("address")!=-1:
        var_list.append("address")
        funct =  "address"

    # elif instr.startswith("pc"):
    #     var_list.append("pc")
    #     funct =  "pc"
    
    elif instr.find("blockhash")!=-1:
        
        var0 = var.strip()
        var_list.append(var0)

        funct = "blockhash"

    elif instr.find("calldataload")!=-1:
        
        var0 = var.strip()
        var_list.append(var0)
        funct = "calldataload"

    elif instr.find("selfbalance")!=-1:
        var_list.append("selfbalance")
        funct =  "selfbalance"

        
    elif instr.find("balance")!=-1:
        var0 = var.strip()
        var_list.append(var0)
        funct = "balance"

    elif instr.find("chainid")!=-1:
        var_list.append("chainid")
        funct =  "chainid"

    elif instr.find("origin")!=-1:
        var_list.append("origin")
        funct =  "origin"

    elif instr.find("caller")!=-1:
        var_list.append("caller")
        funct =  "caller"

    elif instr.find("callvalue")!=-1:
        var_list.append("callvalue")
        funct =  "callvalue"

    elif instr.find("codesize")!=-1:
        var_list.append("codesize")
        funct =  "codesize"

    elif instr.find("gaslimit",0)!=-1:
        var_list.append("gaslimit")
        funct = "gaslimit"
            
    elif instr.find("gasprice")!=-1:
        var_list.append("gasprice")
        funct =  "gasprice"

    elif instr.find("gas")!=-1:
        var_list.append(instr)
        funct =  instr
    
    elif instr.find("calldatasize")!=-1:
        var_list.append("calldatasize")
        funct =  "calldatasize"

    elif instr.find("number")!=-1:
        var_list.append("number")
        funct =  "number"

    elif instr.find("difficulty")!=-1:
        var_list.append("difficulty")
        funct =  "difficulty"

    elif instr.find("basefee")!=-1:
        var_list.append("basefee")
        funct =  "basefee"

    elif instr.find("coinbase")!=-1:
        var_list.append("coinbase")
        funct =  "coinbase"

    elif instr.startswith("call_ext("):
        instr_new = instr.strip("\n")
        pos = instr_new.find("call_ext(")
        arg = instr[pos+9:-1]
        vars06 = arg.split(",")
        var0 = vars06[0].strip()
        var1 = vars06[1].strip()
        var2 = vars06[2].strip()
        var3 = vars06[3].strip()
        var4 = vars06[4].strip()
        var5 = vars06[5].strip()
        var6 = vars06[6].strip()
                                
        var_list.append(var0)
        var_list.append(var1)
        var_list.append(var2)
        var_list.append(var3)
        var_list.append(var4)
        var_list.append(var5)
        var_list.append(var6)

        funct = "call"

    elif instr.startswith("callcode("):
        instr_new = instr.strip("\n")
        pos = instr_new.find("callcode(")
        arg = instr[pos+9:-1]
        vars06 = arg.split(",")
        var0 = vars06[0].strip()
        var1 = vars06[1].strip()
        var2 = vars06[2].strip()
        var3 = vars06[3].strip()
        var4 = vars06[4].strip()
        var5 = vars06[5].strip()
        var6 = vars06[6].strip()
                                
        var_list.append(var0)
        var_list.append(var1)
        var_list.append(var2)
        var_list.append(var3)
        var_list.append(var4)
        var_list.append(var5)
        var_list.append(var6)

        funct = "callcode"

    elif instr.startswith("callstatic("):
        instr_new = instr.strip("\n")
        pos = instr_new.find("callstatic(")
        arg = instr[pos+11:-1]
        vars06 = arg.split(",")
        var0 = vars06[0].strip()
        var1 = vars06[1].strip()
        var2 = vars06[2].strip()
        var3 = vars06[3].strip()
        var4 = vars06[4].strip()
        var5 = vars06[5].strip()
        var6 = vars06[6].strip()
                                
        var_list.append(var0)
        var_list.append(var1)
        var_list.append(var2)
        var_list.append(var3)
        var_list.append(var4)
        var_list.append(var5)
        var_list.append(var6)

        funct = "callstatic"

    elif instr.startswith("delegatecall_ext("):
        instr_new = instr.strip("\n")
        pos = instr_new.find("delegatecall_ext(")
        arg = instr[pos+17:-1]
        vars05 = arg.split(",")
        var0 = vars05[0].strip()
        var1 = vars05[1].strip()
        var2 = vars05[2].strip()
        var3 = vars05[3].strip()
        var4 = vars05[4].strip()
        var5 = vars05[5].strip()
                                
        var_list.append(var0)
        var_list.append(var1)
        var_list.append(var2)
        var_list.append(var3)
        var_list.append(var4)
        var_list.append(var5)

        funct = "delegatecall"

    elif instr.startswith("staticcall_ext("):
        instr_new = instr.strip("\n")
        pos = instr_new.find("staticcall_ext(")
        arg = instr[pos+15:-1]
        vars05 = arg.split(",")
        var0 = vars05[0].strip()
        var1 = vars05[1].strip()
        var2 = vars05[2].strip()
        var3 = vars05[3].strip()
        var4 = vars05[4].strip()
        var5 = vars05[5].strip()
                                
        var_list.append(var0)
        var_list.append(var1)
        var_list.append(var2)
        var_list.append(var3)
        var_list.append(var4)
        var_list.append(var5)

        funct = "staticcall"

    elif instr.startswith("pushtag("):
        instr_new = instr.strip("\n")
        pos = instr_new.find("pushtag(")
        arg0 = instr[pos+8:-1]
        var0 = arg0.strip()
        var_list.append(var0)

        funct = "pushtag"

    elif instr.startswith("push#[$]("):
        instr_new = instr.strip("\n")
        pos = instr_new.find("push#[$](")
        arg0 = instr[pos+9:-1]
        var0 = arg0.strip()
        var_list.append(var0)

        funct = "push#[$]"

    elif instr.startswith("push[$]("):
        instr_new = instr.strip("\n")
        pos = instr_new.find("push[$](")
        arg0 = instr[pos+8:-1]
        var0 = arg0.strip()
        var_list.append(var0)

        funct = "push[$]"


    elif instr.startswith("pushdata("):
        instr_new = instr.strip("\n")
        pos = instr_new.find("pushdata(")
        arg0 = instr[pos+9:-1]
        var0 = arg0.strip()
        var_list.append(var0)

        funct = "pushdata"

    elif instr.startswith("pushimmutable("):
        instr_new = instr.strip("\n")
        pos = instr_new.find("pushimmutable(")
        arg0 = instr[pos+14:-1]
        var0 = arg0.strip()
        var_list.append(var0)

        funct = "pushimmutable"


    elif instr.startswith("mstoreImmutable"):
        assign_inmutable_match = re.fullmatch("(mstoreImmutable[0-9]*)\((.+),(.+)\)", instr)
        var0 = assign_inmutable_match.group(2)
        var1 = assign_inmutable_match.group(3)
        var_list.append(var0)
        var_list.append(var1)

        funct = assign_inmutable_match.group(1)

        
    else:
        var_list.append(instr)
        funct = ""
   
    return var_list, funct

def evaluate_expression(funct,val0,val1):
    if funct == "+":
        return val0+val1
    elif funct == "-":
        return val0-val1
    elif funct == "*":
        return val0*val1
    elif funct == "/":
        return math.floor(val0/val1)
    elif funct == "^":
        return val0**val1
    elif funct == "and":
        return val0&val1
    elif funct == "or":
        return val0|val1
    elif funct == "xor":
        return val0^val1
    elif funct == "%":
        return val0%val1
    elif funct == "eq":
        return 1 if val0==val1 else 0
    elif funct == "gt":
        return 1 if val0>val1 else 0
    elif funct == "lt":
        return 1 if val0 < val1 else 0
    elif funct == "shr":
        return math.floor(val1/(2**val0))
    elif funct == "shl":
        return (val1*(2**val0)) % (2**256)
    elif funct == "sar":
        return math.floor(val1/(2**val0))

def evaluate_expression_ter(funct,val0,val1,val2):
    if funct == "+":
        aux = val0+val1
        return aux%val2
    elif funct == "*":
        aux = val0*val1
        return aux%val2

    
def compute_binary(expression,level):
    global discount_op
    global saved_push
    global gas_saved_op
    global already_considered    
    global rule_applied
    global rule
    global push_rebuilt
    
    v0 = expression[0]
    v1 = expression[1]
    funct = expression[2]

    r, vals = all_integers([v0,v1])

    if r and funct in ["+","-","*","/","^","and","or","xor","%","eq","gt","lt","shl","shr","sar"]:

        exp_str = str(funct)+" "+str(vals[0])+" "+str(vals[1])+","+str(level)
        exp_str_comm = str(funct)+" "+str(vals[1])+" "+str(vals[0])+","+str(level)

        val = evaluate_expression(funct,vals[0],vals[1])

        # To rebuild the expression, we either use the operands that have already been used for any
        # of the operands or a direct PUSH otherwise. Note that gasol_optimization works under the assumption
        # that values are int, and hence, we need to do the cast to hex. Also, as we are operating with a stack,
        # operands are retrieved in reverse order

        # The condition filters computations of the form * PUSH 1 MUL or * PUSH 0 ADD
        if vals[0] != val and vals[1] != val:
            push_rebuilt[val] = (vals[1], vals[0], funct_to_opcode(funct))

        if size_flag:
            r, exp = check_size(expression,val)

            if exp == expression:
                return False, expression
        
        if exp_str not in already_considered:

            if funct in ["*","/","%"]:
                gas_saved_op+=5
            else:
                gas_saved_op+=3
                
            saved_push+=2
            
            if (funct in ["+","*","and","or","xor","eq","shl","shr","sar"]) and (exp_str not in already_considered):
                discount_op+=2
                rule = "EVAL "+str(expression)
                msg = "[RULE]: Evaluate expression "+str(expression)
                check_and_print_debug_info(debug, msg)
                rule_applied = True
                
            elif funct not in ["+","*","and","or","xor","eq","shl","shr","sar"]:
                discount_op+=2
                rule = "EVAL "+str(expression)
                msg = "[RULE]: Evaluate expression "+str(expression)
                check_and_print_debug_info(debug, msg)
                rule_applied = True

        already_considered.append(exp_str)
        
        return True, str(val)
        
    else:
        return False, expression

def compute_ternary(expression):
    global discount_op
    global saved_push
    global gas_saved_op
    global rule_applied
    global rule
    
    v0 = expression[0]
    v1 = expression[1]
    v2 = expression[2]
    funct = expression[3]

    r, vals = all_integers([v0,v1,v2])
    if r and funct in ["addmod","mulmod"]:
        val = evaluate_expression_ter(funct,vals[0],vals[1],vals[2])

        # To rebuild the expression, we either use the operands that have already been used for any
        # of the operands or a direct PUSH otherwise. Note that gasol_optimization works under the assumption
        # that values are int, and hence, we need to do the cast to hex. Also, as we are operating with a stack,
        # operands are retrieved in reverse order

        # The condition filters computations of the form * PUSH 1 MUL or * PUSH 0 ADD
        if vals[1] != val and vals[2] != val and vals[0] != val:
            push_rebuilt[val] = (vals[2], vals[1], vals[0], funct_to_opcode(funct))


        rule = "EVAL "+str(expression)

        msg = "[RULE]: Evaluate expression "+str(expression)
        check_and_print_debug_info(debug, msg)

        rule_applied = True
        
        gas_saved_op+=8
        saved_push+=3
        
        discount_op+=3
        return True, str(val)
    else:
        return False, expression

def check_size(exp_without, expression):
    
    if exp_without != expression:
        v0 = int(exp_without[0])
        v1 = int(exp_without[1])
        bytes_v0 = get_num_bytes_int(v0)
        bytes_v1 = get_num_bytes_int(v1)

        bytes_sol = get_num_bytes_int(expression)

        if bytes_sol <= bytes_v0+bytes_v1+2:
            return True,expression
        else:
            return False,exp_without

    else:
        return False,exp_without
    
def rebuild_expression(vars_input,funct,values,level,evaluate = True):

    if len(vars_input) == 2:
        v0 = values[vars_input[0]]
        v1 = values[vars_input[1]]
        expression_without_simp = (v0, v1, funct)
        if evaluate:
            r, expression = compute_binary(expression_without_simp,level)
        else:
            r = False
            expression = expression_without_simp
        arity = 2
    elif len(vars_input) == 3: #len == 3
        v0 = values[vars_input[0]]
        v1 = values[vars_input[1]]
        v2 = values[vars_input[2]]
        expression_without_simp = (v0,v1,v2,funct)
        if evaluate:
            r, expression = compute_ternary(expression_without_simp)
        else:
            r = False
            expression = expression_without_simp
        arity = 3

    else:
        variables = []
        for v in vars_input:
            variables.append(values[v])
        variables.append(funct)
        expression = tuple(variables)
        r = False
        arity = len(vars_input)
    return r, expression, arity

def create_new_uvar():
    global u_counter

    var =  "u"+str(u_counter)
    u_counter+=1

    return var


def create_new_svar():
    global s_counter
    
    var =  "s("+str(s_counter)+")"
    s_counter+=1

    return var

def create_new_sstorevar():
    global sstore_v_counter

    var =  "sto"+str(sstore_v_counter)
    sstore_v_counter+=1

    return var

def create_new_mstorevar():
    global mstore_v_counter

    var =  "mem"+str(mstore_v_counter)
    mstore_v_counter+=1

    return var
  
def simplify_constants(opcodes_seq,user_def):
    for u in user_def:
        inpt = u["inpt_sk"]
        r, elems = all_integers(inpt)
        if r:
            result = evaluate(elems)
            
def generate_encoding(instructions,variables,source_stack,opcodes,simplification=True):
    global s_dict
    global u_dict
    global variable_content
    global memory_order
    global storage_order
    
    instructions_reverse = instructions[::-1]
    u_dict = {}
    variable_content = {}
    for v in variables:
        s_dict = {}
        search_for_value(v,instructions_reverse, source_stack,simplification)
        variable_content[v] = s_dict[v]
        
    if not split_sto:
        generate_storage_info(instructions,source_stack,opcodes,simplification)
    else:
        memory_order = []
        storage_order = []
        
def generate_storage_info(instructions,source_stack,opcodes,simplification=True):
    global sstore_seq
    global mstore_seq
    global storage_order
    global memory_order
    global storage_dep
    global memory_dep
    global extra_dep_info
    
    sload_relative_pos = {}
    mload_relative_pos = {}

    for x in range(0,len(instructions)):
        s_dict = {}

        if instructions[x].find("sstore")!=-1:
            ins_list = [] if x == 0 else instructions[x-1::-1]
            exp = generate_sstore_mstore(instructions[x],ins_list,source_stack,len(instructions)-x, simplification)
            sstore_seq.append(exp)

        elif instructions[x].find("keccak")!=-1 or instructions[x].find("sha3")!=-1:
            ins_list = [] if x == 0 else instructions[x-1::-1]
            exp = generate_instruction(instructions[x],ins_list,source_stack,len(instructions)-x,simplification)
            sstore_seq.append(exp)
            mstore_seq.append(exp)
        elif instructions[x].find("mstore")!=-1:
            ins_list = [] if x == 0 else instructions[x-1::-1]
            exp = generate_sstore_mstore(instructions[x],ins_list,source_stack,len(instructions)-x,simplification)
            mstore_seq.append(exp)

    last_sload = ""
    sstores = list(sstore_seq)
    last_mload = ""
    mstores = list(mstore_seq)
    
    storage_order = []
    memory_order = []

    extra_dep_info_ins2int = {}
    extra_dep_info_ins2int_sto = {}

    opcodes_idx = 0
    next_val = 0
    
    for x in range(0,len(instructions)):
            
        if instructions[x].find("sload")!=-1:
            ins_list = [] if x == 0 else instructions[x-1::-1]
            exp,r = generate_sload_mload(instructions[x],ins_list,source_stack,len(instructions)-x,simplification)
            last_sload = exp
            storage_order.append(r)
            extra_dep_info_ins2int_sto[opcodes_idx] = (r,len(storage_order)-1)
            
        elif instructions[x].find("sstore")!=-1: #and last_sload != "" and sload_relative_pos.get(last_sload,[])==[]:
            sload_relative_pos[last_sload]=sstores.pop(0)
            storage_order.append(sload_relative_pos[last_sload])
            extra_dep_info_ins2int_sto[opcodes_idx] = (sload_relative_pos[last_sload],len(storage_order)-1)
            
        elif instructions[x].find("mload")!=-1:
            ins_list = [] if x == 0 else instructions[x-1::-1]
            exp,r = generate_sload_mload(instructions[x],ins_list,source_stack,len(instructions)-x,simplification)
            last_mload = exp
            memory_order.append(r)
            extra_dep_info_ins2int[opcodes_idx] = (r,len(memory_order)-1)
            
        elif instructions[x].find("mstore")!=-1: #and last_mload != "" and mload_relative_pos.get(last_mload,[])==[]:
            # print(instructions[x])
            # print("*/*/*/*/*/*/*/*/*/")
            mload_relative_pos[last_mload]=mstores.pop(0)
            memory_order.append(mload_relative_pos[last_mload])
            extra_dep_info_ins2int[opcodes_idx] = (mload_relative_pos[last_mload],len(memory_order)-1)
            
        elif instructions[x].find("keccak")!=-1 or instructions[x].find("sha3")!=-1:
            keccak = mstores.pop(0)
            keccak1 = sstores.pop(0)
            memory_order.append(keccak)
            storage_order.append(keccak)

        if x >= next_val:    
            if  opcodes[opcodes_idx].find("SWAP")!=-1:
                next_val = x+3
                opcodes_idx+=1
            else:
                opcodes_idx+=1


                
    # print(instructions)
    # print(memory_order)
    if extra_dep_info != {}:
        extra_dep_info["mem_deps_int2ins"] = extra_dep_info_ins2int
        extra_dep_info["sto_deps_int2ins"] = extra_dep_info_ins2int_sto

    if useless_info != []: #It deletes from memory_order de useless mstores
        new_memory_order = []
        for i in range(len(memory_order)):

            for x in extra_dep_info_ins2int:
                if i in extra_dep_info_ins2int[x]:
                    if x not in useless_info:
                        new_memory_order.append(memory_order[i])
                    else:
                        extra_dep_info
        memory_order = new_memory_order
        
    remove_loads_instructions()
    
    if simplification:
        simp = True
        while(simp):
            simp = simplify_memory(storage_order, memory_order, "storage")

    # print(memory_order)
            
    storage_order = list(filter(lambda x: type(x) == tuple, storage_order))
    unify_loads_instructions(storage_order, "storage")


    msg = "Storage order: "+str(storage_order)
    check_and_print_debug_info(debug, msg)

    stdep = generate_dependences(storage_order,"storage")

    msg = "Storage dep: "+str(stdep)
    check_and_print_debug_info(debug, msg)

    stdep = simplify_dependencies(stdep)

    msg = "Storage dep simplified: "+str(stdep)
    check_and_print_debug_info(debug, msg)
    
    if simplification:
        simp = True
        while(simp):
            simp = simplify_memory(memory_order, storage_order, "memory")
            
    memory_order = list(filter(lambda x: type(x) == tuple, memory_order))    

    unify_loads_instructions(memory_order, "memory")
    
    unify_keccak_instructions(memory_order,storage_order)

    msg = "Memory order: "+str(memory_order)
    check_and_print_debug_info(debug, msg)
    
    memdep = generate_dependences(memory_order,"memory")
    
    msg = "Memory dep: "+str(memdep)
    check_and_print_debug_info(debug, msg)

    memdep = simplify_dependencies(memdep)

    msg = "Memory dep simplified: "+str(memdep)
    check_and_print_debug_info(debug, msg)
    
    s1= compute_clousure(stdep)
    m1 = compute_clousure(memdep)
    
    get_best_storage(s1, len(storage_order))
    
    storage_dep = stdep
    memory_dep = memdep

    
        
def generate_source_stack_variables(idx):
    ss_list = []
    
    for e in range(idx-1,-1,-1):
        ss_list.append("s("+str(e)+")")
    
    return ss_list
    
def get_s_counter(source_stack,target_stack):
    global s_counter

    max_ss = int(source_stack[0].strip()[2:-1]) if source_stack !=[] else -1
    max_ts = int(target_stack[0].strip()[2:-1]) if target_stack != [] else -1

    s_counter = max(max_ss,max_ts)
    s_counter+=1
    return s_counter


def compute_reverse_svar(var, max_idx):
    
    if str(var).startswith("s("):
        integer = int(var.strip()[2:-1])
    else:
        return var
    
    if integer<=max_idx:
        new_int = max_idx-integer
        new_var = "s("+str(new_int)+")"
    else:
        new_var = var
        
    return new_var

def compute_vars_set(sstack,tstack):
    vars_list = []

    vars_list = list(sstack)

    for user_ins in user_defins:
        output_vars = user_ins["outpt_sk"]
        input_vars = user_ins["inpt_sk"]
        potential_vars = output_vars+input_vars+tstack
        for v in potential_vars:
            if str(v).startswith("s(") and v not in vars_list:
                vars_list.append(v)
    vars_list.sort()
    return vars_list

#When we are simplifying user_def_init = []
def recompute_vars_set(sstack,tstack,userdef,user_def_init):
    vars_list = []

    vars_list = list(sstack)

    
    user_def_instr = userdef+user_def_init
    
    for user_ins in user_def_instr:
        output_vars = user_ins["outpt_sk"]
        input_vars = user_ins["inpt_sk"]
        potential_vars = output_vars+input_vars+tstack
        for v in potential_vars:
            if str(v).startswith("s(") and v not in vars_list:
                vars_list.append(v)
    vars_list.sort()
    return vars_list

def compute_target_stack(tstack):
    new_vals = []
    for v in tstack:
        new_vals.append(variable_content[v])

    return new_vals

def check_all_pops(sstack, tsstack, user_def):
    if len(sstack) > 0 and tsstack == [] and user_def == []:
        return len(sstack)
    else:
        return -1

def compute_max_idx(max_ss,ss):
    if ss == []:
        return max_ss
    
    top_s = ss[0]
    idx_top = int(top_s[2:-1])

    return idx_top




def generate_sstore_info(sstore_elem):
    global user_def_counter
    global sstore_v_counter

    obj = {}
    idx  = user_def_counter.get("SSTORE",0)

    instr_name = "SSTORE"
    name = "SSTORE"+"_"+str(idx)

    args_aux = []
    for e in sstore_elem[0][0:-1]:
        val = is_integer(e)
        if val != -1:
            args_aux.append(val)
        else:
            args_aux.append(e)

    
    obj["id"] = name
    obj["opcode"] = process_opcode(str(opcodes.get_opcode(instr_name)[0]))
    obj["disasm"] = instr_name
    obj["inpt_sk"] = args_aux
    obj["sto_var"] = ["sto"+str(idx)]
    obj["push"] = False
    obj["outpt_sk"] = []
    
    obj["gas"] = opcodes.get_ins_cost(instr_name)
    obj["commutative"] = False
    obj["storage"] = True
    obj["size"] = get_ins_size(instr_name)
    user_def_counter["SSTORE"]=idx+1

    return obj

def generate_mstore_info(mstore_elem):
    global user_def_counter
    global mstore_v_counter

    obj = {}


    if mstore_elem[0][-1].find("mstore8")!=-1:
        idx  = user_def_counter.get("MSTORE8",0)
        instr_name = "MSTORE8"

    elif mstore_elem[0][-1].find("mstoreImmutable")!=-1:
        idx  = user_def_counter.get("ASSIGNIMMUTABLE",0)
        instr_name = "ASSIGNIMMUTABLE"
        
    else:
        idx  = user_def_counter.get("MSTORE",0)
        instr_name = "MSTORE"
            
    name = instr_name+"_"+str(idx)

    args_aux = []
    for e in mstore_elem[0][0:-1]:
        val = is_integer(e)
        if val != -1:
            args_aux.append(val)
        else:
            args_aux.append(e)

    
    obj["id"] = name
    obj["opcode"] = process_opcode(str(opcodes.get_opcode(instr_name)[0]))
    obj["disasm"] = instr_name
    obj["inpt_sk"] = args_aux
    obj["mem_var"] = ["mem"+str(idx)]
    obj["push"] = False
    obj["outpt_sk"] = []
    
    obj["gas"] = opcodes.get_ins_cost(instr_name)
    obj["size"] = get_ins_size(instr_name)
    obj["commutative"] = False
    obj["storage"] = True
    
    if instr_name == "ASSIGNIMMUTABLE":
        obj["value"] = assignImm_values[int(mstore_elem[0][-1].lstrip("mstoreImmutable"))]
        
    user_def_counter[instr_name]=idx+1

    return obj


def modified_variables_userdefins(storage_ins):
    global modified_userdef_vals
    
    for s in modified_userdef_vals.keys():
        ins_lis = filter(lambda x: str(x[0][0]).find(s)!=-1,storage_ins)
        for x in ins_lis:
            pos = storage_ins.index(x)
            ins = storage_ins[pos]
            new_ins =((modified_userdef_vals[s],ins[0][1],ins[0][-1]),ins[1])
            storage_ins[pos] = new_ins

        ins_lis = filter(lambda x: str(x[0][1]).find(s)!=-1,storage_ins)
        for x in ins_lis:
            pos = storage_ins.index(x)
            ins = storage_ins[pos]
            new_ins =((ins[0][0],modified_userdef_vals[s],ins[0][-1]),ins[1])
            storage_ins[pos] = new_ins
    


def generate_json(block_name,ss,ts,max_ss_idx1,gas,opcodes_seq,subblock = None,simplification = True):
    global max_instr_size
    global num_pops
    global blocks_json_dict
    global rule_applied
    global rules_applied
    split_by = False
    
    max_ss_idx = compute_max_idx(max_ss_idx1,ss)
    
    json_dict = {}

    new_ss = []
    new_ts = []
    
    ts_aux = compute_target_stack(ts)
    
    for v in ss:
        new_v = compute_reverse_svar(v,max_ss_idx)
        new_ss.append(new_v)

    for v in ts_aux:
        new_v = compute_reverse_svar(v,max_ss_idx)
        v =  is_integer(new_v)
        if v !=-1:
            new_ts.append(v)
        else:
            new_ts.append(new_v)
            
    sto_objs = []

    sstore_ins = list(filter(lambda x: x[0][-1].find("sstore")!=-1,storage_order))

    modified_variables_userdefins(sstore_ins)

    for sto in sstore_ins:
        x = generate_sstore_info(sto)
        sto_objs.append(x)

    mem_objs = []
    mstore_ins = list(filter(lambda x: x[0][-1].find("mstore")!=-1,memory_order))

    modified_variables_userdefins(mstore_ins)

    for mem in mstore_ins:
        x = generate_mstore_info(mem)
        mem_objs.append(x)

    all_user_defins = user_defins+sto_objs+mem_objs
        
            
    for user_ins in all_user_defins:
        new_inpt_sk = []

        for v in user_ins["inpt_sk"]:
            new_v = compute_reverse_svar(v,max_ss_idx)
            new_inpt_sk.append(new_v)

        user_ins["inpt_sk"] = new_inpt_sk

    remove_vars=[]

    vars_list = compute_vars_set(new_ss,new_ts)

    #Adding sstore seq
    
    if simplification:
        new_user_defins,new_ts = apply_all_simp_rules(all_user_defins,vars_list,new_ts)
        apply_all_comparison(new_user_defins,new_ts)
    else:
        new_user_defins = all_user_defins

    
    new_user_defins1 = update_user_defins(new_ts,new_user_defins)

    removed_instructions = list(filter(lambda x: x not in new_user_defins1,new_user_defins))
    
    update_storage_sequences(removed_instructions)
    
    new_user_defins, new_ts = unify_all_user_defins(new_ts,new_user_defins1,vars_list)
    
    new_user_defins = update_user_defins(new_ts,new_user_defins)
    
    # if simplification:
    vars_list = recompute_vars_set(new_ss,new_ts,new_user_defins,[])
    # else:
    #     vars_list = recompute_vars_set(new_ss,new_ts,new_user_defins,opcodes_seq["non_inter"])
    
    total_inpt_vars = []
    
    for user_ins in new_user_defins:
        for v in user_ins["inpt_sk"]:
            if str(v).startswith("s(") and v not in total_inpt_vars:
                total_inpt_vars.append(v)

    optimized_json(total_inpt_vars,new_ss,new_ts,remove_vars)
    
    max_sk_sz_idx = max(len(vars_list),max_stack_size)
        
    for s in remove_vars:
        if s in vars_list:
            idx = vars_list.index(s)
            vars_list.pop(idx)

    not_used = get_not_used_stack_variables(new_ss,new_ts,total_inpt_vars)

    if pop_flag :
        pop_instructions = generate_pops(not_used)
    else:
        pop_instructions = []
        
    num = check_all_pops(new_ss, new_ts, new_user_defins)

    if num !=-1:
        max_instr_size = num
        num_pops = num
        
    if not split_sto:
        sto_dep, mem_dep = translate_dependences_sfs(new_user_defins)

    else:
        sto_dep, mem_dep = [],[]

    bound_comp = compute_vars(new_ts, new_ss, new_user_defins)
    stack_bound = min(max_sk_sz_idx-len(remove_vars),bound_comp)

    if push_flag:
        new_var_list, new_push_ins = transform_push_uninterpreted_functions(new_ts,new_user_defins)
        
    else:
        new_var_list = []
        new_push_ins = []
        
    json_dict["init_progr_len"] = max_instr_size-discount_op
    json_dict["max_progr_len"] = max_instr_size
    json_dict["max_sk_sz"] = stack_bound #max_sk_sz_idx-len(remove_vars)
    json_dict["vars"] = vars_list+new_var_list
    json_dict["src_ws"] = new_ss
    json_dict["tgt_ws"] = new_ts
    json_dict["user_instrs"] = new_user_defins+pop_instructions+new_push_ins
    json_dict["current_cost"] = gas
    json_dict["storage_dependences"] = [list(dep) for dep in sto_dep]
    json_dict["memory_dependences"]= [list(dep) for dep in mem_dep]
    json_dict["is_revert"]= True if revert_flag else False
    json_dict["rules_applied"] = rule_applied
    json_dict["rules"] = list(filter(lambda x: x != "", rules_applied))
    
    json_dict["original_instrs"] = " ".join(original_ins)
    json_dict = extended_json_with_minlength(json_dict)


    # if not simplification:
    #     op = opcodes_seq["non_inter"]
    #     opcodes_seq["non_inter"] = op+sto_objs+mem_objs
    #     json_dict["init_info"] = opcodes_seq

        
    if subblock is not None:
        block_nm = block_name + "_" + str(subblock)
    else:
        block_nm = block_name + "_0"

        
    if rule_applied:
        msg = "SFS with rule: "+block_nm + "_input.json"
        check_and_print_debug_info(debug, msg)

    if ((max_sk_sz_idx-len(remove_vars)) > bound_comp):
        msg = "MEJORADO: "+paths.json_path+"/"+ block_nm + "_input.json --- "+str((max_sk_sz_idx, bound_comp))
        check_and_print_debug_info(debug, msg)
        # print("MEJORADO: "+paths.json_path+"/"+ block_nm + "_input.json --- "+str((max_sk_sz_idx, bound_comp)))
        
    blocks_json_dict[block_nm] = json_dict

    if "jsons" not in os.listdir(paths.gasol_path):
        os.mkdir(paths.json_path)

    with open(paths.json_path+"/"+ block_nm + "_input.json","w") as json_file:
        json.dump(json_dict,json_file)

    # print(paths.json_path+"/"+ block_nm + "_input.json")
    rule_applied = False
    
    return split_by,""

def get_not_used_stack_variables(new_ss,new_ts,total_inpt_vars):
    not_used = []

    for s in new_ss:
        if (s not in new_ts) and (s not in total_inpt_vars):
            not_used.append(s)

    return not_used
        
def optimized_json(inpt_vars,ss,ts,remove_vars):
    end = False
    i = len(ss)
    
    if ss == [] or ts == []:
        return

    
    while(i>0 and not end):
        same_pos = ss[-1] == ts[-1]
        involved = ts[-1] in inpt_vars
        dups = ts[-1] in ts[:-1]

        if same_pos and not involved and not dups:
            remove_vars.append(ts[-1])
            ss.pop()
            ts.pop()
            if ts == [] or ss == []:
                return
        else:
            end = True
        i-=1

def build_initblock_userdef(u_var,args_exp,arity_exp):
    if arity_exp ==0 or arity_exp == 1:
        funct = args_exp[1]
        args = args_exp[0]

        is_new, obj = generate_userdefname(u_var,funct,[args],arity_exp,True)
                
        return [obj]
            
    elif arity_exp == 2:
        funct = args_exp[2]
        args = [args_exp[0],args_exp[1]]
        is_new, obj = generate_userdefname(u_var,funct,args,arity_exp,True)
        return [obj]
    
    elif arity_exp == 3:
        funct = args_exp[3]

        if funct == "+" or funct == "*":
            
            new_uvar = create_new_svar()
            args01 = [args_exp[0],args_exp[1]]
            is_new, obj = generate_userdefname(new_uvar,funct,args01,arity_exp,True)
            
            funct = "%"
            if not is_new:
                u_var_aux = obj["outpt_sk"][0]
            else:
                u_var_aux = new_uvar
                
            args = [u_var_aux,args_exp[2]]

            is_new, obj1 = generate_userdefname(u_var,funct,args,arity_exp,True)
            
            return [obj, obj1]
        else:

            args = [args_exp[0],args_exp[1],args_exp[2]]
            is_new, obj = generate_userdefname(u_var,funct,args,arity_exp,True)
            
            return [obj]
    else:
        funct = args_exp[-1]
        args = []
        for v in args_exp[:-1]:
            args.append(v)
            
        is_new, obj = generate_userdefname(u_var,funct,args,arity_exp,True)

        return [obj]

        
def build_userdef_instructions():
    global user_defins
    global already_defined_userdef
    global modified_userdef_vals

    
    already_defined_userdef = []
    
    u_dict_sort = sorted(u_dict.keys())
    
    for u_var in u_dict_sort:
        exp = u_dict[u_var]
        arity_exp = exp[1]
        args_exp = exp[0]

        if arity_exp ==0 or arity_exp == 1:
            funct = args_exp[1]
            args = args_exp[0]

            is_new, obj = generate_userdefname(u_var,funct,[args],arity_exp)

            
            if not is_new and funct.find("timestamp")==-1 and funct.find("returndatasize")==-1 and funct.find("gas")==-1:
                if not split_sto and funct.find("sload")==-1 and funct.find("mload")==-1:
                    user_defins.append(obj)
                else:
                    modified_svariable(u_var, obj["outpt_sk"][0])
                    modified_userdef_vals[u_var] = obj["outpt_sk"][0]
            else:
                user_defins.append(obj)
            
        elif arity_exp == 2:
            funct = args_exp[2]
            args = [args_exp[0],args_exp[1]]
            is_new, obj = generate_userdefname(u_var,funct,args,arity_exp)

            
            if not is_new:
                modified_svariable(u_var, obj["outpt_sk"][0])
                modified_userdef_vals[u_var] = obj["outpt_sk"][0]
            else:
                user_defins.append(obj)

        elif arity_exp == 3:
            funct = args_exp[3]

            if funct == "+" or funct == "*":
            
                new_uvar = create_new_svar()
                args01 = [args_exp[0],args_exp[1]]
                is_new, obj = generate_userdefname(new_uvar,funct,args01,arity_exp)

                if not is_new:
                    modified_svariable(new_uvar, obj["outpt_sk"][0])
                    modified_userdef_vals[new_uvar] = obj["outpt_sk"][0]
                    
                else:
                    user_defins.append(obj)

                funct = "%"
                if not is_new:
                    u_var_aux = obj["outpt_sk"][0]
                else:
                    u_var_aux = new_uvar
                
                args = [u_var_aux,args_exp[2]]

                is_new, obj = generate_userdefname(u_var,funct,args,arity_exp)

                if not is_new:
                    modified_svariable(new_uvar, obj["outpt_sk"][0])
                    modified_userdef_vals[new_uvar] = obj["outpt_sk"][0]
                else:
                    user_defins.append(obj)

            else:

                args = [args_exp[0],args_exp[1],args_exp[2]]
                is_new, obj = generate_userdefname(u_var,funct,args,arity_exp)

                if not is_new:
                    modified_svariable(u_var, obj["outpt_sk"][0])
                    modified_userdef_vals[u_var] = obj["outpt_sk"][0]
                else:
                    user_defins.append(obj)
        else:
            funct = args_exp[-1]
            args = []
            for v in args_exp[:-1]:
                args.append(v)

            is_new, obj = generate_userdefname(u_var,funct,args,arity_exp)

            if not is_new:
                modified_svariable(u_var, obj["outpt_sk"][0])
                modified_userdef_vals[u_var] = obj["outpt_sk"][0]
            else:
                user_defins.append(obj)


def funct_to_opcode(funct: str) -> Optional[str]:
    instr_name = None

    if funct.find("+") != -1:
        instr_name = "ADD"

    elif funct.find("mulmod") != -1:
        instr_name = "MULMOD"

    elif funct.find("addmod") != -1:
        instr_name = "ADDMOD"

    elif funct.find("-") != -1:
        instr_name = "SUB"

    elif funct.find("*") != -1:
        instr_name = "MUL"

    elif funct.find("/") != -1:
        instr_name = "DIV"

    elif funct.find("^") != -1:
        instr_name = "EXP"

    elif funct.find("%") != -1:
        instr_name = "MOD"

    elif funct.find("prevrandao") != -1:
        instr_name = "PREVRANDAO"
        
    elif funct.find("and") != -1:
        instr_name = "AND"

    elif funct.find("origin") != -1:
        instr_name = "ORIGIN"

    elif funct.find("pushdeployaddress") != -1:
        instr_name = "PUSHDEPLOYADDRESS"

    elif funct.find("pushsize") != -1:
        instr_name = "PUSHSIZE"

    elif funct.find("xor") != -1:
        instr_name = "XOR"

    elif funct.find("or") != -1:
        instr_name = "OR"

    elif funct.find("not") != -1:
        instr_name = "NOT"

    elif funct.find("sgt") != -1:
        instr_name = "SGT"

    elif funct.find("gt") != -1:
        instr_name = "GT"

    elif funct.find("shr") != -1:
        instr_name = "SHR"

    # pushlib must come before shl to avoid overlapping
    elif funct.find("pushlib") != -1:
        instr_name = "PUSHLIB"

    elif funct.find("shl") != -1:
        instr_name = "SHL"

    elif funct.find("sar") != -1:
        instr_name = "SAR"

    elif funct.find("slt") != -1:
        instr_name = "SLT"
        
    elif funct.startswith("lt"):
        instr_name = "LT"

    elif funct.find("selfbalance") != -1:
        instr_name = "SELFBALANCE"

    elif funct.find("extcodehash") != -1:
        instr_name = "EXTCODEHASH"

    elif funct.find("chainid") != -1:
        instr_name = "CHAINID"

    elif funct.find("create2") != -1:
        instr_name = "CREATE2"

    elif funct.find("byte") != -1:
        instr_name = "BYTE"

    elif funct.find("eq") != -1:
        instr_name = "EQ"

    elif funct.find("iszero") != -1:
        instr_name = "ISZERO"

    elif funct.find("caller") != -1:
        instr_name = "CALLER"

    elif funct.find("callvalue") != -1:
        instr_name = "CALLVALUE"

    elif funct.find("calldataload") != -1:
        instr_name = "CALLDATALOAD"

    elif funct.find("address") != -1:
        instr_name = "ADDRESS"

    elif funct.find("calldatasize") != -1:
        instr_name = "CALLDATASIZE"

    elif funct.find("number") != -1:
        instr_name = "NUMBER"

    elif funct.find("gasprice") != -1:
        instr_name = "GASPRICE"

    elif funct.find("difficulty") != -1:
        instr_name = "DIFFICULTY"

    elif funct.find("basefee") != -1:
        instr_name = "BASEFEE"

    elif funct.find("blockhash") != -1:
        instr_name = "BLOCKHASH"

    elif funct.find("balance") != -1:
        instr_name = "BALANCE"

    elif funct.find("coinbase") != -1:
        instr_name = "COINBASE"

    elif funct.find("mload") != -1:
        instr_name = "MLOAD"

    elif funct.find("sload") != -1:
        instr_name = "SLOAD"

    elif funct.find("timestamp") != -1:
        instr_name = funct.upper()

    elif funct.find("msize") != -1:
        instr_name = "MSIZE"

    elif funct.find("signextend") != -1:
        instr_name = "SIGNEXTEND"

    elif funct.find("extcodesize") != -1:
        instr_name = "EXTCODESIZE"

    elif funct.find("create") != -1:
        instr_name = "CREATE"

    elif funct.find("gaslimit") != -1:
        instr_name = "GASLIMIT"

    elif funct.find("codesize") != -1:
        instr_name = "CODESIZE"

    elif funct.find("sha3") != -1:
        instr_name = "SHA3"

    elif funct.find("keccak256") != -1:
        instr_name = "KECCAK256"

    elif funct.find("gas") != -1:
        instr_name = funct.upper()

    elif funct.find("returndatasize") != -1:
        instr_name = "RETURNDATASIZE"

    elif funct.find("callcode") != -1:
        instr_name = "CALLCODE"

    elif funct.find("delegatecall") != -1:
        instr_name = "DELEGATECALL"

    elif funct.find("staticcall") != -1:
        instr_name = "STATICCALL"

    elif funct.find("callstatic") != -1:
        instr_name = "CALLSTATIC"

    elif funct.find("call") != -1:
        instr_name = "CALL"

    # Yul opcodes

    elif funct.find("pushtag") != -1:
        instr_name = "PUSH [tag]"

    elif funct.find("push#[$]") != -1:
        instr_name = "PUSH #[$]"

    elif funct.find("push[$]") != -1:
        instr_name = "PUSH [$]"

    elif funct.find("pushdata") != -1:
        instr_name = "PUSH data"

    elif funct.find("pushimmutable") != -1:
        instr_name = "PUSHIMMUTABLE"

    return instr_name

def generate_userdefname(u_var,funct,args,arity,init=False):
    global user_def_counter
    global already_defined_userdef

    #TODO: Add more opcodes
    instr_name = funct_to_opcode(funct)
    
    if instr_name in already_defined_userdef:
        if not split_sto and not init and instr_name in ["SLOAD","MLOAD","KECCAK256","SHA3"]:
            defined = -1
        else:
            defined = check_inputs(instr_name,args)
    else:
        defined = -1

        # if instr_name not in ["PUSH [tag]","PUSH #[$]","PUSH [$]","PUSH data"]:
        already_defined_userdef.append(instr_name)
            
    if defined == -1:
        obj = {}

        if (instr_name.find("GAS")!=-1 and instr_name.find("GASPRICE")==-1 and instr_name.find("GASLIMIT")==-1) \
                or instr_name.find("TIMESTAMP")!=-1:
            instr_name = instr_name[:-1]
        
        if funct == args: #0-ary functions
            name = instr_name
        else:
            idx = user_def_counter.get(instr_name,0)    
            name = instr_name+"_"+str(idx)

        args_aux = []
        for e in args:
            val = is_integer(e)
            if val != -1:
                args_aux.append(val)
            else:
                args_aux.append(e)
                
        obj["id"] = name
        obj["opcode"] = process_opcode(str(opcodes.get_opcode(instr_name)[0]))
        obj["disasm"] = instr_name
        obj["inpt_sk"] = [] if arity==0 or instr_name in ["PUSH [tag]","PUSH #[$]","PUSH [$]","PUSH data","PUSHIMMUTABLE","PUSHLIB"] else args_aux
        obj["outpt_sk"] = [u_var]
        obj["push"] = "PUSH" in instr_name
        obj["gas"] = opcodes.get_ins_cost(instr_name)
        obj["commutative"] = True if instr_name in commutative_bytecodes else False
        obj["storage"] = False #It is true only for MSTORE and SSTORE
        if instr_name in ["PUSH [tag]","PUSH #[$]","PUSH [$]","PUSH data","PUSHIMMUTABLE","PUSHLIB"]:
            obj["value"] = args_aux
        user_def_counter[instr_name]=idx+1
        obj["size"] = get_ins_size(instr_name)
        
        new = True
    else:
        obj = defined
        new = False


    return new, obj

def times_used_userdef_instructions(user_def,tstack,all_input_values):
    all_vars = tstack+all_input_values
    for instr in user_def:
        [output] = instr["outpt_sk"]
        used = list(filter(lambda x : str(x).strip() == output.strip(),all_vars))
        instr["times_used"] = len(used)

def process_opcode(result):
    op_val = hex(int(result))[2:]

    if (int(op_val,16)<12):
        op_val = "0"+str(op_val)
    return op_val

def modified_svariable(old_uvar, new_uvar):
    global s_dict
    global u_dict
    global variable_content
    global user_defins
    
    for s_var in s_dict.keys():
        if str(s_dict[s_var]).find(old_uvar)!=-1:
            s_dict[s_var] = new_uvar

    for u_var in u_dict.keys():
        pos = old_uvar in u_dict[u_var][0]
        if pos:
            elems = list(u_dict[u_var][0])
            pos_var = elems.index(old_uvar)
            elems[pos_var] = new_uvar
            new_val = (tuple(elems),u_dict[u_var][1])
            u_dict[u_var] = new_val
            
    for v_var in variable_content.keys():
        if str(variable_content[v_var]).find(old_uvar)!=-1:
            variable_content[v_var] = new_uvar

    for uf in user_defins:
        if old_uvar in uf["inpt_sk"]:
            pos = uf["inpt_sk"].index(old_uvar)
            uf["inpt_sk"][pos] = new_uvar
        
def check_inputs(instr_name,args_aux):
    
    args = []
    for a in args_aux:
        if is_integer(a) !=-1:
            args.append(int(a))
        else:
            args.append(a)
            
    
    for elem in user_defins:
        name = elem["disasm"]
        if name == instr_name and name not in ["PUSH [tag]","PUSH #[$]","PUSH [$]","PUSH data","PUSHIMMUTABLE","PUSHLIB"]:
            input_variables = elem["inpt_sk"]
            if instr_name in commutative_bytecodes:
                if ((input_variables[0] == args[1]) and (input_variables[1] == args[0])) or ((input_variables[0] == args[0]) and (input_variables[1] == args[1])):
                    return elem
                
            else:
                i = 0
                equals = True
                while (i <len(input_variables) and equals):
                    
                    if args[i] !=input_variables[i]:
                        equals = False
                    i+=1

                if equals:
                    return elem

        elif name == instr_name and name in ["PUSH [tag]","PUSH #[$]","PUSH [$]","PUSH data","PUSHIMMUTABLE","PUSHLIB"]:
            input_variables = elem["value"]
            i = 0
            equals = True
            while (i <len(input_variables) and equals):
                    
                if args[i] !=input_variables[i]:
                    equals = False
                i+=1

            if equals:
                return elem

            
    return -1

def split_blocks(rule,opt = False,new_instr = []):
    blocks = []
    
    ins_block = []
    
    if opt:
        instructions = new_instr
    else:
        instructions = rule.get_instructions()
    
    for ins in instructions:
        ins_block.append(ins)
        if ins.startswith("nop("):
            nop = ins[4:-1]
            
            if nop in constants.split_block or nop in terminate_block:
                prev = ins_block[-2]
                blocks.append(ins_block)
                ins_block = [prev,ins]

    blocks.append(ins_block)
    
    return blocks
            


def get_max_stackindex_set(instructions):
    max_idx = float('-inf')
    for ins in instructions:
        vars_ins = ins.split("=")
        var = vars_ins[0].strip()

        idx = int(var[2:-1])
        
        if max_idx < idx:
            max_idx = idx
            
    return max_idx

def is_optimizable(opcode_instructions,instructions):
    ins_aux = list(map(lambda x: x.strip()[4:-1], opcode_instructions))
    ins = list(filter(lambda x: x in constants.split_block or x in terminate_block, ins_aux))

    if ins_aux != [] and list(filter(lambda x: x.find("POP")==-1, ins_aux)) == []:
        return True
    
    if ins == []:

        return True if (instructions[:-1]!=[] or len(instructions)==1) else False
    else:
        return False

def translate_block(rule,instructions,opcodes,isolated,sub_block_name,simp):
    global max_instr_size
    global max_stack_size
    global num_pops
    global gas_t
    
    source_stack_idx = get_stack_variables(rule)   
    
    if not isolated: 
        if "nop(JUMPI)" in opcodes:
            guards_op = get_jumpi_opcodes(rule)
            num_guard = get_numguard_variables(guards_op)
        else:
            guards_op = []
            num_guard = 0

    else:
        num_guard = 0
        guards_op = []
        
    if "nop(JUMP)" in opcodes or "nop(JUMPI)" in opcodes:
        max_instr_size = len(opcodes)-num_guard-1
    else:
        max_instr_size = len(opcodes)-num_guard

    max_instr_size = compute_max_program_len(opcodes, num_guard)
    
    if not isolated:
        pops = list(filter(lambda x: x.find("nop(POP)")!=-1,opcodes))
        num_pops = len(pops)
        x = list(filter(lambda x: (x.find("POP")==-1) and (x.find("JUMPDEST")==-1) and (x.find("JUMP")==-1)and(x.find("JUMPI")==-1),opcodes))
        if x == [] and num_pops >0:

            t_vars_idx = source_stack_idx-num_pops
            seq = range(0,t_vars_idx)
            t_vars = list(map(lambda x: "s("+str(x)+")",seq))[::-1]
            
        else:
            t_vars = generate_vars_target_stack(num_guard,instructions[-1],opcodes)[::-1]
    else:
        t_vars = generate_target_stack_idx(source_stack_idx,opcodes)[::-1]

    pops = list(filter(lambda x: x.find("nop(POP)")!=-1,opcodes))
    num_pops = len(pops)

    source_stack = generate_source_stack_variables(source_stack_idx)
    get_s_counter(source_stack,t_vars)

    generate_encoding(instructions,t_vars,source_stack,opcodes,simp)
    
    build_userdef_instructions()
    gas = get_block_cost(opcodes,len(guards_op))
    max_stack_size = max_idx_used(instructions,t_vars)

    if  gas!=0 and not is_identity_map(source_stack,t_vars,instructions):
       
        gas_t+=get_cost(original_opcodes)
        
        new_opcodes = compute_opcodes2write(opcodes,num_guard)

        # if not simp:
        #     index, fin = find_sublist(rule.get_instructions(),new_opcodes)
        #     init_info = get_encoding_init_block(rule.get_instructions()[index:fin+1],source_stack)
        # else:
        init_info = {}
        generate_json(sub_block_name,source_stack,t_vars,source_stack_idx-1,gas, init_info,simplification = simp)
        if simp:
            write_instruction_block(sub_block_name,new_opcodes)


def compute_opcodes2write(opcodes,num_guard):
    if "nop(JUMPDEST)" in opcodes:
        new_opcodes_aux = opcodes[1:]
    else:
        new_opcodes_aux = opcodes

    if "nop(JUMPI)" in new_opcodes_aux:
        new_opcodes = new_opcodes_aux[:-1-num_guard]
    elif "nop(JUMP)" in new_opcodes_aux:
        new_opcodes = new_opcodes_aux[:-1]
    else:
        new_opcodes = new_opcodes_aux

    return new_opcodes
        
def generate_subblocks(rule,list_subblocks,isolated,sub_block_name,simplification):
    global gas_t
    global revert_flag

    prev_revert_flag = revert_flag
    revert_flag = False
    
    source_stack_idx = get_stack_variables(rule)
    source_stack = generate_source_stack_variables(source_stack_idx)

    source_stack_idx-=1
    i = 0

    pops2remove = 0
    while(i < len(list_subblocks)-1):

        init_globals()
        block = list_subblocks[i]
        nop_instr = block[-1]
        last_instr = block[-2]

        ts_idx = compute_target_stack_subblock(last_instr,nop_instr)

        seq = range(ts_idx,-1,-1)
        target_stack = list(map(lambda x: "s("+str(x)+")",seq))

        new_nexts, pops2remove = translate_subblock(rule,block,source_stack,target_stack,source_stack_idx,i,list_subblocks[i+1],sub_block_name,simplification,pops2remove)

        if new_nexts == []:
        #We update the source stack for the new block
            source_stack, source_stack_idx = get_new_source_stack(last_instr,nop_instr,ts_idx)
        else:
            new_block = new_nexts[0]

            new_idxstack= new_nexts[1] #it returns the last index of sstore

            list_subblocks[i+1] = new_block
            source_stack_idx = new_idxstack
            seq = range(source_stack_idx-1,-1,-1)
            source_stack = list(map(lambda x: "s("+str(x)+")",seq))
            
        i+=1

    instrs = list_subblocks[-1]

    if source_stack == []:
        source_stack_idx = -1

    block = instrs[2:]
    if block != []:
        revert_flag = prev_revert_flag
        translate_last_subblock(rule,block,source_stack,source_stack_idx,i,isolated,sub_block_name,simplification,pops2remove)

    if compute_gast:
        gas_t+=get_cost(original_opcodes)

    
def translate_subblock(rule,instrs,sstack,tstack,sstack_idx,idx,next_block,sub_block_name,simp,prev_pops):
    global max_instr_size
    global max_stack_size
    global num_pops
    global compute_gast
    global original_ins
    
    if idx == 0:
        instructions = instrs[:-2]
    else:
        instructions = instrs[2:-2]
            
    rbr_ins_aux = list(filter(lambda x: x.find("nop(")==-1, instructions))
    instr = list(filter(lambda x: x!="" and x.find("skip")==-1, rbr_ins_aux))
    
    opcodes = list(filter(lambda x: x.find("nop(")!=-1,instructions))
    max_instr_size = compute_max_program_len(opcodes, 0)

    
    pops = list(filter(lambda x: x.find("nop(POP)")!=-1,opcodes))
    num_pops = len(pops)

    new_nexts = []
    
    if instr!=[]:
        get_s_counter(sstack,tstack)
        
        generate_encoding(instr,tstack,sstack,opcodes,simp)
        build_userdef_instructions()
        gas = get_block_cost(opcodes,0)
        max_stack_size = max_idx_used(instructions,tstack)
        pops2remove = 0
        if max_stack_size!=0 and gas !=0 and not is_identity_map(sstack,tstack,instructions):
            compute_gast = True
            new_tstack,new_nexts = tstack,[] #optimize_splitpop_block(tstack,sstack,next_block,opcodes)
            # if new_nexts != []:
            #     pops2remove = new_nexts[2]
            #     # gas = gas+2*pops2remove
            #     max_instr_size+=pops2remove

            new_opcodes = compute_opcodes2write(opcodes,0)
            new_ops = list(map(lambda x: x[4:-1],new_opcodes))
            original_ins = new_ops

            # if not simp:
            #     index, fin = find_sublist(instructions,new_opcodes)
            #     init_info = get_encoding_init_block(instructions[index:fin+1],sstack)
            # else:
            init_info = {}

            if prev_pops != 0:
                gas = gas+2*prev_pops
                
            generate_json(sub_block_name,sstack,new_tstack,sstack_idx,gas,init_info,subblock=idx,simplification = simp)
            if simp:
                write_instruction_block(sub_block_name, new_opcodes,subblock=idx)
            
        return new_nexts, pops2remove
    else:
        return [],0

            

def optimize_splitpop_block(tstack,source_stack,next_block,opcodes):
    
    i = 0
    target_stack = compute_target_stack(tstack)
    opcodes_next_total = list(filter(lambda x: x.find("nop(")!=-1,next_block))
    split_opcode = opcodes_next_total[0]
    opcodes_next = opcodes_next_total[1:]
    stop = False
    while(not stop and i <len(opcodes_next)):
        op = opcodes_next[i]
        if op != "nop(POP)":
          stop = True
        else:
          i+=1

    if i == 0:
        return tstack,[]
    else:
        if split_opcode == "nop(SSTORE)" or split_opcode == "nop(MSTORE)":
            split_stack = target_stack[:2]
            rest_stack = target_stack[2:]
            finished = False
            init_i = i
            while(i>0 and rest_stack !=[] and not finished):
                val = rest_stack.pop(0)

                if val in source_stack and val not in split_stack:
                    finished = True
                    rest_stack = [val]+rest_stack
                else:
                    i-=1

            todelete= True
            source_copy = list(source_stack)
            while i > 0 and todelete and (source_copy != []) and (rest_stack !=[]):
                val1 = rest_stack.pop(0)
                val2 = source_copy.pop(0)
                if val1 == val2:
                    i-=1
                else:
                    todelete = False
          
            pops2remove = init_i-i


            new_next_block,new_next_stack = modify_next_block(next_block,pops2remove)

            
            end_target_stack = tstack[:2]+tstack[2+pops2remove:]#split_stack+rest_stack

            return end_target_stack,(new_next_block,new_next_stack,pops2remove)
        else:
          return tstack,[]


def modify_next_block(next_block,pops2remove):
    split_instr = next_block[0]

    name = split_instr.split("(")[0]

    idx1 = int(split_instr.split(",")[0][9:-1]) #sstore(
    idx2 = int(split_instr.split(",")[1][2:-2])

    new_name = name+"(s("+str(idx1-pops2remove)+"),s("+str(idx2-pops2remove)+"))"

    new_nextblock = [new_name,next_block[1]]+next_block[2+pops2remove*2:]
    return new_nextblock,idx2-pops2remove
    
    
def translate_last_subblock(rule,block,sstack,sstack_idx,idx,isolated,block_name,simp, prev_pops):
    global max_instr_size
    global max_stack_size
    global num_pops
    global compute_gast
    global original_ins
    
    init_globals()
    
    if not isolated:
        if "nop(JUMPI)" in block:
            guards_op = get_jumpi_opcodes(rule)

            num_guard = get_numguard_variables(guards_op)
        else:
            guards_op = []
            num_guard = 0
    else:
        num_guard = 0
        guards_op = []
        
    rbr_ins_aux = list(filter(lambda x: x.find("nop(")==-1, block))
    instructions = list(filter(lambda x: x!="" and x.find("skip")==-1, rbr_ins_aux))

    
    opcodes = list(filter(lambda x: x.find("nop(")!=-1,block))
    max_instr_size = compute_max_program_len(opcodes, num_guard)
    
    if opcodes != []:

        pops = list(filter(lambda x: x.find("nop(POP)")!=-1,opcodes))
        num_pops = len(pops)
        
        if not isolated:

            x = list(filter(lambda x: (x.find("POP")==-1) and (x.find("JUMPDEST")==-1) and (x.find("JUMP")==-1)and(x.find("JUMPI")==-1),opcodes))

            if x == [] and num_pops >0:
                t_vars_idx = sstack_idx-num_pops+1
                if t_vars_idx == sstack_idx and num_pops>0:
                    t_vars_idx-=1
                seq = range(0,t_vars_idx)
                tstack = list(map(lambda x: "s("+str(x)+")",seq))[::-1]
                
            else:
                
                tstack = generate_vars_target_stack(num_guard,instructions[-1],opcodes)[::-1]
        else:
            
            tstack = generate_target_stack_idx(len(sstack),opcodes)[::-1]
        get_s_counter(sstack,tstack)

        if idx is not None:
            block_nm = block_name + "_" + str(idx)
        else:
            block_nm = block_name + "_0"


        msg = paths.json_path+"/"+ block_nm + "_input.json"
        check_and_print_debug_info(debug, msg)

        generate_encoding(instructions,tstack,sstack,opcodes,simp)
    
        build_userdef_instructions()
        gas = get_block_cost(opcodes,len(guards_op))
        max_stack_size = max_idx_used(instructions,tstack)
        if gas!=0 and not is_identity_map(sstack,tstack,instructions):
            compute_gast = True
            new_opcodes = compute_opcodes2write(opcodes,num_guard)
            new_ops = list(map(lambda x: x[4:-1],new_opcodes))

            original_ins = new_ops
            
            # if not simp:
            #     index, fin = find_sublist(block,new_opcodes)
            #     init_info = get_encoding_init_block(block[index:fin+1],sstack)
            # else:
            init_info = {}

            if prev_pops!=0:
                gas+=2*prev_pops
                
            generate_json(block_name,sstack,tstack,sstack_idx,gas,init_info,subblock=idx,simplification = simp)
            if simp:
                write_instruction_block(block_name,new_opcodes,subblock=idx)
    
def get_new_source_stack(instr,nop_instr,idx):
    
    if instr.find("=")!=-1:
        ins = instr.strip()
        var = ins.split("=")[0].strip()
        var_idx = int(var[2:-1])
        seq = range(var_idx,-1,-1)
        return (list(map(lambda x: "s("+str(x)+")",seq)),var_idx)

    else:

        bytecode = nop_instr.strip()[4:-1]
        bytecode_info = opcodes.get_opcode(bytecode)
        delta = bytecode_info[1]

        new_idx = idx-delta
        seq = range(new_idx,-1,-1)
        return (list(map(lambda x: "s("+str(x)+")",seq)),new_idx)
        
def compute_target_stack_subblock(instr, nop):
    bytecode = nop.strip()[4:-1]

    bytecode_info = opcodes.get_opcode(bytecode)
    alpha = bytecode_info[1]
    delta = bytecode_info[2]

    total = alpha - delta
    
    if instr.find("=")!=-1:
        vars_instr = instr.split("=")
        var = vars_instr[0].strip()

        idx_var = int(var[2:-1])

        idx_tstack = idx_var+total

    else:
        instr_aux = instr.strip()
        pos_open_br = instr_aux.find("(")


        variables = instr_aux[pos_open_br+1:-1].split(",")
        vars_aux = list(map(lambda x: int(x[2:-1]), variables))
        idx_tstack = max(vars_aux)

    return idx_tstack


def get_block_cost(opcodes_list,opcodes_guard):
    real_opcodes_aux = list(map(lambda x: x.strip()[4:-1],opcodes_list))
   
    if "JUMPDEST" in real_opcodes_aux:
        real_opcodes_aux.pop(0)

    if "JUMPI" in real_opcodes_aux:
        idx = -1-opcodes_guard
        real_opcodes = real_opcodes_aux[:idx]
    elif "JUMP" in real_opcodes_aux:
        real_opcodes = real_opcodes_aux[:-1]
    else:
        real_opcodes = real_opcodes_aux
   
    val = 0
    for op in real_opcodes:
        if op == "MULMOD":
            gas = 10
        else:
            gas = opcodes.get_ins_cost(op.strip())
        val+=gas
    return val

def get_cost(opcodes_list):
    real_opcodes_aux = list(map(lambda x: x.strip()[4:-1],opcodes_list))

    real_opcodes = real_opcodes_aux
    val = 0
    for op in real_opcodes:
        if op == "MULMOD" or op == "ADDMOD":
            gas = 10
        else:
            gas = opcodes.get_ins_cost(op.strip())
        val+=gas
    return val



def split_terminal_block(rule):
    blocks = []
    
    ins_block = []

    instructions = rule.get_instructions()
    
    for ins in instructions:
        ins_block.append(ins)
        if ins.startswith("nop("):
            nop = ins[4:-1]
            
            if nop in constants.split_block+terminate_block:
                prev = ins_block[-2]
                blocks.append(ins_block)
                ins_block = [prev,ins]

    blocks.append(ins_block)
    
    return blocks

def generate_terminal_subblocks(rule,list_subblocks):
    global gas_t
    
    source_stack_idx = get_stack_variables(rule)
    source_stack = generate_source_stack_variables(source_stack_idx)

    source_stack_idx-=1
    i = 0

    pops2remove = 0
    while(i < len(list_subblocks)-1):
        init_globals()
        block = list_subblocks[i]
        
        nop_instr = block[-1]
        last_instr = block[-2]
        ts_idx = compute_target_stack_subblock(last_instr,nop_instr)
        
        seq = range(ts_idx,-1,-1)
        target_stack = list(map(lambda x: "s("+str(x)+")",seq))
        

        new_nexts,pops2remove = translate_subblock(rule,block,source_stack,target_stack,source_stack_idx,i,list_subblocks[i+1], pops2remove)

        if new_nexts == []:

            source_stack, source_stack_idx = get_new_source_stack(last_instr,nop_instr,ts_idx)
        else:
            new_block = new_nexts[0]
            new_idxstack= new_nexts[1] # it is the index of the last argument of sstore
            list_subblocks[i+1] = new_block
            source_stack_idx = new_idxstack
            seq = range(source_stack_idx-1,-1,-1)
            source_stack = list(map(lambda x: "s("+str(x)+")",seq))

        i+=1
    if compute_gast:
        gas_t+=get_cost(original_opcodes)
        
def translate_terminal_block(rule):
    blocks = split_terminal_block(rule)
    generate_terminal_subblocks(rule,blocks)

        
def write_instruction_block(rule_name,opcodes,subblock = None):
    if subblock is not None:
        block_nm = rule_name+"_"+str(subblock)
    else:
        block_nm = rule_name

    op = list(map(lambda x: x[4:-1],opcodes))
    
    if "disasms" not in os.listdir(paths.gasol_path):
        os.mkdir(paths.gasol_path+"/disasms")
    
    byte_file =  open(paths.gasol_path+"/disasms/" + block_nm+".disasm","w")
    for e in op:
        byte_file.write(e+"\n")
    byte_file.close()

def max_idx_used(instructions,tstack):
    
    if instructions == []:
        return 0
    
    if instructions[-1].find("call(")!=-1:
        idxs_call = list(map(lambda x: int(x[2:-1]),tstack))
    else:
        idxs_call = [0]

        
    insts = list(filter(lambda x: x.find("=")!=-1,instructions))
    variables = list(map(lambda x: x.split("=")[0].strip(),insts))

    real_variables = list(filter(lambda x: x.find("s(")!=-1,variables))
    idxs = list(map(lambda x: int(x[2:-1]),real_variables))

    if idxs == []:
        idxs = [0]
    
    try:
        max_call = max(idxs_call)
        max_body = max(idxs)
        max_number = max(max_call,max_body)+1
    except:
        max_number = 0
    return max_number


def compute_max_program_len(opcodes, num_guard,block = None):
    if "nop(JUMPDEST)" in opcodes:
        new_opcodes_aux = opcodes[1:]
    else:
        new_opcodes_aux = opcodes

    if "nop(JUMPI)" in new_opcodes_aux:
        new_opcodes = new_opcodes_aux[:-1-num_guard]
    elif "nop(JUMP)" in new_opcodes_aux:
        new_opcodes = new_opcodes_aux[:-1]

    else:
        new_opcodes = new_opcodes_aux

    return len(new_opcodes)
    

def smt_translate_block(rule,file_name,block_name,immutable_dict,simplification=True,storage = False, size = False, part = False, pop = False, push = False, revert = False,extra_dependences_info={},extra_opt_info= {}, debug_info = False):
    global s_counter
    global max_instr_size
    global int_not0
    global source_name
    global blocks_json_dict
    global sfs_contracts
    global split_sto
    global original_ins
    global max_l
    global size_flag
    global pop_flag
    global push_flag
    global revert_flag
    global assignImm_values
    global debug
    
    init_globals()
    
    if storage:
        split_sto = True
        constants.append_store_instructions_to_split()

    size_flag = size
    pop_flag = pop
    push_flag = push
    revert_flag = revert
    assignImm_values = immutable_dict
    debug = debug_info
            
    sfs_contracts = {}

    blocks_json_dict = {}
    
    info_deploy = []

    source_name = file_name

    int_not0 = [-1+2**256]#map(lambda x: -1+2**x, range(8,264,8))
    
    begin = dtimer()
    
    instructions = filter_opcodes(rule)
    
    opcodes = get_opcodes(rule)    

    print(extra_opt_info)
    
    if extra_opt_info["relations"]:
        process_extra_dependences_info(extra_dependences_info,"memory")
        process_extra_dependences_info(extra_dependences_info,"storage")

    if extra_opt_info["useless"]:
        process_useless_info(extra_dependences_info)
        print(useless_info)

    
    info = "INFO DEPLOY "+paths.gasol_path+"ethir_OK_"+ block_name + " LENGTH="+str(len(opcodes))+" PUSH="+str(len(list(filter(lambda x: x.find("nop(PUSH")!=-1,opcodes))))
    info_deploy.append(info)
    
    subblocks = []
    res = is_optimizable(opcodes,instructions)
    if res:
        ops = list(map(lambda x: x[4:-1],opcodes))

        original_ins = ops

        if part:
            if len(opcodes) > max_bound and not split_sto:
                stores_pos = compute_position_stores(opcodes)
                where2split = split_by_numbers(stores_pos)

                if where2split == []:
                    subblocks = [opcodes]
                    translate_block(rule,instructions,opcodes,True,block_name,simplification)

                else:
                    subblocks = split_blocks_by_number(rule.get_instructions(),where2split)
                    generate_subblocks(rule,subblocks,True,block_name,simplification)
            else:
                subblocks = [opcodes]
                translate_block(rule,instructions,opcodes,True,block_name,simplification)
        else:
            subblocks = [opcodes]
            translate_block(rule,instructions,opcodes,True,block_name,simplification)
    else: #we need to split the blocks into subblocks
        r = False
        new_instructions = []

        subblocks = split_blocks(rule,r,new_instructions)

        if part:
            end_subblocks = []
            for s in subblocks:
                o = list(filter(lambda x:x.find("nop(")!=-1,s))

                if split_sto:
                    stores_pos = []
                else:
                    stores_pos = compute_position_stores(o)
                
                if len(o)> max_bound and stores_pos !=[]:
                    where2split = split_by_numbers(stores_pos)
                    if where2split == []:
                        end_subblocks.append(s)
                    else:
                        subblocks_aux = split_blocks_by_number(s,where2split)
                        end_subblocks+=subblocks_aux
                else:
                    end_subblocks.append(s)
            subblocks = end_subblocks
        generate_subblocks(rule,subblocks,True,block_name,simplification)

    end = dtimer()

    sfs_contracts["syrup_contract"] = blocks_json_dict
    end = dtimer()

    subblocks_postprocess = []
    for s in subblocks:
        s1 = list(filter(lambda x: x.find("nop(")!=-1,s))
        ins = list(map(lambda x: x.strip()[4:-1],s1))
        subblocks_postprocess.append(ins)

    return subblocks_postprocess

def apply_transform(instr):
    global discount_op
    global saved_push
    global gas_saved_op
    global rule

    
    opcode = instr["disasm"]
    if opcode == "AND":
        inp_vars = instr["inpt_sk"]
        if 0 in inp_vars:
            saved_push+=2
            gas_saved_op+=3
            
            discount_op+=1
            rule = "AND(X,0)"
            return 0
        elif inp_vars[0] == inp_vars[1]:
            saved_push+=1
            gas_saved_op+=3

            discount_op+=1
            rule = "AND(X,X)"
            return inp_vars[0]
    
        elif inp_vars[0] in int_not0 or inp_vars[1] in int_not0:
            saved_push+=2
            gas_saved_op+=3

            discount_op+=1
            rule = "AND(X,2^256-1)"
            return inp_vars[1] if (inp_vars[0] in int_not0) else inp_vars[0]
        else:
            return -1
        
    elif opcode == "OR":
        inp_vars = instr["inpt_sk"]
        if 0 in inp_vars:
            saved_push+=2
            gas_saved_op+=3

            discount_op+=1
            rule = "OR(X,0)"
            return inp_vars[1] if inp_vars[0] == 0 else inp_vars[0]
        elif inp_vars[0] == inp_vars[1]:
            saved_push+=1
            gas_saved_op+=3

            discount_op+=1
            rule = "OR(X,X)"
            return inp_vars[0]
        else:
            return -1

    elif opcode == "XOR":
        inp_vars = instr["inpt_sk"]
        
        if inp_vars[0] == inp_vars[1]:
            saved_push+=1
            gas_saved_op+=3

            discount_op+=1
            rule = "XOR(X,X)"
            return 0
        elif 0 in inp_vars:
            saved_push+=2
            gas_saved_op+=3

            discount_op+=1
            rule = "XOR(X,0)"
            return inp_vars[1] if inp_vars[0] == 0 else inp_vars[0]
        else:
            return -1

    elif opcode == "EXP":
        inp_vars = instr["inpt_sk"]
        
        if inp_vars[1] == 0:
            saved_push+=2
            gas_saved_op+=60

            discount_op+=1
            rule = "EXP(X,0)"
            return 1
        elif inp_vars[1] == 1:
            saved_push+=1
            gas_saved_op+=60
            
            discount_op+=1
            rule = "EXP(X,1)"
            return inp_vars[0]
        elif inp_vars[0] == 1:
            gas_saved_op+=60
            
            discount_op+=1
            rule = "EXP(1,X)"
            return 1
        else:
            return -1

    elif opcode == "ADD":
        inp_vars = instr["inpt_sk"]
        if 0 in inp_vars:
            saved_push+=1
            gas_saved_op+=3

            discount_op+=1
            rule = "ADD(X,0)"
            return inp_vars[1] if inp_vars[0] == 0 else inp_vars[0]
        else:
            return -1

    elif opcode == "SUB":
        inp_vars = instr["inpt_sk"]
        if 0 == inp_vars[1]:
            saved_push+=1
            gas_saved_op+=3

            discount_op+=1
            rule = "SUB(X,0)"
            return inp_vars[0]
        elif inp_vars[0] == inp_vars[1]:
            saved_push+=1
            gas_saved_op+=3

            discount_op+=1
            rule = "SUB(X,X)"
            return 0
        else:
            return -1
        
    elif opcode == "MUL":
        inp_vars = instr["inpt_sk"]
        if 0 in inp_vars:
            saved_push+=2
            gas_saved_op+=5

            discount_op+=1
            rule = "MUL(X,0)"
            return 0
        elif 1 in inp_vars:
            saved_push+=1
            gas_saved_op+=5
            
            discount_op+=1
            rule = "MUL(X,1)"
            return inp_vars[1] if inp_vars[0] == 1 else inp_vars[0]
        else:
            return -1

    elif opcode == "DIV":
        inp_vars = instr["inpt_sk"]
        if  1 == inp_vars[1]:
            saved_push+=1
            gas_saved_op+=5
            
            discount_op+=1
            rule = "DIV(X,1)"
            return inp_vars[0]

        elif 0 in inp_vars:
            saved_push+=2
            gas_saved_op+=5

            discount_op+=1
            rule = "DIV(X,0)"
            return 0

        elif inp_vars[0] == inp_vars[1]:
            saved_push+=2
            gas_saved_op+=5

            discount_op+=1
            rule = "DIV(X,X)"
            return 1
        else:
            return -1

    elif opcode == "MOD":
        inp_vars = instr["inpt_sk"]
        if  1 == inp_vars[1]:
            saved_push+=2
            gas_saved_op+=5
            
            discount_op+=1
            rule = "MOD(X,1)"
            return 0

        elif inp_vars[0] == inp_vars[1]:
            saved_push+=2
            gas_saved_op+=5

            discount_op+=1
            rule = "MOD(X,X)"
            return 0

        elif inp_vars[1] == 0:
            saved_push+=2
            gas_saved_op+=5

            discount_op+=1
            rule = "MOD(X,0)"
            return 0

        else:
            return -1

    elif opcode == "EQ":
        inp_vars = instr["inpt_sk"]
        if inp_vars[0] == inp_vars[1]:
            discount_op+=1
            saved_push+=2
            gas_saved_op+=3

            rule = "EQ(X,X)"
            
            return 1
        else:
            return -1

    elif opcode == "GT" or opcode == "SGT":
        inp_vars = instr["inpt_sk"]
        if inp_vars[0] == 0 and opcode == "GT":
            saved_push+=2
            gas_saved_op+=3

            discount_op+=1

            rule = "GT(0,X)"
            
            return 0
        elif inp_vars[0] == inp_vars[1]:
            discount_op+=1
            saved_push+=2
            gas_saved_op+=3

            rule = opcode+"(X,X)"
            return 0
        else:
            return -1

    elif opcode == "LT" or opcode == "SLT":
        inp_vars = instr["inpt_sk"]
        if inp_vars[1] == 0 and opcode == "LT":
            saved_push+=2
            gas_saved_op+=3

            discount_op+=1

            rule = "LT(X,0)"
            return 0
        elif inp_vars[0] == inp_vars[1]:
            discount_op+=1
            saved_push+=2
            gas_saved_op+=3

            rule = opcode+"(X,X)"
            return 0
        else:
            return -1

    elif opcode == "NOT":
        inp_vars = instr["inpt_sk"]
        r, val = all_integers(inp_vars)
        if r:
            val_end = ~(int(val[0]))+2**256

            if size_flag:
                v0 = int(val[0])
                bytes_v0 = get_num_bytes_int(v0)
                bytes_sol = get_num_bytes_int(val_end)

                if bytes_sol <= bytes_v0+1:    
                    saved_push+=1
                    gas_saved_op+=3
                    rule = "NOT(X)"
                    return val_end
                else:
                    return -1

            else:
                saved_push+=1
                gas_saved_op+=3
                rule = "NOT(X)"
                return val_end
            
        else:
            return -1
        
    elif opcode == "ISZERO":
        inp_vars = instr["inpt_sk"]
        if inp_vars[0] == 0:
            gas_saved_op+=3
            saved_push+=1
            rule = "ISZ(0)"
            return 1
        elif inp_vars[0] == 1:
            gas_saved_op+=3
            saved_push+=1
            rule = "ISZ(1)"
            return 0
        else:
            return -1

    elif opcode == "SHR" or opcode == "SHL":
        inp_vars = instr["inpt_sk"]
        if inp_vars[0] == 0:
            discount_op+=1
            saved_push+=2
            gas_saved_op+=3

            rule = opcode+"(0,X)"
            
            return inp_vars[1]
        elif inp_vars[1] == 0:
            discount_op+=1
            saved_push+=2
            gas_saved_op+=3
            rule = opcode+"(X,0)"
            return inp_vars[0]
        else:
            return -1


def apply_all_simp_rules(user_def,list_vars,tstack):
    global rule_applied
    
    modified = True
    user_def_instrs = user_def
    target_stack = tstack
    while(modified):

        modified, user_def_instrs,target_stack = apply_transform_rules(user_def_instrs,list_vars,target_stack)
        if modified:
           rule_applied = True 
    return user_def_instrs,target_stack

def apply_transform_rules(user_def_instrs,list_vars,tstack):
    global rules_applied
    global rule

    to_delete = []
    target_stack = tstack
    modified = False
    for instr in user_def_instrs:
        
        if instr["disasm"] in ["AND","OR","XOR","ADD","SUB","MUL","DIV","EXP","EQ","GT","LT","SGT","SLT","NOT","ISZERO"]:
            r = apply_transform(instr)

            if r!=-1:
                rules_applied.append(rule)
                rule = ""
                msg = "[RULE]: Simplification rule type 1: "+str(instr)
                check_and_print_debug_info(debug, msg)
                
                replace_var_userdef(instr["outpt_sk"][0],r,user_def_instrs)
                target_stack = replace_var(instr["outpt_sk"][0],r,target_stack)
                delete_from_listvars(instr["outpt_sk"][0],list_vars)
                to_delete.append(instr)
                modified = True
    i = 0
    new_user_def = []
    while len(user_def_instrs)>0:
        instr = user_def_instrs.pop()
        if instr not in to_delete:
            new_user_def.append(instr)


    return modified, new_user_def, target_stack

def replace_var_userdef(out_var,value,user_def):
    modified_instrs = []
    for instr in user_def:
        inpt = instr["inpt_sk"]
        if out_var in inpt:
            idx = inpt.index(out_var)
            part1 = inpt[:idx]
            part2 = inpt[idx+1:]
            part1.append(value)
            new_inpt = part1+part2
            instr["inpt_sk"] = new_inpt
            
def replace_var(out_var,value,tstack):
    new_stack = []
    if out_var in tstack:
        for s in tstack:
            if s!= out_var:
                new_stack.append(s)
            else:
                new_stack.append(value)
        return new_stack
    else:
        return tstack

def delete_from_listvars(out_var,list_vars):
    idx = list_vars.index(out_var)
    list_vars.pop(idx)


def check_rule_iszero_gt(num_gt,num_iszero):
    for gt in num_gt:
        o_var = gt["outpt_sk"]
        


def apply_cond_transformation(instr,user_def_instrs,tstack):
    global discount_op
    global saved_push
    global gas_saved_op
    global user_def_counter
    global rule
    
    opcode = instr["disasm"]
    
    if opcode == "GT" or opcode == "SGT":
        if 0 == instr["inpt_sk"][1] and opcode == "GT":
            out_var = instr["outpt_sk"][0]
            is_zero = list(filter(lambda x: out_var in x["inpt_sk"] and x["disasm"] == "ISZERO",user_def_instrs))
            if len(is_zero) == 1 and out_var not in tstack:
                # print(tstack)
                # raise Exception
                index = user_def_instrs.index(is_zero[0])
                zero_instr = user_def_instrs[index]
                zero_instr["inpt_sk"] = [instr["inpt_sk"][0]]
                saved_push+=2
                gas_saved_op+=3

                
                if out_var not in tstack:
                    discount_op+=2

                msg = "ISZ(GT(X,0))"
                rule = msg
                check_and_print_debug_info(debug, msg)
                
                return True, []
            else:
                return False, []

        elif 1 == instr["inpt_sk"][0] and opcode == "GT":
            var = instr["inpt_sk"][1]
            idx = user_def_counter.get("ISZERO",0)
            instr["id"] = "ISZERO_"+str(idx)
            instr["opcode"] = "15"
            instr["disasm"] = "ISZERO"
            instr["inpt_sk"] = [var]
            instr["commutative"] = False
            discount_op+=1
            saved_push+=2

            user_def_counter["ISZERO"]=idx+1
            
            msg = "GT(1,X)"
            rule = msg
            check_and_print_debug_info(debug, msg)
            return True, []


        else:
            out_var = instr["outpt_sk"][0]
            is_zero = list(filter(lambda x: out_var in x["inpt_sk"] and x["disasm"] == "ISZERO",user_def_instrs))
            if len(is_zero)==1:
                zero = is_zero[0]
                zero2 = list(filter(lambda x: zero["outpt_sk"][0] in x["inpt_sk"] and x["disasm"] == "ISZERO",user_def_instrs))
                if len(zero2) == 1 and zero["outpt_sk"][0] not in tstack:
                    # instr["outpt_sk"] = zero2[0]["outpt_sk"]
                    old_var = instr["outpt_sk"]
                    new_var = zero2[0]["outpt_sk"]
                    instr["outpt_sk"] = new_var
                    
                    discount_op+=2

                    gas_saved_op+=6

                    msg = "ISZ(ISZ("+opcode+"(X,Y)))" #It may be GT or SGT
                    rule = msg
                    check_and_print_debug_info(debug, msg)

                    update_tstack_userdef(old_var[0], new_var[0],tstack, user_def_instrs)
                    
                    return True, [zero,zero2[0]]
                else:
                    return False, []
            else:
                
                return False, []

    elif opcode == "ISZERO":
    
        out_var = instr["outpt_sk"][0]
        is_zero = list(filter(lambda x: out_var in x["inpt_sk"] and x["disasm"] == "ISZERO",user_def_instrs))

        is_eq = list(filter(lambda x: out_var in x["inpt_sk"] and x["disasm"] == "EQ",user_def_instrs))
        
        if len(is_zero)==1:
         
            zero = is_zero[0]
  
            zero2 = list(filter(lambda x: zero["outpt_sk"][0] in x["inpt_sk"] and x["disasm"] == "ISZERO",user_def_instrs))
            if len(zero2) == 1 and zero["outpt_sk"][0] not in tstack:
             
                # instr["outpt_sk"] = zero2[0]["outpt_sk"]
                old_var = instr["outpt_sk"]
                new_var = zero2[0]["outpt_sk"]
                instr["outpt_sk"] = new_var

                discount_op+=2
                
                gas_saved_op+=6

                msg = "ISZ(ISZ(ISZ(X)))"
                rule = msg
                check_and_print_debug_info(debug, msg)

                update_tstack_userdef(old_var[0], new_var[0],tstack, user_def_instrs)
                
                return True, [zero,zero2[0]]
            else:
                return False, []

        elif len(is_eq) == 1:
            eq = is_eq[0]

            if 1 in eq["inpt_sk"]:
                old_var = instr["outpt_sk"]
                new_var = eq["outpt_sk"]
                # instr["outpt_sk"] = eq["outpt_sk"]
                instr["outpt_sk"] = new_var
                discount_op+=1

                saved_push+=1
                gas_saved_op+=3

                msg = "EQ(1,ISZ(X))"
                rule = msg
                check_and_print_debug_info(debug, msg)

                update_tstack_userdef(old_var[0], new_var[0],tstack, user_def_instrs)
                
                return True, [eq]

            else:
                return False, []
        else:
                
            return False, []
            
    elif opcode == "LT" or opcode == "SLT":
         if 0 == instr["inpt_sk"][0] and opcode == "LT":
            out_var = instr["outpt_sk"][0]
            is_zero = list(filter(lambda x: out_var in x["inpt_sk"] and x["disasm"] == "ISZERO",user_def_instrs))
            if len(is_zero) == 1 and out_var not in tstack:
                index = user_def_instrs.index(is_zero[0])
                zero_instr = user_def_instrs[index]
                zero_instr["inpt_sk"] = [instr["inpt_sk"][1]]

                if out not in tstack:
                    discount_op+=2

                saved_push+=1
                gas_saved_op+=3

                msg = "ISZ(LT(0,X))"
                rule = msg
                check_and_print_debug_info(debug, msg)
                
                return True, []
            else:
                return False, []

         elif 1 == instr["inpt_sk"][1] and opcode == "LT":
            var = instr["inpt_sk"][0]

            new_exist = list(filter(lambda x: x["inpt_sk"] == [var] and x["disasm"] == "ISZERO", user_def_instrs))
                        
            if len(new_exist) >0:
                old_var = instr["outpt_sk"]
                new_var = new_exist[0]["outpt_sk"]
                update_tstack_userdef(old_var[0], new_var[0],tstack, user_def_instrs)
                delete = [instr]
            else:
                idx = user_def_counter.get("ISZERO",0)
                instr["id"] = "ISZERO_"+str(idx)
                instr["opcode"] = "15"
                instr["disasm"] = "ISZERO"
                instr["inpt_sk"] = [var]
                instr["commutative"] = False
                user_def_counter["ISZERO"]=idx+1
                delete = []
                
            discount_op+=1

            saved_push+=1

            msg = "LT(X,1)"
            rule = msg
            check_and_print_debug_info(debug, msg)
            return True, delete
        
         else:
            out_var = instr["outpt_sk"][0]
            is_zero = list(filter(lambda x: out_var in x["inpt_sk"] and x["disasm"] == "ISZERO",user_def_instrs))
            if len(is_zero)==1:
                zero = is_zero[0]
                zero2 = list(filter(lambda x: zero["outpt_sk"][0] in x["inpt_sk"] and x["disasm"] == "ISZERO",user_def_instrs))
                if len(zero2) == 1 and zero["outpt_sk"][0] not in tstack:
                    old_var = instr["outpt_sk"]
                    new_var = zero2[0]["outpt_sk"]
                    instr["outpt_sk"] = new_var

                    # instr["outpt_sk"] = zero2[0]["outpt_sk"]
                    discount_op+=2

                    gas_saved_op+=6

                    msg = "ISZ(ISZ("+opcode+"(X,Y)))" # It may be LT or SLT
                    rule = msg
                    check_and_print_debug_info(debug, msg)

                    update_tstack_userdef(old_var[0], new_var[0],tstack, user_def_instrs)
                    
                    return True, [zero,zero2[0]]
                else:
                    return False, []
            else:
                
                return False, []
            
    elif opcode == "EQ":
        if 0 in instr["inpt_sk"]:
            var0 = instr["inpt_sk"][0]
            var1 = instr["inpt_sk"][1]

            nonz = var1 if var0 == 0 else var0

            new_exist = list(filter(lambda x: x["inpt_sk"] == [nonz] and x["disasm"] == "ISZERO", user_def_instrs))

            if len(new_exist) >0:
                old_var = instr["outpt_sk"]
                new_var = new_exist[0]["outpt_sk"]
                update_tstack_userdef(old_var[0], new_var[0],tstack, user_def_instrs)
                delete = [instr]

            else:
                idx = user_def_counter.get("ISZERO",0)
                instr["id"] = "ISZERO_"+str(idx)
                instr["opcode"] = "15"
                instr["disasm"] = "ISZERO"
                instr["inpt_sk"] = [nonz]
                instr["commutative"] = False
                user_def_counter["ISZERO"]=idx+1
                delete = []

            

            discount_op+=1
            saved_push+=1

            msg = "EQ(0,X)"
            rule = msg
            check_and_print_debug_info(debug, msg)

            # user_def_counter["ISZERO"]=idx+1
            
            return True, delete

        else:

            out_var = instr["outpt_sk"][0]
            is_zero = list(filter(lambda x: out_var in x["inpt_sk"] and x["disasm"] == "ISZERO",user_def_instrs))
            if len(is_zero)==1:
                zero = is_zero[0]
                zero2 = list(filter(lambda x: zero["outpt_sk"][0] in x["inpt_sk"] and x["disasm"] == "ISZERO",user_def_instrs))
                if len(zero2) == 1 and zero["outpt_sk"][0] not in tstack:

                    old_var = instr["outpt_sk"]
                    new_var = zero2[0]["outpt_sk"]
                    instr["outpt_sk"] = new_var
                    # instr["outpt_sk"] = zero2[0]["outpt_sk"]
                    discount_op+=2

                    gas_saved_op+=6


                    msg = "ISZ(ISZ(EQ(X,Y)))"
                    rule = msg
                    check_and_print_debug_info(debug, msg)

                    update_tstack_userdef(old_var[0], new_var[0],tstack, user_def_instrs)
                    
                    return True, [zero,zero2[0]]
                else:
                    return False, []
            else:
                
                return False, []
            
    
    elif opcode == "AND":
        out_pt = instr["outpt_sk"][0]
        and_op = list(filter(lambda x: out_pt in x["inpt_sk"] and x["disasm"] == "AND", user_def_instrs))
        or_op = list(filter(lambda x: out_pt in x["inpt_sk"] and x["disasm"] == "OR", user_def_instrs))
        
        if len(and_op)==1:
            and_instr = and_op[0]
            if (and_instr["inpt_sk"][1] in instr["inpt_sk"]) or (and_instr["inpt_sk"][0] in instr["inpt_sk"]):
                
                old_var = instr["outpt_sk"]
                new_var = and_instr["outpt_sk"]
                instr["outpt_sk"] = new_var
                # instr["outpt_sk"] = and_instr["outpt_sk"]
                discount_op+=1

                saved_push+=1
                gas_saved_op+=3

                msg = "AND(X,AND(X,Y))"
                rule = msg
                check_and_print_debug_info(debug, msg)

                update_tstack_userdef(old_var[0], new_var[0],tstack, user_def_instrs)
                
                return True, [and_instr]
            else:
                return False, []

        elif len(or_op) == 1:
            or_instr = or_op[0]
            out_pt2 = or_instr["outpt_sk"][0]
            if out_pt == or_instr["inpt_sk"][1]: #(or(x,and(x,y)) = x, or(x,and(y,x)) = x, or(and(x,y),x) = x, or(and(y,x),x) = x
    
                if or_instr["inpt_sk"][0] == instr["inpt_sk"][0]:
                    x = instr["inpt_sk"][0]
                elif or_instr["inpt_sk"][0] == instr["inpt_sk"][1]:
                    x = instr["inpt_sk"][1]
                else:
                    return False, []
            elif out_pt == or_instr["inpt_sk"][0]:
                if or_instr["inpt_sk"][1] == instr["inpt_sk"][0]:
                    x = instr["inpt_sk"][0]
                elif or_instr["inpt_sk"][1] == instr["inpt_sk"][1]:
                    x = instr["inpt_sk"][1]
                else:
                    return False, []

            else:
                return False, []

            i = 0
                
            while (i<len(tstack)):
                if tstack[i] == (out_pt2):
                    tstack[i] = x
                i+=1
                
            for elems in user_def_instrs:
                if out_pt2 in elems["inpt_sk"]:
                    pos = elems["inpt_sk"].index(out_pt2)
                    elems["inpt_sk"][pos] = x
                    
            discount_op+=2
            gas_saved_op+=6


            msg = "OR(X,AND(X,Y))"
            rule = msg
            check_and_print_debug_info(debug, msg)
            
            return True, [or_instr]
            

        else:
            return False,[]
        
    elif opcode == "OR":
        out_pt = instr["outpt_sk"][0]
        or_op = list(filter(lambda x: out_pt in x["inpt_sk"] and x["disasm"] == "OR", user_def_instrs))
        and_op = list(filter(lambda x: out_pt in x["inpt_sk"] and x["disasm"] == "AND", user_def_instrs))
        if len(or_op)==1:
            or_instr = or_op[0]
            if (or_instr["inpt_sk"][1] in instr["inpt_sk"]) or (or_instr["inpt_sk"][0] in instr["inpt_sk"]):
                instr["outpt_sk"] = or_instr["outpt_sk"]
                discount_op+=1

                saved_push+=1
                gas_saved_op+=3

                msg = "OR(OR(X,Y),Y)"
                rule = msg
                check_and_print_debug_info(debug, msg)
                
                return True, [or_instr]
            else:
                return False, []

        elif len(and_op) == 1: 
            and_instr = and_op[0]
            out_pt2 = and_instr["outpt_sk"][0]
            if out_pt == and_instr["inpt_sk"][1]: #(and(x,or(x,y)) = x, and(x,or(y,x)) = x, and(or(x,y),x) = x, and(or(y,x),x) = x
    
                if and_instr["inpt_sk"][0] == instr["inpt_sk"][0]:
                    x = instr["inpt_sk"][0]
                elif and_instr["inpt_sk"][0] == instr["inpt_sk"][1]:
                    x = instr["inpt_sk"][1]
                else:
                    return False, []
            elif out_pt == and_instr["inpt_sk"][0]:
                if and_instr["inpt_sk"][1] == instr["inpt_sk"][0]:
                    x = instr["inpt_sk"][0]
                elif and_instr["inpt_sk"][1] == instr["inpt_sk"][1]:
                    x = instr["inpt_sk"][1]
                else:
                    return False, []

            else:
                return False, []

            i = 0
                
            while (i<len(tstack)):
                if tstack[i] == (out_pt2):
                    tstack[i] = x
                i+=1
                    
            for elems in user_def_instrs:
                if out_pt2 in elems["inpt_sk"]:
                    pos = elems["inpt_sk"].index(out_pt2)
                    elems["inpt_sk"][pos] = x
                    
            discount_op+=2
            gas_saved_op+=6

            msg = "AND(X,OR(X,Y))"
            rule = msg
            check_and_print_debug_info(debug, msg)
            
            return True, [and_instr]
            
        else:
            return False,[]


    elif opcode == "XOR":
        out_pt = instr["outpt_sk"][0]
        xor_op = list(filter(lambda x: out_pt in x["inpt_sk"] and x["disasm"] == "XOR", user_def_instrs))
        isz_op = list(filter(lambda x: out_pt in x["inpt_sk"] and x["disasm"] == "ISZERO", user_def_instrs))
        
        if len(xor_op)==1:
            xor_instr = xor_op[0]
            out_pt2 = xor_instr["outpt_sk"][0]
            if out_pt == xor_instr["inpt_sk"][1]: #xor(x,xor(x,y)) = y, xor(x,xor(y,x)) = y, xor(xor(x,y),x) = y, xor(xor(y,x),x) = y
    
                if xor_instr["inpt_sk"][0] == instr["inpt_sk"][0]:
                    y = instr["inpt_sk"][1]
                elif xor_instr["inpt_sk"][0] == instr["inpt_sk"][1]:
                    y = instr["inpt_sk"][0]
                else:
                    return False, []
            elif out_pt == xor_instr["inpt_sk"][0]:
                if xor_instr["inpt_sk"][1] == instr["inpt_sk"][0]:
                    y = instr["inpt_sk"][1]
                elif xor_instr["inpt_sk"][1] == instr["inpt_sk"][1]:
                    y = instr["inpt_sk"][0]
                else:
                    return False, []

            else:
                return False, []

            i = 0
                
            while (i<len(tstack)):
                if tstack[i] == (out_pt2):
                    tstack[i] = y
                i+=1

                    
            for elems in user_def_instrs:
                if out_pt2 in elems["inpt_sk"]:
                    pos = elems["inpt_sk"].index(out_pt2)
                    elems["inpt_sk"][pos] = y
                    
            discount_op+=2
            gas_saved_op+=6

            msg = "XOR(X,XOR(X,Y))"
            rule = msg
            check_and_print_debug_info(debug, msg)
            
            return True, [xor_instr]

        elif len(isz_op) == 1: #ISZ(XOR(X,Y)) = EQ(X,Y)
            isz_instr = isz_op[0]


            comm_inpt = [instr["inpt_sk"][1], instr["inpt_sk"][0]]
            new_exist = list(filter(lambda x: (x["inpt_sk"] == instr["inpt_sk"] or x["inpt_sk"] == comm_inpt) and x["disasm"] == "EQ", user_def_instrs))

            if len(new_exist) >0:
                old_var = isz_instr["outpt_sk"]
                new_var = new_exist[0]["outpt_sk"]
                update_tstack_userdef(old_var[0], new_var[0],tstack, user_def_instrs)
                delete = [isz_instr]

                # discount_op+=1
                # gas_saved_op+=3

                
            elif out_pt not in tstack and len(list(filter(lambda x: outpt in x["inpt_sk"] and x!= isz_instr, user_def_instrs))) == 0:
                idx = user_def_counter.get("EQ",0)
                isz_instr["inpt_sk"] = instr["inpt_sk"]
                isz_instr["id"] = "EQ_"+str(idx)
                isz_instr["opcode"] = "14"
                isz_instr["disasm"] = "EQ"
                isz_instr["commutative"] = True
                user_def_counter["EQ"]=idx+1
                delete = []
                
                discount_op+=1
                gas_saved_op+=3
                
            else:
                return False, []
            # idx = user_def_counter.get("EQ",0)            
            # instr["outpt_sk"] = isz_instr["outpt_sk"]
            # instr["id"] = "EQ_"+str(idx)
            # instr["opcode"] = "14"
            # instr["disasm"] = "EQ"
            # instr["commutative"] = True            


            # user_def_counter["EQ"]=idx+1
            rule = msg
            msg = "ISZ(XOR(X,Y))"
            check_and_print_debug_info(debug, msg)
            
            return True, delete
                
        else:
            return False,[]

        
    elif opcode == "NOT":
        out_pt = instr["outpt_sk"][0]
        not_op = list(filter(lambda x: out_pt in x["inpt_sk"] and x["disasm"] == "NOT", user_def_instrs))
        and_op = list(filter(lambda x: out_pt in x["inpt_sk"] and x["disasm"] == "AND", user_def_instrs))
        or_op = list(filter(lambda x: out_pt in x["inpt_sk"] and x["disasm"] == "NOT", user_def_instrs))

        if len(not_op)==1:
            not_instr = not_op[0]
            out_pt2 = not_instr["outpt_sk"][0]
            real_var = instr["inpt_sk"]

            i = 0
            while (i<len(tstack)):
                if tstack[i] == (out_pt2):
                    tstack[i] = real_var
                i += 1

            for elems in user_def_instrs:
                if out_pt2 in elems["inpt_sk"]:
                    pos = elems["inpt_sk"].index(out_pt2)
                    elems["inpt_sk"][pos] = real_var
                    
                discount_op+=2
                gas_saved_op+=6

                msg = "NOT(NOT(X))"
                rule = msg
                check_and_print_debug_info(debug, msg)
                
                return True, [not_instr]
            else:
                return False, []

        elif len(and_op) == 1: #and(x,not(x)) = 0
            and_instr = and_op[0]
            out_pt2 = and_instr["outpt_sk"][0]

            if instr["inpt_sk"][0] in and_instr["inpt_sk"]:
                real_var = 0
                i = 0
                while (i<len(tstack)):
                    if tstack[i] == (out_pt2):
                        tstack[i] = real_var
                    i+=1
                    
                for elems in user_def_instrs:
                    if out_pt2 in elems["inpt_sk"]:
                        pos = elems["inpt_sk"].index(out_pt2)
                        elems["inpt_sk"][pos] = real_var
                    
                discount_op+=2
                gas_saved_op+=6

                msg = "AND(X,NOT(X))"
                rule = msg
                check_and_print_debug_info(debug, msg)
                
                return True, [and_instr]

            else:
                return False, []

        elif len(or_op) == 1: #or(x,not(x)) = 2^256-1
            or_instr = or_op[0]
            out_pt2 = or_instr["outpt_sk"][0]

            if instr["inpt_sk"][0] in or_instr["inpt_sk"]:
                real_var = -1+2**256
                i = 0
                while (i<len(tstack)):
                    if tstack[i] == (out_pt2):
                        tstack[i] = real_var
                    i+=1
                    
                for elems in user_def_instrs:
                    if out_pt2 in elems["inpt_sk"]:
                        pos = elems["inpt_sk"].index(out_pt2)
                        elems["inpt_sk"][pos] = real_var
                    
                discount_op+=2
                gas_saved_op+=6

                msg = "OR(X,NOT(X))"
                rule = msg
                check_and_print_debug_info(debug, msg)
                
                return True, [or_instr]

        else:
            return False,[]


    elif opcode == "ORIGIN" or opcode == "COINBASE" or opcode == "CALLER":
        out_pt = instr["outpt_sk"][0]
        and_op = list(filter(lambda x: out_pt in x["inpt_sk"] and x["disasm"] == "AND", user_def_instrs))
        if len(and_op) == 1:
            and_instr = and_op[0]
            if -1+2**160 in and_instr["inpt_sk"]:

                old_var = instr["outpt_sk"]
                new_var = and_instr["outpt_sk"]
                instr["outpt_sk"] = new_var
                discount_op+=1

                saved_push+=1
                gas_saved_op+=3

                msg = "AND(ORIGIN,2^160-1)"
                rule = msg
                check_and_print_debug_info(debug, msg)

                update_tstack_userdef(old_var[0], new_var[0],tstack, user_def_instrs)
                
                return True,[and_instr]
            else:
                return False, []
        else:
            return False, []


    elif opcode == "SUB":
        out_pt = instr["outpt_sk"][0]
        isz_op = list(filter(lambda x: out_pt in x["inpt_sk"] and x["disasm"] == "ISZERO", user_def_instrs))
        

        if len(isz_op) == 1: #ISZ(SUB(X,Y)) = EQ(X,Y)
            isz_instr = isz_op[0]

            comm_inpt = [instr["inpt_sk"][1],instr["inpt_sk"][0]]
            
            new_exist = list(filter(lambda x: (x["inpt_sk"] == instr["inpt_sk"] or x["inpt_sk"] == comm_inpt) and x["disasm"] == "EQ", user_def_instrs))

            if len(new_exist) >0:
                old_var = isz_instr["outpt_sk"]
                new_var = new_exist[0]["outpt_sk"]
                update_tstack_userdef(old_var[0], new_var[0],tstack, user_def_instrs)
                delete = [isz_instr]

            elif out_pt not in tstack and len(list(filter(lambda x: out_pt in x["inpt_sk"] and x!=isz_instr, user_def_instrs))) == 0:
                idx = user_def_counter.get("EQ",0)
                isz_instr["inpt_sk"] = instr["inpt_sk"]
                isz_instr["id"] = "EQ_"+str(idx)
                isz_instr["opcode"] = "14"
                isz_instr["disasm"] = "EQ"
                isz_instr["commutative"] = True
                user_def_counter["EQ"]=idx+1
                delete = []

                discount_op+=1
                gas_saved_op+=3

            else:
                return False, []
            # old_var = instr["outpt_sk"]
            # new_var = isz_instr["outpt_sk"]
            # instr["outpt_sk"] = new_var
            
            # # instr["outpt_sk"] = isz_instr["outpt_sk"]
            # instr["id"] = "EQ_"+str(idx)
            # instr["opcode"] = "14"
            # instr["disasm"] = "EQ"
            # instr["commutative"] = True            



            msg = "ISZ(SUB(X,Y))"
            rule = msg
            check_and_print_debug_info(debug, msg)

            # update_tstack_userdef(old_var[0], new_var[0],tstack, user_def_instrs)
            
            return True, delete
                
        else:
            return False,[]

    elif opcode == "SHL":
        out_pt = instr["outpt_sk"][0]
        mul_op = list(filter(lambda x: out_pt in x["inpt_sk"] and x["disasm"] == "MUL", user_def_instrs))
        div_op = list(filter(lambda x: out_pt in x["inpt_sk"] and x["disasm"] == "DIV", user_def_instrs))
        and_op = list(filter(lambda x: out_pt in x["inpt_sk"] and x["disasm"] == "AND", user_def_instrs))
        if len(mul_op) == 1 and instr["inpt_sk"][1] == 1:
            mul_instr = mul_op[0]

            if mul_instr["inpt_sk"][1] == out_pt:
                new_input = [instr["inpt_sk"][0],mul_instr["inpt_sk"][0]]
                new_exist = list(filter(lambda x: x["inpt_sk"] == new_input and x["disasm"] == "SHL", user_def_instrs))

                if len(new_exist) > 0:
                    old_var = mul_instr["outpt_sk"]
                    new_var = new_exist[0]["outpr_sk"]
                    update_tstack_userdef(old_var[0], new_var[0],tstack, user_def_instrs)
                    delete = [mul_instr]

                else:
                    mul_instr["inpt_sk"] = new_input
                                        
                    idx = user_def_counter.get("SHL",0)
                    mul_instr["id"] = "SHL_"+str(idx)
                    mul_instr["opcode"] = "1b"
                    mul_instr["disasm"] = "SHL"
                    mul_instr["commutative"] = False            
                    user_def_counter["SHL"]=idx+1
                    delete = []
                    
                # old_var = instr["outpt_sk"]
                # new_var = mul_instr["outpt_sk"]
                # instr["outpt_sk"] = new_var
                # instr["inpt_sk"][1] = mul_instr["inpt_sk"][0]

                discount_op+=1
                gas_saved_op+=5
                saved_push+=1

                msg = "MUL(X,SHL(Y,1)"
                rule = msg
                check_and_print_debug_info(debug, msg)

                # update_tstack_userdef(old_var[0], new_var[0],tstack, user_def_instrs)
                
                return True, delete

            elif mul_instr["inpt_sk"][0] == out_pt:
                new_input = [instr["inpt_sk"][0],mul_instr["inpt_sk"][1]]
                new_exist = list(filter(lambda x: x["inpt_sk"] == new_input and x["disasm"] == "SHL", user_def_instrs))

                if len(new_exist) > 0:
                    old_var = mul_instr["outpt_sk"]
                    new_var = new_exist[0]["outpr_sk"]
                    update_tstack_userdef(old_var[0], new_var[0],tstack, user_def_instrs)
                    delete = [mul_instr]

                else:
                    mul_instr["inpt_sk"] = new_input
                                        
                    idx = user_def_counter.get("SHL",0)
                    mul_instr["id"] = "SHL_"+str(idx)
                    mul_instr["opcode"] = "1b"
                    mul_instr["disasm"] = "SHL"
                    mul_instr["commutative"] = False            
                    user_def_counter["SHL"]=idx+1
                    delete = []

                # instr["outpt_sk"] = mul_instr["outpt_sk"]
                # old_var = instr["outpt_sk"]
                # new_var = mul_instr["outpt_sk"]
                # instr["outpt_sk"] = new_var
                # instr["inpt_sk"][1] = mul_instr["inpt_sk"][1]

                discount_op+=1
                gas_saved_op+=5
                saved_push+=1

                msg = "MUL(SHL(X,1),Y)"
                rule = msg
                check_and_print_debug_info(debug, msg)

                # update_tstack_userdef(old_var[0], new_var[0],tstack, user_def_instrs)
                
                return True, delete

            else:
                return False, []

        elif len(div_op) == 1 and instr["inpt_sk"][1] == 1:
            div_instr = div_op[0]

            if div_instr["inpt_sk"][1] == out_pt:
                new_input = [instr["inpt_sk"][0], div_instr["inpt_sk"][0]]
                new_exist = list(filter(lambda x: x["inpt_sk"] == new_input and x["disasm"] == "SHR", user_def_instrs))

                if len(new_exist) > 0:
                    old_var = div_instr["outpt_sk"]
                    new_var = new_exist[0]["outpt_sk"]
                    update_tstack_userdef(old_var[0], new_var[0],tstack, user_def_instrs)
                    delete = [div_instr]
                else:
                    div_instr["inpt_sk"] = new_input
                    
                    idx = user_def_counter.get("SHR",0)
                    div_instr["id"] = "SHR_"+str(idx)
                    div_instr["opcode"] = "1c"
                    div_instr["disasm"] = "SHR"
                    div_instr["commutative"] = False            
                    user_def_counter["SHR"]=idx+1
                    delete = []
                    
                # old_var = instr["outpt_sk"]
                # new_var = div_instr["outpt_sk"]
                # instr["outpt_sk"] = new_var
                # # instr["outpt_sk"] = div_instr["outpt_sk"]
                # instr["inpt_sk"][1] = div_instr["inpt_sk"][0]

                # idx = user_def_counter.get("SHR",0)
            
                # instr["id"] = "SHR_"+str(idx)
                # instr["opcode"] = "1c"
                # instr["disasm"] = "SHR"
                # instr["commutative"] = False            
                
                
                discount_op+=1
                gas_saved_op+=5
                saved_push+=1

                # user_def_counter["SHR"]=idx+1
                msg = "DIV(X,SHL(Y,1))"
                rule = msg
                check_and_print_debug_info(debug, msg)

                # update_tstack_userdef(old_var[0], new_var[0],tstack, user_def_instrs)
                
                return True, delete

        elif len(and_op) > 0: #AND(SHL(X,Y), SHL(X,Z)) => SHL(X,AND(Y,Z))

            found = False
            i = 0
            while i < len(and_op) and not found:
                
                and_ins = and_op[i]
                if out_pt == and_ins["inpt_sk"][0]:
                    out_pt1 = and_ins["inpt_sk"][1]
                else:
                    out_pt1 = and_ins["inpt_sk"][0]

                new_ins = list(filter(lambda x: out_pt1 in x["outpt_sk"] and x["disasm"] == "SHL" and x["inpt_sk"][0] == instr["inpt_sk"][0],user_def_instrs))
                if len(new_ins) == 1:
                    shl1 = new_ins[0]
                    found = True

                i+=1

            #if the shl instructions are not used by any other operation or do not appear in the target stack, then I can simplify them
            if found and out_pt not in tstack and out_pt1 not in tstack and len(list(filter(lambda x: out_pt in x["inpt_sk"] and x!= and_ins, user_def_instrs))) == 0 and len(list(filter(lambda x: out_pt1 in x["inpt_sk"] and x!= and_ins, user_def_instrs))) == 0:

                inpt1 = instr["inpt_sk"][0]
                inpt2 = instr["inpt_sk"][1]
                inpt3 = shl1["inpt_sk"][1]
                
                new_and_idx = user_def_counter.get("AND",0)

                instr["inpt_sk"] = [inpt2,inpt3]
                instr["id"] = "AND_"+str(new_and_idx)
                instr["opcode"] = "16"
                instr["disasm"] = "AND"
                instr["commutative"] = True
                user_def_counter["AND"]=new_and_idx+1

                new_shl_idx = user_def_counter.get("SHL",0)
                
                and_ins["inpt_sk"] = [inpt1,instr["outpt_sk"][0]]
                and_ins["id"] = "SHL_"+str(new_shl_idx)
                and_ins["opcode"] = "1b"
                and_ins["disasm"] = "SHL"
                and_ins["commutative"] = False
                user_def_counter["SHL"]=new_shl_idx+1

                delete = [shl1]
                
                discount_op+=1
                gas_saved_op+=3

                return True, delete
            else:
                return False, []
        else:
            return False, []

    elif opcode == "ADDRESS":
        out_pt = instr["outpt_sk"][0]
        bal_op = list(filter(lambda x: out_pt in x["inpt_sk"] and x["disasm"] == "BALANCE", user_def_instrs))

        and_op = list(filter(lambda x: out_pt in x["inpt_sk"] and x["disasm"] == "AND", user_def_instrs))

        if len(bal_op) == 1:
            bal_instr = bal_op[0]

            new_exist = list(filter(lambda x: x["disasm"] == "SELFBALANCE", user_def_instrs))

            if len(new_exist) > 0:
                    old_var = bal_instr["outpt_sk"]
                    new_var = new_exist[0]["outpt_sk"]
                    update_tstack_userdef(old_var[0], new_var[0],tstack, user_def_instrs)
                    delete = [bal_instr]
            else:
                bal_instr["inpt_sk"] = []
                    
                idx = user_def_counter.get("SELFBALANCE",0)
                bal_instr["id"] = "SELFBALANCE_"+str(idx)
                bal_instr["opcode"] = "47"
                bal_instr["disasm"] = "SELFBALANCE"
                bal_instr["commutative"] = False            
                user_def_counter["SELFBALANCE"]=idx+1
                delete = []

            
            # old_var = instr["outpt_sk"]
            # new_var = bal_instr["outpt_sk"]
            # instr["outpt_sk"] = new_var
            
            # instr["outpt_sk"] = bal_instr["outpt_sk"]

            # idx = user_def_counter.get("SELFBALANCE",0)
            
            # instr["id"] = "SELFBALANCE_"+str(idx)
            # instr["opcode"] = "47"
            # instr["disasm"] = "SELFBALANCE"
            # instr["commutative"] = False            
                
            discount_op+=1
            gas_saved_op+=397 #BALANCE 400 ADDRESS 2 SELFBALANCE 5

            # user_def_counter["SELFBALANCE"]=idx+1
            msg = "BALANCE(ADDRESS)"
            rule = msg
            check_and_print_debug_info(debug, msg)

            # update_tstack_userdef(old_var[0], new_var[0],tstack, user_def_instrs)
            
            return True, delete
        
        elif len(and_op) == 1:
            and_instr = and_op[0]
            if -1+2**160 in and_instr["inpt_sk"]:
                # instr["outpt_sk"] = and_instr["outpt_sk"]
                old_var = instr["outpt_sk"]
                new_var = and_instr["outpt_sk"]
                instr["outpt_sk"] = new_var

                discount_op+=1

                saved_push+=1
                gas_saved_op+=3

                msg = "AND(ADDRESS,2^160)"
                rule = msg
                check_and_print_debug_info(debug, msg)

                update_tstack_userdef(old_var[0], new_var[0],tstack, user_def_instrs)
                
                return True,[and_instr]
            else:
                return False, []
        else:
            return False, []
        
    elif opcode == "EXP":
        if instr["inpt_sk"][0] == 0:
            instr["inpt_sk"].pop(0)

            new_exist = list(filter(lambda x: x["inpt_sk"] == instr["inpt_sk"] and x["disasm"] == "ISZERO", user_def_instrs))

            if len(new_exist) > 0:
                old_var = instr["outpt_sk"]
                new_var = new_exist[0]["outpt_sk"]
                update_tstack_userdef(old_var[0], new_var[0],tstack, user_def_instrs)
                delete = [instr]
            else:
                idx = user_def_counter.get("ISZERO",0)
            
                instr["id"] = "ISZERO_"+str(idx)
                instr["opcode"] = "15"
                instr["disasm"] = "ISZERO"
                instr["commutative"] = False            
                user_def_counter["ISZERO"]=idx+1
                delete = []
                
            saved_push+=1
            gas_saved_op+=57


            msg = "EXP(0,X)"
            rule = msg
            check_and_print_debug_info(debug, msg)
            
            return True, delete

        elif instr["inpt_sk"][0] == 2:
            instr["inpt_sk"].pop(0)

            new_input = [instr["inpt_sk"][0],1]
            new_exist = list(filter(lambda x: x["inpt_sk"] == new_input and x["disasm"] == "SHL", user_def_instrs))

            if len(new_exist) > 0:
                old_var = instr["outpt_sk"]
                new_var = new_exist[0]["outpt_sk"]
                update_tstack_userdef(old_var[0], new_var[0],tstack, user_def_instrs)
                delete = [instr]
            else:
                idx = user_def_counter.get("SHL",0)
                instr["inpt_sk"] = new_input
                instr["id"] = "SHL_"+str(idx)
                instr["opcode"] = "1b"
                instr["disasm"] = "SHL"
                instr["commutative"] = False            
                user_def_counter["SHL"]=idx+1
                delete = []
            
            
            
            # instr["inpt_sk"].append(1)
            # idx = user_def_counter.get("SHL",0)
            
            # instr["id"] = "SHL_"+str(idx)
            # instr["opcode"] = "1b"
            # instr["disasm"] = "SHL"
            # instr["commutative"] = False            
                
            gas_saved_op+=57 #EXP-SHL

            # user_def_counter["SHL"]=idx+1
            msg = "EXP(2,X)"
            rule = msg
            check_and_print_debug_info(debug, msg)

            return True, delete

        else:
            return False, []

    else:
        return False, []


    
def apply_all_comparison(user_def_instrs,tstack):
    global rule_applied

    modified = True
    while(modified):
        msg = "********************IT*********************"
        check_and_print_debug_info(debug, msg)
        modified = apply_comparation_rules(user_def_instrs,tstack)
        if modified:
            rule_applied = True
        
def apply_comparation_rules(user_def_instrs,tstack):
    global rules_applied
    global rule
    
    modified = False

    for instr in user_def_instrs:
        
        r, d_instr = apply_cond_transformation(instr,user_def_instrs,tstack)

        if r:
            
            rules_applied.append(rule)
            rule = ""
            msg = "[RULE]: Simplification rule type 2: "+str(instr)
            msg = msg+"\n[RULE]: Delete rules: "+str(d_instr)
            check_and_print_debug_info(debug, msg)

            modified = True
            for b in d_instr:
                idx = user_def_instrs.index(b)
                user_def_instrs.pop(idx)
    return modified
                   
def update_tstack_userdef(old_var, new_var,tstack, user_def_instrs):
    i = 0
    while(i<len(tstack)):
        if tstack[i] == old_var:
            tstack[i] = new_var
        i+=1

    for instr in user_def_instrs:
        inp_st = instr["inpt_sk"]
        if old_var in inp_st:
            i = inp_st.index(old_var)
            instr["inpt_sk"][i] = new_var
            
def get_sfs_dict():
    return sfs_contracts

def is_identity_map(source_stack,target_stack,instructions):

    if len(user_defins) > 0:
        return False
    
    if len(source_stack) != len(target_stack):
        return False

    
    for v in variable_content:
        if v != variable_content[v]:
            return False

    storage_ins = list(filter(lambda x: x.find("mstore")!=-1 or x.find("sstore")!=-1,instructions))

    if len(storage_ins)>0:
        return False
        
    return True


def get_idx_in_instructions(idx_in_seq, location = "memory"):
    if location == "memory":
        for i in extra_dep_info["mem_deps_int2ins"]:
            if idx_in_seq in extra_dep_info["mem_deps_int2ins"][i]:
                return i
    elif location == "storage":
        for i in extra_dep_info["sto_deps_int2ins"]:
            if idx_in_seq in extra_dep_info["sto_deps_int2ins"][i]:
                return i
    else:
        raise Exception("Unknown location")
    
    return -1

def remove_extra_deps_info(idx_in_seq, location = "memory"):
    global extra_dep_info

    idx = get_idx_in_instructions(idx_in_seq, location)

    if idx != -1 and location == "memory":
        extra_dep_info["memory_deps_eqs"] = list(filter(lambda x: x.get_first()!=idx and x.get_second()!= idx,extra_dep_info["memory_deps_eqs"]))
        extra_dep_info["memory_deps_noneqs"] = list(filter(lambda x: x.get_first()!=idx and x.get_second()!= idx,extra_dep_info["memory_deps_noneqs"]))
        extra_dep_info["mem_deps_int2ins"].pop(idx) 

        for x in extra_dep_info["memory_deps_eqs"]:
            if x.get_first() > idx:
                x.set_first(x.get_first()-1)
            if x.get_second() > idx:
                x.set_second(x.get_second()-1)

        for x in extra_dep_info["memory_deps_noneqs"]:
            if x.get_first() > idx:
                x.set_first(x.get_first()-1)
            if x.get_second() > idx:
                x.set_second(x.get_second()-1)

        for i in extra_dep_info["mem_deps_int2ins"]:
            if extra_dep_info["mem_deps_int2ins"][i][1]>idx_in_seq:
                extra_dep_info["mem_deps_int2ins"][i] = (extra_dep_info["mem_deps_int2ins"][i][0],extra_dep_info["mem_deps_int2ins"][i][1]-1)

    elif idx != -1 and location == "storage":
        extra_dep_info["storage_deps_eqs"] = list(filter(lambda x: x.get_first()!=idx and x.get_second()!= idx,extra_dep_info["storage_deps_eqs"]))
        extra_dep_info["storage_deps_noneqs"] = list(filter(lambda x: x.get_first()!=idx and x.get_second()!= idx,extra_dep_info["storage_deps_noneqs"]))
        extra_dep_info["sto_deps_int2ins"].pop(idx) 

        for x in extra_dep_info["storage_deps_eqs"]:
            if x.get_first() > idx:
                x.set_first(x.get_first()-1)
            if x.get_second() > idx:
                x.set_second(x.get_second()-1)

        for x in extra_dep_info["storage_deps_noneqs"]:
            if x.get_first() > idx:
                x.set_first(x.get_first()-1)
            if x.get_second() > idx:
                x.set_second(x.get_second()-1)

        for i in extra_dep_info["sto_deps_int2ins"]:
            if extra_dep_info["sto_deps_int2ins"][i][1]>idx_in_seq:
                extra_dep_info["sto_deps_int2ins"][i] = (extra_dep_info["sto_deps_int2ins"][i][0],extra_dep_info["sto_deps_int2ins"][i][1]-1)
            
def remove_loads(storage,instruction):
    new_storage = []
    for i in range(0,len(storage)):
        s = storage[i]
        if s[0][-1].find(instruction)!=-1:
            if s in list(u_dict.values()) :
                new_storage.append(s)
            else:
                if instruction == "mload" and extra_dep_info != {}: #in order to distinguish with the case of sload
                    remove_extra_deps_info(i,"memory")
                elif instruction == "sload" and extra_dep_info != {}:
                    remove_extra_deps_info(i, "storage")
        else:
            new_storage.append(s)
    return new_storage

# It removes from storage_order or memory_order the loads instructions
# that are not used neither in the target stack nor the storage
# operations
def remove_loads_instructions():
    global storage_order
    global memory_order

    target_stack_content = variable_content.values()

    sstore_instructions = filter(lambda x: x[0][-1].find("sstore")!=-1,storage_order)
    sstore_vars = list(map(lambda x: x[0][0],sstore_instructions))
    
    mstore_instructions = filter(lambda x: x[0][-1].find("mstore")!=-1,memory_order)
    mstore_vars = list(map(lambda x: x[0][0],mstore_instructions))
                
    storage_order = remove_loads(storage_order,"sload")
    memory_order = remove_loads(memory_order,"mload")



#Here it means that we have sloads between the sstores that are equals.
#Otherwise it would have been removed with remove_store_recursive_dif
def replace_loads_by_sstores(storage_location, complementary_location, location):
    global u_dict
    global variable_content
    global gas_store_op
    global gas_memory_op
    global discount_op
    global rule_applied
    global rules_applied
    
    if location == "storage":
        store_ins = "sstore"
        load_ins = "sload"
    else:
        store_ins = "mstore"
        load_ins = "mload"

    i = 0
    finish = False
    while(i<len(storage_location) and not finish):
        elem = storage_location[i]

        if elem[0][-1].find(store_ins) !=-1:
            var = elem[0][0]
            value = elem[0][1]
            l_ins = list(filter(lambda x: x[0][0] == var and x[0][-1].find(load_ins)!=-1,storage_location[i+1::]))
            if len(l_ins)>0:
                load = l_ins[0]
                pos = storage_location[i+1::].index(load)
                rest_list = storage_location[i+1:i+pos+1]
                dep = []
                for j in range(len(rest_list)):
                    dep.append(are_dependent(elem, rest_list[j],i,j+i+1, location))
                # dep = list(map(lambda x: are_dependent(elem,x),rest_list))

                if True in dep and elem[0][-1].find("mstore8") == -1:
                    j = 0
                    while(j<len(dep)):
                        if dep[j] and rest_list[j][0][-1].find("keccak")!=-1:
                            dep[j] = False
                        j+=1
                        
                if True not in dep and elem[0][-1].find("mstore8") == -1: #it does not work for mstore8
                    if location == "storage":
                        msg = "[OPT]: Replaced sload by its value"
                        check_and_print_debug_info(debug, msg)

                        gas_store_op+=700
                    else:
                        msg = "[OPT]: Replaced mload by its value"
                        check_and_print_debug_info(debug, msg)

                        gas_memory_op+=3
                    storage_location.pop(i+pos+1)
                    if extra_dep_info != {}:
                        remove_extra_deps_info(i+pos+1, location)
                    # discount_op+=1  @It may be replace by a DUP+SWAP
                    finish = True

                    rule_applied = True
                    rules_applied.append(str(load)+"= "+str(elem[0]))
                    
                    for v in u_dict:
                        elem = u_dict[v]
                        if elem == load:
                            var2replace = v

                    for v in u_dict:
                        elem = u_dict[v]
                        list_tuple = list(elem[0])
                        if var2replace in list_tuple:
                            pos = elem[0].index(var2replace)
                            list_tuple[pos] = value
                            u_dict[v] = (tuple(list_tuple),elem[1])
    
                    for var in variable_content:
                        if variable_content[var] == var2replace:
                            variable_content[var] = value

                    for i in range(0,len(storage_location)):
                        elem = storage_location[i]
                        list_tuple = list(elem[0])
                        if var2replace in list_tuple:
                            pos = list_tuple.index(var2replace)
                            list_tuple[pos] = value
                            storage_location[i] = (tuple(list_tuple),elem[1])

                    for i in range(0,len(complementary_location)):
                        elem = complementary_location[i]
                        list_tuple = list(elem[0])
                        if var2replace in list_tuple:
                            pos = list_tuple.index(var2replace)
                            list_tuple[pos] = value
                            complementary_location[i] = (tuple(list_tuple),elem[1])

                    del u_dict[var2replace]

                    replace_loads_by_sstores(storage_location, complementary_location,location)
        i+=1

    
def remove_store_recursive_dif(storage_location, location):
    global gas_store_op
    global gas_memory_op
    global discount_op
    global rule_applied
    global rules_applied
    
    if location == "storage":
        instruction = "sstore"
    else:
        instruction = "mstore"

    i = 0
    finish = False

    while(i<len(storage_location) and not finish):
        elem = storage_location[i]
        
        if elem[0][-1].find(instruction)!=-1:
            var = elem[0][0]
            rest = list(filter(lambda x: x[0][0] == var and x[0][-1].find(instruction)!=-1 and x[0][-1] == elem[0][-1], storage_location[i+1::]))
            # # If instruction is mstore and the next one is mstore8, then i cannot remove any of them. Otherwise, it is
            # # possible if both instructions are dependent
            # rest = list(filter(lambda x: x[0][-1].find(instruction)!=-1 and (elem[0][-1] != "mstore" or x[0][-1] != "mstore8") and
            #                              are_dependent(x[0][0],var,x[0][-1],elem[0][-1]), storage_location[i+1::]))
            if rest !=[]:
                next_ins = rest[0]
                pos = storage_location[i+1::].index(next_ins)
                sublist = storage_location[i+1:pos+i+1]

                dep = []
                for j in range(len(sublist)):
                    dep.append(are_dependent(elem, sublist[j],i,j+i+1, location))
                # dep = list(map(lambda x: are_dependent(elem, x),sublist)) #It checks for loads and and keccaks betweeen the stores

                #Keccaks are considered in dep list
                if True not in dep:
                    storage_location.pop(i)
                    if extra_dep_info != {}:
                        remove_extra_deps_info(i, location)
                    discount_op+=1
                    if location == "storage":
                        msg = "[OPT]: Removed sstore sstore "
                        check_and_print_debug_info(debug, msg)

                        gas_store_op+=5000
                    else:
                        msg = "[OPT]: Removed mstore mstore "
                        check_and_print_debug_info(debug, msg)

                        gas_memory_op+=3

                    rule_applied = True
                    rules_applied.append(str(elem[0])+" useless")
                    
                    remove_store_recursive_dif(storage_location,location)
                    finish = True

                elif True in dep and next_ins == elem and location == "memory": #It may happend that two mstores can be optimized though a keccak is between them. mstore(x,y) keccak(x,z), mstore(x,y)
                    #All trues have to correspond to keccaks
                    j = 0
                    all_keccaks = True
                    while(j < len(sublist) and all_keccaks):
                        ins = sublist[j]
                        if dep[j]:
                            if ins[0][-1].find("keccak256")==-1:
                                all_keccaks = False
                        j+=1
                        
                    if all_keccaks:
                        rules_applied.append(str(storage_location[i+pos+1])+" useless")

                        storage_location.pop(i+pos+1)
                        if extra_dep_info != {}:
                            remove_extra_deps_info(i+pos+1, location)
                        discount_op+=1
                        msg = "[OPT]: Removed mstore mstore with KECCAK"
                        check_and_print_debug_info(debug, msg)
                        gas_memory_op+=3

                        rule_applied = True

                        
                        remove_store_recursive_dif(storage_location,location)
                        finish = True

                else: #True in list. If we have dependences, we an delete them if all are stores. mstore(x,y) mstore(z,w) mstore(x,k)
                        j = 0
                        all_mstores = True
                        while(j<len(sublist) and all_mstores):
                            ins = sublist[j]
                            if dep[j]:
                                if ins[0][-1].find(elem[0][-1])==-1:
                                    all_mstores = False
                            j+=1

                        if all_mstores:
                            storage_location.pop(i)
                            if extra_dep_info != {}:
                                remove_extra_deps_info(i, location)
                            discount_op+=1
                            if location == "storage":
                                msg = "[OPT]: Removed sstore sstore "
                                check_and_print_debug_info(debug, msg)

                                gas_store_op+=5000
                            else:
                                msg = "[OPT]: Removed mstore mstore "
                                check_and_print_debug_info(debug, msg)

                                gas_memory_op+=3
                               
                            rule_applied = True
                            rules_applied.append(str(elem[0])+" useless")
                            
                            remove_store_recursive_dif(storage_location,location)
                            finish = True
                    
        i+=1


#It removes things of the type sstore(4,sload(4))
def remove_store_loads(storage_location, location):
    global gas_store_op
    global gas_memory_op
    global discount_op
    global rule_applied
    global rules_applied
    
    if storage_location == "storage":
        store_ins = "sstore"
        load_ins = "sload"
    else:
        store_ins = "mstore"
        load_ins = "mload"

    i = 0
    finished = False
    while(i<len(storage_location) and not finished):
        elem = storage_location[i]
        if elem[0][-1].find(store_ins)!=-1:
            var = elem[0][0]
            value = elem[0][1]
            if value in u_dict:
                symb_ins = u_dict[value]
                if symb_ins[0][-1].find(load_ins)!=-1 and symb_ins[0][0] == var:
                    pos = storage_location.index(symb_ins)
                    # rest_instructions = storage_location[i+1:pos]
                    rest_instructions = storage_location[pos+1:i]

                    variables = []
                    for j in range(len(rest_instructions)):
                        variables.append(are_dependent(elem,rest_instructions[j],i,j+pos+1, location))
                    # variables = list(map(lambda x: are_dependent(elem,x),rest_instructions))

                    
                    #Keccaks are considered in the previous list
                    if True not in variables:
                        storage_location.pop(i)
                        if extra_dep_info != {}:
                            remove_extra_deps_info(i, location)
                        discount_op+=1
                        finished = True

                        if storage_location == "storage":
                            msg = "[OPT]: OPTIMIZATION sstore OF sload"
                            check_and_print_debug_info(debug, msg)

                            gas_store_op+=5000
                        else:
                            msg = "[OPT]: OPTIMIZATION mstore OF mload"
                            check_and_print_debug_info(debug, msg)

                            gas_memory_op+=3

                        rule_applied = True
                        rules_applied.append(str(elem[0])+" of mload")

                        
                        remove_store_loads(storage_location,location)
        i+=1




def simplify_memory(storage_location, complementary_location, location):
    global memory_opt
    global storage_opt
    global mem_delete_pos
    global sto_delete_pos

    del_pos = []
    old_storage_location = list(storage_location)
    
    replace_loads_by_sstores(storage_location, complementary_location, location)
    
    if old_storage_location != storage_location:
        old_storage_location = list(filter(lambda x: type(x)==tuple, old_storage_location))
        storage_location1 = list(filter(lambda x: type(x)==tuple, storage_location))
        pos = compute_delete_positions(old_storage_location, storage_location1)
        
        del_pos+=pos
        if location == "storage":
            storage_opt[0] = True
        else:
            memory_opt[0] = True

    old_storage_location2 = list(storage_location)
    remove_store_recursive_dif(storage_location,location)

    
    
    if old_storage_location2 != storage_location:

        old_storage_location2 = list(filter(lambda x: type(x)==tuple, old_storage_location2))
        storage_location2 = list(filter(lambda x: type(x)==tuple, storage_location))
        pos = compute_delete_positions(old_storage_location2, storage_location2)
        del_pos+=pos

        
        if location == "storage":
            storage_opt[1] = True
        else:
            memory_opt[1] = True

    
    old_storage_location3 = list(storage_location)
    remove_store_loads(storage_location,location)

    if old_storage_location3 != storage_location:

        old_storage_location3 = list(filter(lambda x: type(x)==tuple, old_storage_location3))
        storage_location3 = list(filter(lambda x: type(x)==tuple, storage_location))
        pos = compute_delete_positions(old_storage_location3, storage_location3)
        del_pos+=pos
        
        if location == "storage":
            storage_opt[2] = True
        else:
            memory_opt[2] = True


    if location == "storage":
        sto_delete_pos = del_pos
    else:
        mem_delete_pos = del_pos

        
    if storage_location != old_storage_location:
        return True
    else:
        return False



def are_dependent_variables(v1,v2):
    # print("AREDEPENDENTVARIABLES")
    # print(v1)
    # print(v2)
    # print(u_dict)
    # print(u_dict[v1][0])
    # print(u_dict[v2][0])

    exp_v1 = (v1) if v1 not in u_dict.keys() else u_dict[v1][0]
    exp_v2 = (v2) if v2 not in u_dict.keys() else u_dict[v2][0]

    if v1 == v2:
        return False

    if is_integer(v1)!=-1 and is_integer(v2)!=-1:
        return False

    if is_integer(v1)!=-1 or is_integer(v2)!=-1:
        return True

    if v2 in exp_v1:
        return True

    if v1 in exp_v2:
        return True

    for v in exp_v1:
        if v in exp_v2:
            return True
    
    return False

    
    
#storage location may be storage_order or memory_order
def generate_dependences(storage_location, location):
    storage_dependences = []

    if location == "storage":
        instruction = "sstore"
        load_instruction = "sload"
    else:
        instruction = "mstore"
        load_instruction = "mload"

    for i in range(len(storage_location)-1,-1,-1):
        elem = storage_location[i]
        var = elem[0][0]
        
        if elem[0][-1].find(instruction)!=-1:
            predecessor = storage_location[:i]
            j = len(predecessor)-1
            already = False
            # while((j>=0) and not already):
            while(j>=0):
                store = predecessor[j]
                if store[0][-1].find(instruction)!=-1:
                    var_rest = store[0][0]
                    # print("ARE DEPENDENT")
                    # print(elem)
                    # print(store)
                    # print(i)
                    # print(j)
                    # raise Exception
                    dep = are_dependent(elem,store,i,j, location)
                    # dep = are_dependent(elem,store)
                    if dep:
                        if elem[0][1] != store[0][1]: #if the value is the same they are not dependent
                            storage_dependences.append((j,i))
                            already = True
                        else:
                            # print(elem)
                            # print(store)
                            # print(are_dependent_variables(elem[0][0],store[0][0]))
                            if are_dependent_variables(elem[0][0],store[0][0]): #if they stored the same value but on index depends on the other
                            # store[0][0] in u_dict[elem[0][0]][0]:

                                storage_dependences.append((j,i))
                                already = True
                                
                            if str(var) == str(var_rest) and location == "memory":
                                storage_dependences.append((j,i))
                                already = True

                                
                j-=1

        elif elem[0][-1].find("keccak")!=-1:
            predecessor = storage_location[:i]

            j = len(predecessor)-1
            while(j>=0):
                store = predecessor[j]
                if store[0][-1].find(instruction)!=-1:
                    var_rest = store[0][0]
                    dep = are_dependent(store,elem,j,i, location)
                    # dep = are_dependent(store,elem)
                    if dep:
                        storage_dependences.append((j,i))                                
                j-=1

            j = 0
            successor = storage_location[i+1:]
            while(j<len(successor)):
                store = successor[j]
                if store[0][-1].find(instruction)!=-1:
                    var_rest = store[0][0]
                    dep = are_dependent(elem,store,i,i+1+j, location)
                    # dep = are_dependent(elem,store)
                    if dep:
                        storage_dependences.append((i,i+j+1))

                j+=1                                

                
            
        else: #loads
            predecessor = storage_location[:i]
            successor = storage_location[i+1:]

            #pre
            j = len(predecessor)-1
            already = False
            while((j>=0)):
                store = predecessor[j]
                if store[0][-1].find(instruction)!=-1:
                    var_rest = store[0][0]
                    # print(elem)
                    # print(store)
                    # print(i)
                    # print(j)
                    dep = are_dependent(elem, store,i,j, location)
                    # dep = are_dependent(elem,store)
                    if dep:
                        if elem[0][1] != store[0][1]: #if the value is the same they are not dependent
                            storage_dependences.append((j,i))
                            already = True
                        else:
                            if str(var) == str(var_rest) and location == "memory":
                                storage_dependences.append((j,i))
                                already = True
                j-=1

            j = 0
            already = False
            while(j<len(successor)):
                store = successor[j]
                if store[0][-1].find(instruction)!=-1:
                    var_rest = store[0][0]
                    dep = are_dependent(elem,store,i,i+1+j, location)
                    # dep = are_dependent(elem,store)
                    if dep:
                        if elem[0][1] != store[0][1]: #if the value is the same they are not dependent
                            storage_dependences.append((i,i+j+1))
                            already = True
                        else:
                            if str(var) == str(var_rest) and location == "memory":
                                storage_dependences.append((i,i+j+1))
                                already = True
                j+=1                                
            
    return storage_dependences

def simplify_dependencies(deps: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    dg = nx.DiGraph(deps)
    tr = nx.transitive_reduction(dg)
    return list(tr.edges)


def update_variables_loads(elem1, elem2, storage_location, location):
    global variable_content
    global storage_order
    global memory_order
    global u_dict


    for v in u_dict:
        elem = u_dict[v]
        if elem == elem1:
            var2keep = v
        if elem == elem2:
            var2replace = v
            
    #We remove the second sload
    u_dict.pop(var2replace)

    for v in u_dict:
        elem = u_dict[v]
        list_tuple = list(elem[0])
        if var2replace in list_tuple:
            pos = elem[0].index(var2replace)
            list_tuple[pos] = var2keep
            u_dict[v] = (tuple(list_tuple),elem[1])
    
    for var in variable_content:
        if variable_content[var] == var2replace:
            variable_content[var] = var2keep

    for i in range(0,len(storage_location)):
        elem = storage_location[i]
        list_tuple = list(elem[0])
        if var2replace in list_tuple:
            pos = list_tuple.index(var2replace)
            list_tuple[pos] = var2keep
            storage_location[i] = (tuple(list_tuple),elem[1])


    if location == "storage":
        complement_order = memory_order
    else:
        complement_order = storage_order

    for i in range(0,len(complement_order)):
        elem = complement_order[i]
        list_tuple = list(elem[0])
        if var2replace in list_tuple:
            pos = list_tuple.index(var2replace)
            list_tuple[pos] = var2keep
            complement_order[i] = (tuple(list_tuple),elem[1])

        

            
            

def update_variables_keccaks(elem1, elem2, storage_location, storage_order):
    global variable_content
    global u_dict


    for v in u_dict:
        elem = u_dict[v]
        if elem == elem1:
            var2keep = v
        if elem == elem2:
            var2replace = v
            
    #We remove the second sload
    u_dict.pop(var2replace)

    for v in u_dict:
        elem = u_dict[v]
        list_tuple = list(elem[0])
        if var2replace in list_tuple:
            pos = elem[0].index(var2replace)
            list_tuple[pos] = var2keep
            u_dict[v] = (tuple(list_tuple),elem[1])
    
    for var in variable_content:
        if variable_content[var] == var2replace:
            variable_content[var] = var2keep

    for i in range(0,len(storage_location)):
        elem = storage_location[i]
        list_tuple = list(elem[0])
        if var2replace in list_tuple:
            pos = list_tuple.index(var2replace)
            list_tuple[pos] = var2keep
            storage_location[i] = (tuple(list_tuple),elem[1])


    #It may affect also to storage instructions
    for i in range(0,len(storage_order)):
        elem = storage_order[i]
        list_tuple = list(elem[0])
        if var2replace in list_tuple:
            pos = list_tuple.index(var2replace)
            list_tuple[pos] = var2keep
            storage_order[i] = (tuple(list_tuple),elem[1])
            
    
#It checks in which cases the loads are the same
def unify_loads_instructions(storage_location, location):
    global variable_content

    if location == "storage":
        instruction = "sload"
        store_ins = "sstore"
    elif location == "memory":
        instruction = "mload"
        store_ins = "mstore"

    i = 0
    finished = False
    
    while(i<len(storage_location) and not finished):
        elem = storage_location[i]
        if elem[0][-1].find(instruction)!=-1:
            loads = list(filter(lambda x: x[0][0] == elem[0][0] and x[0][-1].find(instruction)!=-1,storage_location[i+1::]))
            if len(loads)>0:
                load_ins = loads[0]
                pos_aux = storage_location[i+1::].index(load_ins)
                rest_list = storage_location[i+1:i+pos_aux+1]
                dep = []
                for j in range(len(rest_list)):
                    x = rest_list[j]
                    if(x[0][-1].find(store_ins)!=-1):
                        dep.append(are_dependent(elem,x,i,i+1+j, location))
                # st_list = list(filter(lambda x: x[0][-1].find(store_ins)!=-1, rest_list))
                # dep = list(map(lambda x: are_dependent(elem,x),st_list))
                
                if True not in dep:
                    # print(storage_location)
                    # print(memory_order)
                    # print(u_dict)
                    # print(elem, load_ins)

                    old = storage_location.pop(pos_aux+i+1)
                    update_variables_loads(elem,load_ins,storage_location, location)
                    unify_loads_instructions(storage_location,location)
                    # storage_location.insert(pos_aux+i+1,old)
                    finished = True
                
            
        i+=1


#It checks in which cases the loads are the same
#It is checked only respect to memory as it is the storage location that may affect keccaks
def unify_keccak_instructions(storage_location,storage_order, location = "memory"):
    global variable_content

    instruction = "keccak"
    store_ins = "mstore"

    i = 0
    finished = False
    while(i<len(storage_location) and not finished):
        elem = storage_location[i]
        if elem[0][-1].find(instruction)!=-1:
            keccaks = list(filter(lambda x: x[0][0] == elem[0][0] and x[0][1] == elem[0][1] and x[0][-1].find(instruction)!=-1,storage_location[i+1::]))
            if len(keccaks)>0:
                k_ins = keccaks[0]
                pos_aux = storage_location[i+1::].index(k_ins)
                rest_list = storage_location[i+1:i+pos_aux+1]
                # st_list = list(filter(lambda x: x[0][-1].find(store_ins)!=-1, rest_list))
                # dep = list(map(lambda x: are_dependent(elem,x),st_list))
                dep = []
                for j in range(len(rest_list)):
                    x = rest_list[j]
                    if(x[0][-1].find(store_ins)!=-1):
                        dep.append(are_dependent(elem,x,i,i+1+j, location))
                
                if True not in dep:
                    old = storage_location.pop(pos_aux+i+1)
                    update_variables_keccaks(elem,k_ins,storage_location,storage_order)
                    unify_keccak_instructions(storage_location,storage_order)
                    # storage_location.insert(pos_aux+i+1,old)
                    finished = True
                
            
        i+=1

        
def compute_identifiers_storage_instructions(storage_location, location, new_user_defins):

    if location == "storage":
        store = "sstore"
        store8 = ""
        store_up = "SSTORE"
        store8_up = ""
        load = "SLOAD"
    else:
        store = "mstore"
        store8 = "mstore8"
        store_up = "MSTORE"
        store8_up = "MSTORE8"
        load = "MLOAD"
    
    store_count = 0
    store8_count = 0
    keccak_count = 0
    
    storage_identifiers = []

    key_list = list(u_dict.keys())
    values_list = list(u_dict.values())

    
    for i in range(0,len(storage_location)):
        ins = storage_location[i]
        
        if ins[0][-1].find(store)!=-1:
            if location !="storage" and ins[0][-1].find(store8)!=-1:
                storage_identifiers.append(store8_up+"_"+str(store8_count))
                store8_count+=1
            elif location !="storage" and ins[0][-1].find("mstoreImmutable")!=-1:
                storage_identifiers.append(ins[0][-1])
            else:
                storage_identifiers.append(store_up+"_"+str(store_count))
                store_count+=1

        elif ins[0][-1].find("keccak")!=-1:
            keccak_ins = list(filter(lambda x: x[0][-1] == ins[0][-1],values_list))
            if len(keccak_ins)!=1: #if it does not exist means that it does not appear in the target stack and we have to create the identifier
                storage_identifiers.append("KECCAK256_"+str(keccak_count))
                keccak_count+=1
            else:
                pos = values_list.index(keccak_ins[0])
                var = key_list[pos]
                k_ins = list(filter(lambda x: x["disasm"] == "KECCAK256" and x["outpt_sk"] == [var],new_user_defins))
                if len(k_ins)!= 1:
                    raise Exception("Error in looking for keccak instruction")
                else:
                    storage_identifiers.append(k_ins[0]["id"])

            
        else: # loads instructions
            load_ins = list(filter(lambda x: x[0][-1] == ins[0][-1],values_list))
            if len(load_ins)!=1:
                raise Exception("Error in looking load instruction")
            
            pos = values_list.index(load_ins[0])
            var = key_list[pos]
            sload_ins = list(filter(lambda x: x["disasm"] == load and x["outpt_sk"] == [var],new_user_defins))

            if len(sload_ins)!= 1:
                raise Exception("Error in looking for load instruction")
            else:
                storage_identifiers.append(sload_ins[0]["id"])

    return storage_identifiers



def update_storage_sequences(removed_instructions):
    global storage_order
    global memory_order
    global storage_dep
    global memory_dep
    
    new_storage_order = []
    new_memory_order = []
    
    for ins in storage_order:
        instructions_name = ins[0][-1]
        inpt_var = ins[0][0]
        if instructions_name.find("sload")!=-1:
            unused = list(filter(lambda x: x["disasm"] == "SLOAD" and inpt_var in x["inpt_sk"],removed_instructions))
            if len(unused)==0:
                new_storage_order.append(ins)
        elif instructions_name.find("sstore")!=-1:
            unused = list(filter(lambda x: x["disasm"] == "SSTORE" and inpt_var == x["inpt_sk"][0],removed_instructions))
            if len(unused)==0:
                new_storage_order.append(ins)
        else:
            new_storage_order.append(ins)


    if storage_order != new_storage_order:
        stdep = generate_dependences(new_storage_order,"storage")
        stdep = simplify_dependencies(stdep)
        
        storage_dep = stdep
        storage_order = new_storage_order
        
    for ins in memory_order:
        instructions_name = ins[0][-1]
        inpt_var = ins[0][0]
        if instructions_name.find("mload")!=-1:
            unused = list(filter(lambda x: x["disasm"] == "MLOAD" and inpt_var in x["inpt_sk"],removed_instructions))
            if len(unused)==0:
                new_memory_order.append(ins)

        elif instructions_name.find("mstore8")!=-1:
            unused = list(filter(lambda x: x["disasm"] == "MSTORE8" and inpt_var == x["inpt_sk"][0],removed_instructions))
            if len(unused)==0:
                new_memory_order.append(ins)

        elif instructions_name.find("mstore")!=-1:
            unused = list(filter(lambda x: x["disasm"] == "MSTORE" and inpt_var == x["inpt_sk"][0],removed_instructions))
            if len(unused)==0:
                new_memory_order.append(ins)

        elif instructions_name.find("keccak")!=-1:
            unused = list(filter(lambda x: x["disasm"] == "KECCAK256" and inpt_var == x["inpt_sk"][0],removed_instructions))
            if len(unused)==0:
                new_memory_order.append(ins)
        else:
            new_storage_order.append(ins)
            
    if memory_order != new_memory_order:
        memdep = generate_dependences(new_memory_order,"memory")
        memdep = simplify_dependencies(memdep)
        
        memory_dep = memdep
        memory_order = new_memory_order
        
def translate_dependences_sfs(new_user_defins):    
    new_storage_dep = []
    new_memory_dep = []
    
    storage = compute_identifiers_storage_instructions(storage_order,"storage",new_user_defins)
    memory = compute_identifiers_storage_instructions(memory_order,"memory",new_user_defins)
    
    for e in storage_dep:
        first, second = e    
        new_storage_dep.append((storage[first],storage[second]))

    for e in memory_dep:
        first, second = e
        new_memory_dep.append((memory[first],memory[second]))

    return new_storage_dep, new_memory_dep
    

#it receives two tuples of the form ((ar1,arg2, opcode),arity) and
#checks if t1 has to be executed before t2.
def are_dependent(t1, t2, idx1, idx2, location = "memory"):
    dep = False


    #It uses memory analysis dependences
    if extra_dep_info!={}:
        pc_index1 = get_idx_in_instructions(idx1, location)
        pc_index2 = get_idx_in_instructions(idx2, location)

        if location == "memory":
            eqs = extra_dep_info["memory_deps_eqs"]
            neqs = extra_dep_info["memory_deps_noneqs"]
        elif location == "storage":
            eqs = extra_dep_info["storage_deps_eqs"]
            neqs = extra_dep_info["storage_deps_noneqs"]
        else:
            raise Exception("Unknown location")

        # print("*********************")
        # print(memory_order)
        # print(t1)
        # print(t2)
        # print(idx1)
        # print(idx2)
        # print(pc_index1)
        # print(pc_index2)
        # print(eqs)
        # print(neqs)
        # print("********************")
        
        if pc_index1 != -1 and pc_index2 != -1:
            if any(filter(lambda x: x.same_pair(pc_index1, pc_index2),eqs)):
                # print("IGUALES")
                return True

            if any(filter(lambda x: x.same_pair(pc_index1, pc_index2),neqs)):
                # print("DISTINTOS")
                return False
    
    #If we reach this points means that the memory analysis is not able to finfer any information related to the pair and we apply the current solver
    var1 = t1[0][0]
    ins1 = t1[0][-1]
    var2 = t2[0][0]
    ins2 = t2[0][-1]
    
    if (ins1.find("keccak")!=-1 and (ins2.find("sload")!=-1 or ins2.find("sstore")!=-1)) or ((ins2.find("keccak")!=-1 and (ins1.find("sload")!=-1 or ins1.find("sstore")!=-1))):
        dep = False

    elif str(var1) == str(var2):
        dep = True

    #The dependences with keccaks have to be computed only for mstore instructions.    
    elif ins1.find("mstore")!=-1 and ins2.find("keccak256")!=-1:
        if str(var1).startswith("s") or str(var2).startswith("s"):
            dep = True
        else:
            if int(var1)>= int(var2):
                if str(t2[0][1]).startswith("s") or int(var1)< int(var2)+int(t2[0][1]):
                    dep = True
                else:
                    dep = False
            else:
                dep = False

    elif ins1.find("keccak256")!=-1 and ins2.find("mstore")!=-1:
        if str(var1).startswith("s") or str(var2).startswith("s"):
            dep = True
        else:
            if int(var2)>= int(var1):
                if str(t1[0][1]).startswith("s") or int(var2)< int(var1)+int(t1[0][1]):
                    dep = True
                else:
                    dep = False
            else:
                dep = False
        
    else:
        var1_str = str(var1)
        var2_str = str(var2)
        if var1_str.startswith("s") and var2_str.startswith("s"):
            list1 = []
            list2 = []
            get_variables(var1,list1)
            get_variables(var2,list2)
            if var1 in list2 or var2 in list1:
                dep = False
            else:
                dep = True

                
        elif var1_str.startswith("s") or var2_str.startswith("s"):
            if mem40_pattern:
                if (ins1.find("mload")!=-1 or ins1.find("mstore")!=-1) and (var1_str =="64" or var2_str == "64"):
                    dep = False
                else:
                    dep = True
            else:
                dep = True

        else: #two int values
            var1_int, var2_int = int(var1), int(var2)
            # if ins1.find("mstore8")!=-1 and var1>=var2 and var1<int(var2)+32:

            # Two mstore8 are dependant if they affect the same memory position
            if ins1.find("mstore8") != -1 and ins2.find("mstore8") != -1:
                dep = var1_int == var2_int
            # ins1 is mstore8 and ins2 is mstore
            elif ins1.find("mstore8")!=-1 and var1_int>=var2_int and var1_int<var2_int+32:
                dep = True
            # elif ins2.find("mstore8")!=-1 and var2>=var1 and var2<var1+32:
            elif ins2.find("mstore8")!=-1 and var2_int>=var1_int and var2_int<var1_int+32:
                dep = True
            elif (ins1.find("mstore")!=-1 or ins2.find("mstore")!=-1) and (ins1.find("mstore8")==-1 and ins2.find("mstore8")==-1):
                alt1 = var1_int>=var2_int and var1_int<var2_int+32
                alt2 = var2_int>=var1_int and var2_int<var1_int+32
                dep = alt1 or alt2
            else:
                dep = False
            
    return dep

def get_variables(var1,list_variables):
    if var1 in u_dict:
        values = list(u_dict[var1])

        for v in values[:-1]:
            get_variables(v,list_variables)
        
    else:
        list_variables.append(var1)

def compute_clousure(deps):
    clousure = {}
    for e in deps:
        f = e[0]
        visited = compute_clousure_dir(f,deps,[])
        clousure[f] = visited

    return clousure

def compute_clousure_dir(v,deps,visited):
    candidates = list(filter(lambda x: x[0] == v, deps))
    for c in candidates:
        if c[1] not in visited:
            visited.append(c[1])
            compute_clousure_dir(c[1],deps,visited)
    return visited
        
    
def get_dependencies_balance(sto_dep,mem_dep):
    storage_balance = {}
    memory_balance = {}
    
    for e in sto_dep:
        f,s = e
        pre = storage_balance.get(f,0)
        post = storage_balance.get(s,0)

        storage_balance[f] = pre+1
        storage_balance[s] = post+1

    for e in mem_dep:
        f,s = e
        pre = memory_balance.get(f,0)
        post = memory_balance.get(s,0)

        memory_balance[f] = pre+1
        memory_balance[s] = post+1

def get_best_storage(clousure, ins_number):
    half = ins_number/2
    best = -1

    dep = {}
    
    for b in clousure:
        back = len(clousure[b])
        pre = len(list(filter(lambda x: b in x,clousure.values())))
        dep[b] = (pre,back)


        

def compute_delete_positions(old_storage, storage):
    delete_positions = []

    i = 0
    j = 0
    while(i<len(old_storage) and j<len(storage)):
        old = old_storage[i]
        new = storage[j]

        if old != new:
            if i !=0 and old == old_storage[i-1]:
                delete_positions.append(i-1)
            else:
                delete_positions.append(i)
            i+=1
            
        else:
            i+=1
            j+=1

    if i ==j: #the last element
        if i !=0 and old_storage[i] == old_storage[i-1]:
            delete_positions.append(i-1)
        else:
            delete_positions.append(i)

    return delete_positions


def compute_position_stores(instructions):

    stores_pos = []
    cont = 0
    
    for ins in instructions:
        if ins.startswith("nop("):
            nop = ins[4:-1]
            if nop.find("SSTORE")!=-1 or nop.find("MSTORE")!=-1:
                stores_pos.append(cont)
            cont +=1       
    
    return stores_pos

def get_sequence(split_list):
    i = 0
    split = []
    if split_list == []:
        return split
    
    while (i<len(split_list) and split_list[i]<max_bound):

        split.append(split_list[i])
        i+=1

    for i in split:
        split_list.pop(0)
        
    return split


def split_by_numbers(stores):
    s = 0
    last = 0
    split_list = []
    count = 0
    remove = 0

    next_split = ""
    while(stores!=[]):

        split = get_sequence(stores)
        if split == []:
            next_element = stores.pop(0)
            split_list.append(next_element+last)
            last= split_list[-1]
            stores = list(map(lambda x: x-next_element,stores))
        else:
            split_list.append(split[-1]+last)
            last = split_list[-1]
            stores = list(map(lambda x: x-split[-1],stores))
            
    return split_list
    

def split_blocks_by_number(instructions,where2split):
    blocks = []        
    ins_block = []
    cont = -1
    
    for ins in instructions:
        ins_block.append(ins)
        if ins.startswith("nop("):
            nop = ins[4:-1]
            cont+=1                    
            if where2split != [] and cont == where2split[0]:
                where2split.pop(0)
                prev = ins_block[-2]
                blocks.append(ins_block)
                ins_block = [prev,ins]
                
    blocks.append(ins_block)
    
    return blocks


def update_user_defins(target_stack, userdef_ins):
    new_userdef_ins = []
    already = False
    while(not already):
        new_userdef_ins = remove_unused_userdefins(target_stack,userdef_ins)
        if new_userdef_ins != userdef_ins:
            userdef_ins = new_userdef_ins
        else:
            already = True
    return new_userdef_ins

def remove_unused_userdefins(target_stack, userdef_ins):
    new_userdef_ins = []
    for u in userdef_ins:
        if not u["storage"]: 
            output_st = u["outpt_sk"][0]

            used = list(filter(lambda x: output_st in x["inpt_sk"], userdef_ins))
            if len(used) != 0 or output_st in target_stack:
                new_userdef_ins.append(u)
        else:
            new_userdef_ins.append(u)
    return new_userdef_ins
            
def generate_pops(not_used_variables):
    pop_id = 0

    pop_instructions = []
    obj = {}
    for v in not_used_variables:
        obj["id"] = "POP_"+str(pop_id)
        obj["opcode"] = process_opcode(str(opcodes.get_opcode("POP")[0]))
        obj["disasm"] = "POP"
        obj["inpt_sk"] = [v]
        obj["outpt_sk"] = []
        obj["push"] = False
        obj["gas"] = opcodes.get_ins_cost("POP")
        obj["size"] = get_ins_size("POP")
        obj["commutative"] = False
        obj["storage"] = False #It is true only for MSTORE and SSTORE

        pop_instructions.append(obj)
        pop_id+=1

    return pop_instructions

def generate_push_instruction(idx, value, out):
    # If v is not in push rebuilt, then it has been introduced from a direct PUSH
    # disasm_list = replace_repeated_values_by_dup(value, push_rebuilt, []) if value in push_rebuilt else [f'PUSH {hex(value)[2:]}']

    disasm_list = ['PUSH']
    obj = {}
    obj["id"] = "PUSH_"+str(idx) if value != 0 or not constants.push0_enabled else "PUSH0_"+str(idx)
    obj["opcode"] = process_opcode(str(opcodes.get_opcode("PUSH")[0])) if value != 0 or not constants.push0_enabled else process_opcode(str(opcodes.get_opcode("PUSH0")[0]))
    obj["disasm"] = "PUSH" if value != 0 or not constants.push0_enabled else "PUSH0"
    obj["inpt_sk"] = []
    obj["value"] = [value]
    obj["push"] = True
    obj["outpt_sk"] = [out]
    obj["gas"] = opcodes.get_ins_cost("PUSH") if value != 0 or not constants.push0_enabled else opcodes.get_ins_cost("PUSH0")
    obj["commutative"] = False
    obj["storage"] = False #It is true only for MSTORE and SSTORE
    obj["size"] = get_ins_size("PUSH",value)


    return obj

def transform_push_uninterpreted_functions(target_stack,uninterpreted_functions):
    global s_counter

    push_variables = {}
    new_variables = []
    new_uninterpreted = []

    push_idx = 0
    
    i = 0
    while i< len(target_stack):
        v = target_stack[i]
        if is_integer(v) != -1:
            s_var = push_variables.get(v,-1)
            if s_var == -1:
                s_var = "s("+str(s_counter)+")"
                push_variables[v] = s_var
                s_counter+=1
                new_obj = generate_push_instruction(push_idx, v, s_var)
                push_idx+=1
                new_uninterpreted.append(new_obj)
                
            target_stack[i] = s_var
            if s_var not in new_variables:
                new_variables.append(s_var)
        i+=1

    i = 0
    while(i < len(uninterpreted_functions)):
        ins = uninterpreted_functions[i]
        
        input_sk = ins["inpt_sk"]
        j = 0
        while j < len(input_sk):
            in_v = input_sk[j]
            if is_integer(in_v) != -1:
                s_var = push_variables.get(in_v,-1)
                if s_var == -1:
                    s_var = "s("+str(s_counter)+")"
                    push_variables[in_v] = s_var
                    s_counter+=1
                    new_obj = generate_push_instruction(push_idx, in_v, s_var)
                    push_idx+=1
                    new_uninterpreted.append(new_obj)

                input_sk[j] = s_var

                if s_var not in new_variables:
                    new_variables.append(s_var)

                
            j+=1
        
        i+=1

    return new_variables, new_uninterpreted

def compute_vars(tstack, sstack, userdef_ins):
    total_vars = 0
    visited = []
    
    last_atomic = True
    total_current = 0
    sstack_aux = list(sstack)
    coincide = True
    i = len(sstack)-1
    j = len(tstack)-1
    
    while(i>=0 and coincide and tstack != []):
        if(sstack[i] == tstack[j]):
            sstack_aux.pop()
        else:
            coincide = False

        i-=1
        j-=1
            
    if not coincide and sstack_aux != sstack:
        current = len(sstack_aux)
    else:
        current = 0
        
    
    # current = 0#len(sstack)
    for v in tstack[::-1]:
        # print(v)
        visited_old = list(visited)
        max_stack,current_var,is_atomic=compute_vars_aux(v,sstack,tstack,userdef_ins,visited)

        # print(max_stack)
        # print(current_var)
        
        
        num_vars = current+max_stack

        #If the current variable needs to be considered from the beginning as part of the input stack
        if v in sstack and v not in visited_old:
            v_value = int(v[2:-1])
            sstack_vars = list(filter(lambda x: x in sstack,visited_old))
            if sstack_vars != []:
                v_already = max(list(map(lambda x: int(x[2:-1]),sstack_vars)))

                if v_value > v_already:
                    total_vars+= v_value-v_already
            else:
                total_vars+=v_value+1
        current+=current_var
        # print(current)
        # print(num_vars)
        
        if total_vars < max(num_vars,current):
            total_vars = max(num_vars,current)
        
        # if last_atomic:
        #     total_vars+=max_stack

        # else:
        #     total_current = current+total_vars
            
        # last_atomic = is_atomic
        # print(total_vars)
        # print(total_current)
        # print("************")
        # if (max_stack > total_vars):
        #     total_vars += max_stack
        # total_vars+=m
    # print(total_vars)
    storage = list(filter(lambda x: x["disasm"].find("MSTORE")!=-1 or x["disasm"] == "SSTORE", userdef_ins))
    for s in storage:
        inp_vars = s["inpt_sk"]
        for v in inp_vars:
            t,m,_=compute_vars_aux(v,sstack,tstack,userdef_ins,visited)
            total_vars+= t

    # for v in visited:
    #     if v in sstack and v not in tstack:
    #         total_vars+=1
            

    for v in sstack:
        is_input = list(filter(lambda x: v in x["inpt_sk"], userdef_ins))
        if (len(is_input) == 0) and (v not in tstack):
            total_vars+=1
        elif (len(is_input)>0 and (v in tstack)):
            total_vars+=tstack.count(v)-(len(is_input)-1)

    max_stacks = max(len(sstack), len(tstack))
            
    return max(max_stacks,total_vars)
        
def compute_vars_aux(var, sstack, tstack, userdef_ins, visited):

    if var in visited:
        return 1,1, True
    elif var in sstack and var not in visited:
        
        val = int(var[2:-1])
        
        already_computed = list(filter(lambda x: x in sstack,visited))
        already_val = -1 if already_computed == [] else max(list(map(lambda x: int(x[2:-1]), already_computed)))

        visited.append(var)
        
        # print("++++++++")
        # print(visited)
        # print(already_computed)
        # print(already_val)
        # print(val)
        # print("+++++++")
        
        if val > already_val:
            # print("HOLA")
            return val+1,1, True
        else:
            return 1,1, True
            
    elif is_integer(var)!=-1:
        if var not in visited:
            visited.append(var) 
        return 1,1, True
    else:
        instr_l = list(filter(lambda x: var in x["outpt_sk"], userdef_ins))
        if len(instr_l) == 0:
            raise Exception("Error in computing vars")

        instr = instr_l[0]
        inpt_vars = instr["inpt_sk"]
        
        if inpt_vars == []:
            visited.append(var)
            return 1,1, True

        # print(instr["disasm"])
        total = 0
        total_current=0
        acc_current=0
        last_var_atomic = True

        for v in inpt_vars[::-1]:
            num_vars, current, _ = compute_vars_aux(v,sstack,tstack,userdef_ins,visited)
            acc_current+=current
            # print("AQUI!")
            # print(num_vars)
            # print(current)
            
            if(last_var_atomic):
                total+=num_vars
            else:
                total = max(total,acc_current+num_vars)
            
            last_var_atomic = is_atomic(v,sstack)

        # print(total)
        # print(total_current)
        #     print("--")
        # print("TERMINO:"+ instr["disasm"])
        # print("*********")

        acc_current+=len(instr["outpt_sk"])-len(inpt_vars)

        if var not in visited:
            visited.append(var)

        return max(total,acc_current), acc_current, False

def is_atomic(var,sstack):
    if var in sstack or is_integer(var)!=-1:
        return True
    else:
        return False

    
def generate_subblocks2split(rule,part,split_sto):

    instructions = filter_opcodes(rule)
    opcodes = get_opcodes(rule)    

    res = is_optimizable(opcodes,instructions)
    if res:
        ops = list(map(lambda x: x[4:-1],opcodes))

        original_ins = ops

        if part:
            if len(opcodes) > max_bound and not split_sto:
                stores_pos = compute_position_stores(opcodes)
                where2split = split_by_numbers(stores_pos)

                if where2split == []:
                    subblocks = [opcodes]

                else:
                    subblocks = split_blocks_by_number(rule.get_instructions(),where2split)
            else:
                subblocks = [opcodes]
        else:
            subblocks = [opcodes]
    else: #we need to split the blocks into subblocks
        r = False
        new_instructions = []

        subblocks = split_blocks(rule,r,new_instructions)       
        if part:
            end_subblocks = []
            for s in subblocks:
                o = list(filter(lambda x:x.find("nop(")!=-1,s))

                if split_sto:
                    stores_pos = []
                else:
                    stores_pos = compute_position_stores(o)

                if len(o)> max_bound and stores_pos !=[]:
                    where2split = split_by_numbers(stores_pos)
                    if where2split == []:
                        end_subblocks.append(s)
                    else:
                        subblocks_aux = split_blocks_by_number(s,where2split)
                        end_subblocks+=subblocks_aux
                else:
                    end_subblocks.append(s)
            subblocks = end_subblocks

    subblocks_postprocess = []
    for s in subblocks:
        s1 = list(filter(lambda x: x.find("nop(")!=-1,s))
        ins = list(map(lambda x: x.strip()[4:-1],s1))
        subblocks_postprocess.append(ins)

    # print(subblocks_postprocess)
        
    return subblocks_postprocess

def unify_all_user_defins(ts,user_def_instructions,list_vars):

    modified = True
    target_stack = ts
    user_defins = user_def_instructions
    while(modified):
        modified, user_defins, target_stack = unify_user_defins(target_stack,user_defins,list_vars)

    return user_defins,target_stack

def unify_user_defins(ts,user_def_instructions,list_vars):

    to_delete = []
    target_stack = ts
    user_defins = user_def_instructions
    modified = False
    
    for ins in user_defins:
        if ins["disasm"] not in ["SHA3","SLOAD","MLOAD","KECCAK256","SSTORE","MSTORE","GAS","TIMESTAMP"] and ins not in to_delete:
            duplicated = list(filter(lambda x: x["inpt_sk"] == ins["inpt_sk"] and x["disasm"] == ins["disasm"] and x.get("value",-1) == -1, user_defins))
            if len(duplicated) > 1:
                tokeep = duplicated[0]
                # print(duplicated)
                for rest in duplicated[1:]:
                    replace_var_userdef(rest["outpt_sk"][0],tokeep["outpt_sk"][0],user_defins)
                    target_stack = replace_var(rest["outpt_sk"][0],tokeep["outpt_sk"][0],target_stack)
                    # print(list_vars)
                    delete_from_listvars(rest["outpt_sk"][0],list_vars)
                    to_delete.append(rest)
                modified = True
    i = 0
    new_user_def = []
    while len(user_defins)>0:
        instr = user_defins.pop()
        if instr not in to_delete:
            new_user_def.append(instr)

    return modified, new_user_def, target_stack
