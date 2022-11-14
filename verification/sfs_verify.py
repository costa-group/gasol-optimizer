from verification.utils_verify import is_integer

'''
The jsons are going to be different. What needs to be the same are the
uninterpreted functions, and source and target stack.
'''

def are_equals(json_orig, json_opt):

    src_orig = json_orig["src_ws"]
    src_opt = json_opt["src_ws"]

    src_st = src_orig == src_opt

    if not src_st:
        return False, "Different source stack"

    tgt_st, reason = compare_target_stack(json_orig, json_opt)

    if not tgt_st:
        return False, reason

    dep_orig = json_orig["storage_dependences"]
    dep_opt = json_opt["storage_dependences"]
    userdef_orig = json_orig["user_instrs"]
    userdef_opt = json_opt["user_instrs"]

    same_dep_sto = compare_dependences(dep_orig,dep_opt,src_orig,src_opt,userdef_orig,userdef_opt,"storage")

    if not same_dep_sto:
        return False, "Storage dependences are different"

    dep_orig = json_orig["memory_dependences"]
    dep_opt = json_opt["memory_dependences"]

    same_dep_mem = compare_dependences(dep_orig,dep_opt,src_orig,src_opt,userdef_orig,userdef_opt,"memory")

    if not same_dep_mem:
        return False, "Memory dependences generated are different"

    same_userdef, reason = compare_storage_userdef_ins(src_orig, src_opt,userdef_orig,userdef_opt)

    if not same_userdef:
        return False, reason

    if src_st and tgt_st and same_dep_mem and same_userdef:
        return True, ""
    else:
        return False, "ERROR"


def compare_target_stack(json_origin, json_opt):

    src_origin = json_origin["src_ws"]
    src_opt = json_opt["src_ws"]
    tgt_origin = json_origin["tgt_ws"]
    tgt_opt = json_opt["tgt_ws"]


    if len(tgt_origin) != len(tgt_opt):
        return False, "Different lenghts between target stacks"

    i = 0

    while i < len(tgt_origin):
        #If an element is in the source stack it has to be stored in
        #the same location and it has to be the same in both target
        #stack representations


        r, reason_element = compare_variables(tgt_origin[i], tgt_opt[i], src_origin, src_opt, json_origin["user_instrs"], json_opt["user_instrs"])

        if not r:
            reason = "Elements "+str(tgt_origin[i])+"(original sfs) and "+ str(tgt_opt[i])+"(optimized sfs) in target stack are different\n"+reason_element
            return False, reason

        i+=1

    return True, ""


def compare_dependences(dep_origin,dep_opt,src_origin,src_opt,user_def_origin,user_def_opt,location):
    i = 0
    verified = True

    if location == "storage":
        ins_origin = list(filter(lambda x: x["disasm"].find("SSTORE")!=-1 or x["disasm"].find("SLOAD")!=-1,user_def_origin))
        ins_opt = list(filter(lambda x: x["disasm"].find("SSTORE")!=-1 or x["disasm"].find("SLOAD")!=-1,user_def_opt))
    else:
        ins_origin = list(filter(lambda x: x["disasm"].find("MSTORE")!=-1 or x["disasm"].find("MLOAD")!=-1 or x["disasm"].find("KECCAK")!=-1,user_def_origin))
        ins_opt = list(filter(lambda x: x["disasm"].find("MSTORE")!=-1 or x["disasm"].find("MLOAD")!=-1 or x["disasm"].find("KECCAK")!=-1,user_def_opt))

    if len(dep_origin) != len(dep_opt):
        return False


    while(i< len(dep_origin) and verified):
        dep = dep_origin[i]

        # it may have different identifiers We have to check if any
        # tuple in dep_opt corresponds to dep
        if dep not in dep_opt:
            first = dep[0]
            second = dep[1]

            first_instr_list = list(filter(lambda x: x["id"] == first, ins_origin))
            if len(first_instr_list) != 1:
                raise ValueError

            first_instr = first_instr_list[0]

            second_instr_list = list(filter(lambda x: x["id"] == second, ins_origin))
            if len(second_instr_list) != 1:
                raise ValueError

            second_instr = second_instr_list[0]


            r,first_opt_id = search_val_in_userdef(first_instr,ins_opt,src_origin,src_opt,user_def_origin,user_def_opt)
            r1,second_opt_id = search_val_in_userdef(second_instr,ins_opt,src_origin,src_opt,user_def_origin,user_def_opt)

            if all(first_opt_id != dependency[0] or second_opt_id != dependency[1] for dependency in dep_opt):
                if first.find("KECCAK")!= -1:
                    dep_opt_elemlist = list(filter(lambda x: x[0].find("KECCAK")!=-1 and x[1] == second_opt_id, dep_opt))
                    if len(dep_opt_elemlist) == 0:
                        raise ValueError

                    dep_opt_elem = dep_opt_elemlist[0]
                    keccak_elem = list(filter(lambda x: x["id"] == dep_opt_elem[0], ins_opt))[0]
                    r, _ = compare_variables(first_instr["outpt_sk"][0], keccak_elem["outpt_sk"][0], src_origin, src_opt, user_def_origin, user_def_opt)
                    verified = second_opt_id!=-1 and r
                    
                    
                elif second.find("KECCAK")!=-1:

                    # print(dep_opt)
                    
                    dep_opt_elemlist = list(filter(lambda x: x[1].find("KECCAK")!=-1 and x[0] == first_opt_id, dep_opt))
                    if len(dep_opt_elemlist) == 0:
                        raise ValueError

                    dep_opt_elem = dep_opt_elemlist[0]
                    keccak_elem = list(filter(lambda x: x["id"] == dep_opt_elem[1], ins_opt))[0]

                    # print(second_instr["outpt_sk"])
                    # print(keccak_elem["outpt_sk"])
                    
                    r, _ = compare_variables(second_instr["outpt_sk"][0], keccak_elem["outpt_sk"][0], src_origin, src_opt, user_def_origin, user_def_opt)
                    verified = second_opt_id!=-1 and r

                    # verified = first_opt_id != -1 and second_opt_id!=-1

                else:
                    verified = False

        i+=1
    return verified

def compare_storage_userdef_ins(src_origin,src_opt,user_def_origin,user_def_opt):
    storage_ins_origin = list(filter(lambda x: x["disasm"].find("SSTORE")!=-1 or x["disasm"].find("SLOAD")!=-1,user_def_origin))
    storage_ins_opt = list(filter(lambda x: x["disasm"].find("SSTORE")!=-1 or x["disasm"].find("SLOAD")!=-1,user_def_opt))

    memory_ins_origin = list(filter(lambda x: x["disasm"].find("MSTORE")!=-1 or x["disasm"].find("MLOAD")!=-1,user_def_origin))
    memory_ins_opt = list(filter(lambda x: x["disasm"].find("MSTORE")!=-1 or x["disasm"].find("MLOAD")!=-1,user_def_opt))

    if len(storage_ins_origin) != len(storage_ins_opt):
        return False, "Different lengths between storage operations"

    if len(memory_ins_origin) != len(memory_ins_opt):
        return False, "Different lengths between memory operations"

    i = 0
    verified = True
    while(i < len(storage_ins_origin) and verified):
        ins = storage_ins_origin[i]

        if ins not in storage_ins_opt:
            r,new_id = search_val_in_userdef(ins,storage_ins_opt,src_origin,src_opt,user_def_origin,user_def_opt)

            if new_id == -1:
                verified = False
        i+=1


    if not verified:
        return False, "Element "+str(ins)+" in original sfs does not appear in the optimized one"

    i = 0
    verified = True
    while(i < len(memory_ins_origin) and verified):
        ins = memory_ins_origin[i]

        if ins not in memory_ins_opt:
            r,new_id = search_val_in_userdef(ins,memory_ins_opt,src_origin,src_opt,user_def_origin,user_def_opt)

            if new_id == -1:
                verified = False
        i+=1

    if not verified:
        return False, "Element "+str(ins)+" in original sfs does not appear in the optimized one"

    return verified, ""


def search_val_in_userdef(instruction, storage_ins,src_origin,src_opt,user_def_origin,user_def_opt):

    found = False
    i = 0

    idx = -1

    while(i<len(storage_ins) and not found):
        opt_ins = storage_ins[i]

        if instruction["disasm"] == opt_ins["disasm"]:
            inpt_origin = instruction["inpt_sk"]
            inpt_opt = opt_ins["inpt_sk"]

            j = 0

            result = True



            while j < len(inpt_origin):
                r,_ = compare_variables(inpt_origin[j], inpt_opt[j],src_origin, src_opt, user_def_origin, user_def_opt)
                result = result and r
                j+=1

            if result:
                idx = opt_ins["id"]
                found = result

        i+=1


    return found,idx


def compare_variables(var_origin, var_opt, src_origin, src_opt, user_def_origin, user_def_opt):

    #If var is in the source stack, it has to be the same variable in
    #both representations
    if var_origin in src_origin and var_origin != var_opt:
        return False, "The variables do not refer to the same source stack element"

    if is_integer(var_origin) and var_origin !=var_opt:
        return False, "Variables does not represent the same integer"

    #It corresponds to a uninterpreted function. The name of the stack
    #variable may differ but it has to be the same function with the
    #same arguments.  Non-uninterpreted function
    elif var_origin not in src_origin and not is_integer(var_origin):
        elem_origin_l = list(filter(lambda x : var_origin in x["outpt_sk"], user_def_origin))
        elem_opt_l = list(filter(lambda x: var_opt in x["outpt_sk"], user_def_opt))

        if len(elem_origin_l) != len (elem_opt_l):
            return False, "Definition of "+str(var_origin)+ "and "+ str(var_opt) + "differs"

        elem_origin = elem_origin_l[0]
        elem_opt = elem_opt_l[0]

        #They may be different or not
        if elem_origin != elem_opt:
            if elem_origin["disasm"] != elem_opt["disasm"]:
                return False, "Different opcode between "+str(var_origin)+ "and "+ str(var_opt)+". Original: "+str(elem_origin["disasm"])+" --- Optimized: "+str(elem_opt["disasm"])

            if elem_origin["disasm"] == "PUSH":
                if elem_origin["value"] == elem_opt["value"]:
                    return True, ""
                else:
                    return False, "PUSH values are different"

            j = 0

            result = True

            inpt_origin = elem_origin["inpt_sk"]
            inpt_opt = elem_opt["inpt_sk"]

            while j < len(inpt_origin):
                r, reason_aux = compare_variables(inpt_origin[j], inpt_opt[j],src_origin, src_opt, user_def_origin, user_def_opt)

                if not r and result:
                    reason = reason_aux

                result = result and r
                j+=1

            if not result and not elem_origin["commutative"]:
                return False, reason

            if not result and elem_origin["commutative"]:
                result = True
                j = 0
                while j < len(inpt_origin):
                    r, reason = compare_variables(inpt_origin[j], inpt_opt[len(inpt_opt)-j-1],src_origin, src_opt, user_def_origin, user_def_opt)
                    if not r:
                        return False, reason
                    j+=1

    return True, ""


# Given two lists of sfs_dict (possibly, corresponding to the sub blocks from the same block)
# compares the equivalence between them.
def verify_block_from_list_of_sfs(old_sfs_dict, new_sfs_dict):
    old_block_ids = old_sfs_dict.keys()
    new_block_ids = new_sfs_dict.keys()

    # Both sfs dicts must contain the same sub blocks
    if set(old_block_ids) != set(new_block_ids):
        return False, "Different number of subblocks"

    for key in old_block_ids:
        old_sfs = old_sfs_dict[key]
        new_sfs = new_sfs_dict[key]

        eq, reason = are_equals(old_sfs, new_sfs)

        if not eq:
            return False, reason
    return True, ""
