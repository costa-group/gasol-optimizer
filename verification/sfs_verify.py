from utils_verify import *

'''
The jsons are going to be different. What needs to be the same are the
uninterpreted functions, and source and target stack.
'''

def are_equals(json_orig, json_opt):

    src_orig = json_orig["src_ws"]
    src_opt = json_opt["src_ws"]

    src_st = src_orig == src_opt
    
    tgt_st = compare_target_stack(json_orig, json_opt)
    
    if src_st and tgt_st:
        return True
    else:
        return False


def compare_target_stack(json_origin, json_opt):

    src_origin = json_origin["src_ws"]
    src_opt = json_opt["src_ws"]
    tgt_origin = json_origin["tgt_ws"]
    tgt_opt = json_opt["tgt_ws"]


    if len(tgt_origin) != len(tgt_opt):
        return False

    i = 0
    
    while i < len(tgt_origin):
        #If an element is in the source stack it has to be stored in
        #the same location and it has to be the same in both target
        #stack representations

        
        r = compare_variables(tgt_origin[i], tgt_opt[i], src_origin, src_opt, json_origin["user_instrs"], json_opt["user_instrs"])

        if not r:
            return False

        i+=1

    return True
        

def compare_variables(var_origin, var_opt, src_origin, src_opt, user_def_origin, user_def_opt):

    #If var is in the source stack, it has to be the same variable in
    #both representations
    if var_origin in src_origin and var_origin != var_opt:
        return False

    if is_integer(var_origin) and var_origin !=var_opt:
        return False

    #It corresponds to a uninterpreted function. The name of the stack
    #variable may differ but it has to be the same function with the
    #same arguments.  Non-uninterpreted function
    elif var_origin not in src_origin and not is_integer(var_origin):
        elem_origin_l = list(filter(lambda x : var_origin in x["outpt_sk"], user_def_origin))
        elem_opt_l = list(filter(lambda x: var_opt in x["outpt_sk"], user_def_opt))

        if len(elem_origin_l) != len (elem_opt_l):
            return False

        elem_origin = elem_origin_l[0]
        elem_opt = elem_opt_l[0]

        #They may be different or not
        if elem_origin != elem_opt:
            if elem_origin["disasm"] != elem_opt["disasm"]:
                return False
            
            j = 0

            result = True
            
            inpt_origin = elem_origin["inpt_sk"]
            inpt_opt = elem_opt["inpt_sk"]
            
            while j < len(inpt_origin):
                r = compare_variables(inpt_origin[j], inpt_opt[j],src_origin, src_opt, user_def_origin, user_def_opt)
                result = result and r
                j+=1

            if not result and not elem_origin["commutative"]:
                return False

            if not result and elem_origin["commutative"]:
                result = True
                j = 0
                while j < len(inpt_origin):
                    r = compare_variables(inpt_origin[j], inpt_opt[len(inpt_opt)-j-1],src_origin, src_opt, user_def_origin, user_def_opt)
                    if not r:
                        return False
                    j+=1
    return True


# Given two lists of sfs_dict (possibly, corresponding to the sub blocks from the same block)
# compares the equivalence between them.
def verify_block_from_list_of_sfs(old_sfs_dict, new_sfs_dict):
    old_block_ids = old_sfs_dict.keys()
    new_block_ids = new_sfs_dict.keys()

    # Both sfs dicts must contain the same sub blocks
    if set(old_block_ids) != set(new_block_ids):
        return False

    for key in old_block_ids:
        old_sfs = old_sfs_dict[key]
        new_sfs = new_sfs_dict[key]

        if not are_equals(old_sfs, new_sfs):
            return False
    return True
