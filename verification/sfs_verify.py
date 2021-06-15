import sys
import os
sys.path.append(os.path.dirname(os.path.realpath(__file__))+"/../ethir")
from utils_verify import *
import rbr_isolate_block
from utils import process_isolate_block
from syrup_optimization import get_sfs_dict
from timeit import default_timer as dtimer

costabs_path = "/tmp/costabs/"
solutions_path = costabs_path + "solutions/"


'''
The jsons are going to be different. What needs to be the same are the
uninterpreted functions, and source and target stack.
'''

def are_equals(json_orig, json_opt):

    # print("COMPARA")
    # print(json_orig)
    # print(json_opt)


    src_orig = json_orig["src_ws"]
    src_opt = json_opt["src_ws"]

    src_st = src_orig == src_opt

    tgt_orig = json_orig["tgt_ws"]
    tgt_opt = json_opt["tgt_ws"]
    
    tgt_st = compare_target_stack(json_orig, json_opt)

    # unint_func = len(json_opt["user_instrs"]) == len(json_orig["user_instrs"])
    # for fun in json_opt["user_instrs"]:
    #     unint_func = unint_func and (fun in json_orig["user_instrs"])

    #The uninterpreted fucntions are compared within the target stacks
    
    if (src_st and tgt_st):
        # print(True)
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

# def compare_usrdef_instr(elem_origin, elem_opt, json_origin,json_opt):

#     #If they do not represent the same instruction
#     if elem_origin["disasm"] != elem_opt["disasm"]:
#         return False

#     j = 0

#     inpt_origin = elem_origin["inpt_sk"]
#     inpt_opt = elem_opt["inpt_sk"]
#     while j < len(elem_origin["inpt_sk"]):
#         var = inpt_origin[j]

#         if var in json_origin["src_ws"] and inpt_opt[j] != var:
#             return False 


#         elif var not in json_origin["src_ws"]:
            
#             elem_origin = filter(lambda x : var in x["outpt_sk"], json_origin["user_instrs"])
#             elem_opt = filter(lambda x: inpt_opt[j] in x["outpt_sk"], json_opt["user_instrs"])

#             if len(elem_origin) != len (elem_opt):
#                 return False

#             #They may be different or not
#             if elem_origin[0] != elem_opt[0]:
#                 r = compare_usrdef_instr(elem_origin[0],elem_opt[0], json_origin, json_opt)
#                 if not r:
#                     return False
#         j+=1

#     return True
    

def verify_sfs(source, sfs_dict):

    report = ""
    
    if sfs_dict != {}:
        if not os.path.exists(solutions_path):
            print("[ERROR] Path "+solutions_path+" does not exist.")
        else:
            init_time = dtimer()
            
            keys_dict = sfs_dict.keys()
            solution_files = list(filter(lambda x: x.find("disasm_opt")!=-1,os.listdir(solutions_path)))
            for f in solution_files:

                if "syrup_contract" in keys_dict:
                    contract = "syrup_contract"
                else:
                    contract = get_contract_name(f)
                    
                block_id = get_block_id(f)
                if os.path.getsize(solutions_path+f)!=0:
                    if len(solution_files) == 1: #analyze json directly
                        try:
                            json_obj = sfs_dict[contract][block_id]
                        except:
                            json_obj = sfs_dict
                        block_id = f
                    else:
                        print(contract)
                        json_obj = sfs_dict[contract][block_id]
                    input_stack = len(json_obj["src_ws"])
                    gas = json_obj["current_cost"]

                    x, y = process_isolate_block(solutions_path+f, input_stack)

                    block_data = {}
                    block_data["instructions"] = x
                    block_data["input"] = y

                    print(block_data)
                    
                    value_gas = get_block_cost(x)

                    if value_gas > gas:
                        result = "Block "+block_id+" : GAS ERROR"
                        report+=result+"\n"

                    else:
                        cname_aux = source.split("/")[-1]
                        cname = cname_aux.strip().split(".")[0]
    
                        exit_code = rbr_isolate_block.evm2rbr_compiler(contract_name = cname, syrup = True, block = block_data)
                        json_opt_c = get_sfs_dict()
                        print("++++++++++++++")
                        print(json_opt_c)

                        if len(json_opt_c)>1:
                            print("[ERROR] Something fails with the optimized block.")
                        else:
                            json_opt = json_opt_c["syrup_contract"]
                            result = are_equals(json_obj,json_opt[next(iter(json_opt.keys()))])

                            if result:
                                result = "Block "+block_id+" :VERIFIED"
                            else:
                                result = "Block "+block_id+" :NO VERIFIED"
                            report+=result+"\n"
                    
                else:
                    report += "File for "+block_id+" is empty.\n"

            with open(costabs_path + "report_verification.txt", 'w') as f:
                print(report)
                f.write(report)

            end_time = dtimer()
            
            print("*************************************************************")
            print("Verification time: "+str(end_time-init_time)+"s")
            print("*************************************************************")

                
    else:
        print("There are not solutions generated. They cannot be verified.")



if __name__ == '__main__':
    verify_sfs({'block0':'prueba'})
