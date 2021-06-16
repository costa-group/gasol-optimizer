# return true if the two paths have different flows of money
# later on we may want to return more meaningful output: e.g. if the concurrency changes
# the amount of money or the recipient.
import shlex
import subprocess
import json
import mmap
import os
import errno
import signal
import csv
import re
import difflib
import six
from functools import reduce
#from z3 import *
#from z3.z3util import get_vars

from dot_tree import Tree, build_tree
from global_params import costabs_path, tmp_path, costabs_folder
# costabs_path = "/tmp/costabs/"
# tmp_path = "/tmp/"

def ceil32(x):
    return x if x % 32 == 0 else x + 32 - (x % 32)

def isSymbolic(value):
    return not isinstance(value, six.integer_types)

def isReal(value):
    return isinstance(value, six.integer_types) or isinstance(value,float)

def isAllReal(*args):
    for element in args:
        if isSymbolic(element):
            return False
    return True

def to_symbolic(number):
    if isReal(number):
        # print number
        # print BitVecVal(number, 256)
        return number#BitVecVal(number, 256)
    return number

def to_unsigned(number):
    if number < 0:
        return abs(number)# + 2**256
    return number

def to_signed(number):
    if number > 2**(256 - 1):
        return (2**(256) - number) * (-1)
    else:
        return number

def check_sat(solver, pop_if_exception=True):
    try:
        ret = solver.check()
        if ret == unknown:
            raise Z3Exception(solver.reason_unknown())
    except Exception as e:
        if pop_if_exception:
            solver.pop()
        raise e
    return ret

def custom_deepcopy(input):
    output = {}
    for key in input:
        if isinstance(input[key], list):
            output[key] = list(input[key])
        elif isinstance(input[key], dict):
            output[key] = custom_deepcopy(input[key])
        else:
            output[key] = input[key]
    return output

# check if a variable is a storage address in a contract
# currently accept only int addresses in the storage
def is_storage_var(var):
    return isinstance(var, six.integer_types)
    #     return True
    # else:
    #     return isinstance(var, str) and var.startswith("Ia_store_")


# copy only storage values/ variables from a given global state
# TODO: add balance in the future
def copy_global_values(global_state):
    new_gstate = {}

    for var in global_state["Ia"]:
        if is_storage_var(var):
            new_gstate[var] = global_state["Ia"][var]
    return new_gstate


# check if a variable is in an expression
def is_in_expr(var, expr):
    list_vars = get_vars(expr)
    set_vars = set(i.decl().name() for i in list_vars)
    return var in set_vars


# check if an expression has any storage variables
def has_storage_vars(expr, storage_vars):
    list_vars = get_vars(expr)
    for var in list_vars:
        if var in storage_vars:
            return True
    return False


def get_all_vars(list_of_storage_exprs):
    ret_vars = []
    for expr in list_of_storage_exprs:
        ret_vars += get_vars(list_of_storage_exprs[expr])
    return ret_vars


# Rename variables to distinguish variables in two different paths.
# e.g. Ia_store_0 in path i becomes Ia_store_0_old if Ia_store_0 is modified
# else we must keep Ia_store_0 if its not modified
def rename_vars(pcs, global_states):
    ret_pcs = []
    vars_mapping = {}

    for expr in pcs:
        list_vars = get_vars(expr)
        for var in list_vars:
            if var in vars_mapping:
                expr = substitute(expr, (var, vars_mapping[var]))
                continue
            var_name = var.decl().name()
            # check if a var is global
            if var_name.startswith("Ia_store_"):
                position = var_name.split('Ia_store_')[1]
                # if it is not modified then keep the previous name
                if position not in global_states:
                    continue
            # otherwise, change the name of the variable
            new_var_name = var_name + '_old'
            new_var = BitVec(new_var_name, 256)
            vars_mapping[var] = new_var
            expr = substitute(expr, (var, vars_mapping[var]))
        ret_pcs.append(expr)

    ret_gs = {}
    # replace variable in storage expression
    for storage_addr in global_states:
        expr = global_states[storage_addr]
        # z3 4.1 makes me add this line
        if is_expr(expr):
            list_vars = get_vars(expr)
            for var in list_vars:
                if var in vars_mapping:
                    expr = substitute(expr, (var, vars_mapping[var]))
                    continue
                var_name = var.decl().name()
                # check if a var is global
                if var_name.startswith("Ia_store_"):
                    position = int(var_name.split('_')[len(var_name.split('_'))-1])
                    # if it is not modified
                    if position not in global_states:
                        continue
                # otherwise, change the name of the variable
                new_var_name = var_name + '_old'
                new_var = BitVec(new_var_name, 256)
                vars_mapping[var] = new_var
                expr = substitute(expr, (var, vars_mapping[var]))
        ret_gs[storage_addr] = expr

    return ret_pcs, ret_gs


# split a file into smaller files
def split_dicts(filename, nsub = 500):
    with open(filename) as json_file:
        c = json.load(json_file)
        current_file = {}
        file_index = 1
        for u, v in c.iteritems():
            current_file[u] = v
            if len(current_file) == nsub:
                with open(filename.split(".")[0] + "_" + str(file_index) + '.json', 'w') as outfile:
                    json.dump(current_file, outfile)
                    file_index += 1
                    current_file.clear()
        if len(current_file):
            with open(filename.split(".")[0] + "_" + str(file_index) + '.json', 'w') as outfile:
                json.dump(current_file, outfile)
                current_file.clear()


def do_split_dicts():
    for i in range(11):
        split_dicts("contract" + str(i) + ".json")
        os.remove("contract" + str(i) + ".json")


def run_re_file(re_str, fn):
    size = os.stat(fn).st_size
    with open(fn, 'r') as tf:
        data = mmap.mmap(tf.fileno(), size, access=mmap.ACCESS_READ)
        return re.findall(re_str, data)


def get_contract_info(contract_addr):
    six.print_("Getting info for contracts... " + contract_addr)
    file_name1 = "tmp/" + contract_addr + "_txs.html"
    file_name2 = "tmp/" + contract_addr + ".html"
    # get number of txs
    txs = "unknown"
    value = "unknown"
    re_txs_value = r"<span>A total of (.+?) transactions found for address</span>"
    re_str_value = r"<td>ETH Balance:\n<\/td>\n<td>\n(.+?)\n<\/td>"
    try:
        txs = run_re_file(re_txs_value, file_name1)
        value = run_re_file(re_str_value, file_name2)
    except Exception as e:
        try:
            os.system("wget -O %s http://etherscan.io/txs?a=%s" % (file_name1, contract_addr))
            re_txs_value = r"<span>A total of (.+?) transactions found for address</span>"
            txs = run_re_file(re_txs_value, file_name1)

            # get balance
            re_str_value = r"<td>ETH Balance:\n<\/td>\n<td>\n(.+?)\n<\/td>"
            os.system("wget -O %s https://etherscan.io/address/%s" % (file_name2, contract_addr))
            value = run_re_file(re_str_value, file_name2)
        except Exception as e:
            pass
    return txs, value


def get_contract_stats(list_of_contracts):
    with open("concurr.csv", "w") as stats_file:
        fp = csv.writer(stats_file, delimiter=',')
        fp.writerow(["Contract address", "No. of paths", "No. of concurrency pairs", "Balance", "No. of TXs", "Note"])
        with open(list_of_contracts, "r") as f:
            for contract in f.readlines():
                contract_addr = contract.split()[0]
                value, txs = get_contract_info(contract_addr)
                fp.writerow([contract_addr, contract.split()[1], contract.split()[2],
                             value, txs, contract.split()[3:]])


def get_time_dependant_contracts(list_of_contracts):
    with open("time.csv", "w") as stats_file:
        fp = csv.writer(stats_file, delimiter=',')
        fp.writerow(["Contract address", "Balance", "No. of TXs", "Note"])
        with open(list_of_contracts, "r") as f:
            for contract in f.readlines():
                if len(contract.strip()) == 0:
                    continue
                contract_addr = contract.split(".")[0].split("_")[1]
                txs, value = get_contract_info(contract_addr)
                fp.writerow([contract_addr, value, txs])


def get_distinct_contracts(list_of_contracts = "concurr.csv"):
    flag = []
    with open(list_of_contracts, "rb") as csvfile:
        contracts = csvfile.readlines()[1:]
        n = len(contracts)
        for i in range(n):
            flag.append(i) # mark which contract is similar to contract_i
        for i in range(n):
            if flag[i] != i:
                continue
            contract_i = contracts[i].split(",")[0]
            npath_i = int(contracts[i].split(",")[1])
            npair_i = int(contracts[i].split(",")[2])
            file_i = "stats/tmp_" + contract_i + ".evm"
            six.print_(" reading file " + file_i)
            for j in range(i+1, n):
                if flag[j] != j:
                    continue
                contract_j = contracts[j].split(",")[0]
                npath_j = int(contracts[j].split(",")[1])
                npair_j = int(contracts[j].split(",")[2])
                if (npath_i == npath_j) and (npair_i == npair_j):
                    file_j = "stats/tmp_" + contract_j + ".evm"

                    with open(file_i, 'r') as f1, open(file_j, 'r') as f2:
                        code_i = f1.readlines()
                        code_j = f2.readlines()
                        if abs(len(code_i) - len(code_j)) >= 5:
                            continue
                        diff = difflib.ndiff(code_i, code_j)
                        ndiff = 0
                        for line in diff:
                            if line.startswith("+") or line.startswith("-"):
                                ndiff += 1
                        if ndiff < 10:
                            flag[j] = i
    six.print_(flag)

def run_command(cmd):
    FNULL = open(os.devnull, 'w')
    solc_p = subprocess.Popen(shlex.split(cmd), stdout=subprocess.PIPE, stderr=FNULL)
    return solc_p.communicate()[0].decode()


#Added by PG

def get_uncalled_blocks(blocks, visited_blocks):
    return list(set(blocks).difference(set(visited_blocks)))

'''
It returns the start address of the block received.

'''    
def getKey(block):
    return str(block.get_start_address())

def toInt(a):
    elem = a.split("_")
    if len(elem)>1:
        return int(elem[0])
    else:
        return int(a)

def getLevel(block):
    return block.get_depth_level()
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

def get_function_names(i,lineas):
    delimiter = "======"
    names = {}
    line = lineas[i]
    while line !="" and line.find(delimiter)==-1:
        parts = line.split(":")
        hash_code = parts[0].strip()
        fun_name = parts[1].strip()
        names[hash_code]=fun_name
        i+=1
        line = lineas[i]

    return i, names

'''
It returns a map that for each contract, it returns a list of pairs (hash, name_function).
Solidity file is a string that contains the name of the solidity file that is going to be analized.
'''
def process_hashes(solidity_file,solidity_version):
    
    solc = get_solc_executable(solidity_version)

    cmd = solc+" --hashes "+str(solidity_file)
        
    delimiter = "======="

    m = {}
    
    FNULL = open(os.devnull, 'w')
    solc_p = subprocess.Popen(shlex.split(cmd), stdout=subprocess.PIPE, stderr=FNULL)
    string = solc_p.communicate()[0].decode()
    lines = string.split("\n")
    i = 0
    while i < len(lines):
        line = lines[i]
        parts = line.strip().split()
        
        if parts!=[] and parts[0] == delimiter:
            cname = parts[1].split(":")[1]
            i, names = get_function_names(i+2,lines)
            m[cname] = names
        else:
            i+=1

    return m


def write_cfg(it,vertices,name = False,cloned = False):
    vert = sorted(vertices.values(), key = getKey)
    if costabs_folder not in os.listdir(tmp_path):
        os.mkdir(costabs_path)

    if not cloned:
        if it == None:
            name = costabs_path+"cfg_evm.cfg"
        elif name == False:
            name = costabs_path+"cfg_evm"+str(it)+".cfg"
        else:
            name = costabs_path+"cfg_"+name+".cfg"

    else:
        if it == None:
            name = costabs_path+"cfg_cloned_evm.cfg"
        elif name == False:
            name = costabs_path+"cfg__cloned_evm"+str(it)+".cfg"
        else:
            name = costabs_path+"cfg_"+name+"_cloned.cfg"
        
    with open(name,"w") as f:
        for block in vert:
            f.write("================\n")
            f.write("start address: "+ str(block.get_start_address())+"\n")
            f.write("end address: "+str(block.get_end_address())+"\n")
            f.write("end statement type: " + block.get_block_type()+"\n")

            f.write("jump target: " + " ".join(str(x) for x in block.get_list_jumps())+"\n")
            if(block.get_falls_to() != None):
                f.write("falls to: " +str(block.get_falls_to())+"\n")
            for instr in block.get_instructions():
                f.write(instr+"\n")
    f.close()

def cfg_dot(it,block_input,name = False,cloned = False):
    vert = sorted(block_input.values(), key = getKey)

    if costabs_folder not in os.listdir(tmp_path):
        os.mkdir(costabs_path)
    
    if not cloned:

        if it == None:
            name = costabs_path+"cfg.dot"
        elif name == False:
            name = costabs_path+"cfg"+str(it)+".dot"
        else:
            name = costabs_path+name+".dot"
    else:

        if it == None:
            name = costabs_path+"cfg_cloned.dot"
        elif name == False:
            name = costabs_path+"cfg_cloned_"+str(it)+".dot"
        else:
            name = costabs_path+name+"_cloned.dot"
        
    f = open(name,"w")
    tree = build_tree(vert[0],[("st",0)],block_input)
    tree.generatedot(f)
    f.close()

def update_map(m,key,val):
    l = m.get(key,[])
    l.append(val)
    m[key]=l
    return m

def store_times(oyente_time,ethir_time):
    f = open(costabs_path+"times.csv","a")
    fp = csv.writer(f, delimiter=',')
    fp.writerow(["Oyente",oyente_time,"EthIR",ethir_time])
    f.close()


def get_public_fields(source_file,arr = True):
    with open(source_file,"r") as f:
        lines = f.readlines()
        good_lines_aux = list(filter(lambda x: x.find("[]")!=-1 and x.find("public")!=-1,lines))
        good_lines = list(map(lambda x: x.split("//")[0],good_lines_aux))
        fields = list(map(lambda x: x.split()[-1].strip().strip(";"),good_lines))
    f.close()
    return fields

def update_sstore_map(state_vars,initial_name,compressed_name,isCompresed,position,compress_index,state):

    r_val = False
    if initial_name != '':
        if not isCompresed:
            #print compressed_name
            if initial_name != compressed_name:
                compressed = get_field_from_string(compressed_name,state)
                nn = compressed_name.split()
                r_val = (initial_name,nn[-1]) if nn != [] else (initial_name,initial_name)  
 
            state_vars[position] = initial_name
        else:
            name = str(position)+"_"+str(compress_index)

            if compress_index == 0:
                state_vars[name] = initial_name
            else:
                exist = state_vars.get(name, False)
                if (not exist) or (exist not in state):
                    st_name = get_field_from_string(compressed_name, state)
                    state_vars[name] = st_name

    return r_val

def compute_ccomponent(inverse_component, block):
    component = []
    for b in inverse_component.keys():
        if block in inverse_component[b]:
            component.append(b)

    return component

def get_field_from_string(string, state_variables):
    parts = string.split()

    i = 0
    st_name = ""
    found = False
    while(i<len(parts) and (not found)):
        if parts[i] in state_variables:
            st_name = parts[i]
            found = True
        i+=1
    return st_name

def correct_map_fields(candidate_fields,fields_map):
    for e in candidate_fields:
        (x,y) = candidate_fields[e]
        elem = fields_map.get(str(e)+"_0",False)
        if elem:
            fields_map[e] = elem
        else:
            pos = search_for_index(x,fields_map)

            if pos ==-1:
                fields_map[e] = x
            else:
                if not(str(pos).startswith(str(e))):
                    val = int(str(pos).split("_")[0])
                    f = y if e>val else x
                    fields_map[e] = f


def correct_map_fields1(fields_map,var_fields):
    correct = True
    i = 0
    offset=0
    fields_map_def = {}
    for e in fields_map:
        val = fields_map[e]
        fields_map_def[str(e)] = val

    del fields_map
    fields_map = fields_map_def
    
    while(i<len(var_fields) and correct):
        field = var_fields[i]
        pos = search_for_index(field,fields_map)

        if pos ==-1:
            fields_map[str(i)] = field
        else:
            if str(pos).split("_")[0] != str(i):
                correct = False
                offset = offset+1
        i=i+1

    while(i<len(var_fields)):
        number = search_greatter_compacts(pos,fields_map)

        if number !=0:
            offset = offset+number
        field = var_fields[i]

        potential_index = i-offset

        pos = exist_index(potential_index,fields_map)

        fields_map[str(pos)] = field

        i+=1

def search_greatter_compacts(pos,fields_map):
    
    numbers = fields_map.keys()
    pos_int = str(pos).split("_")[0]
    numbers_str = list(filter(lambda x: str(x).startswith(pos_int),numbers))
    end = list(filter(lambda x: str(x)>str(pos),numbers_str))
    if len(end)>0:
        if end[0] == pos_int+"_0":
            fields_map[pos_int+"_0"] = fields_map[pos_int]
            end.pop(0)
        
    return len(end)

def exist_index(potential_index,fields_map):
    numbers = fields_map.keys()
    numbers_str = list(filter(lambda x: str(x).startswith(str(potential_index)), numbers))
    
    if len(numbers_str)== 0:
        return potential_index
    else:
        numbers_str = list(map(lambda x: str(x), numbers_str))
        numbers_str.sort()
        return numbers_str[0]

def search_for_index(field,field_map):
    possible_values = []
    for e in field_map:
        if field == field_map[e]:
            possible_values.append(e)

    vals = list(map(lambda x: str(x), possible_values))
    vals.sort()
    if len(vals)!=0:
        return vals[0]
    else:
        return -1

def is_integer(num):
    try:
        val = int(num)
    except:
        val = -1

    return val


def get_push_value(elem):
    try:
        push_val, _ = elem
        return push_val
    except:
        return elem

# Added by AHC

def get_initial_block_address(elem):
    numbers = str(elem).split("_")
    return int(numbers[0])

def get_next_block_address(elem, index_dict):
    numbers = str(elem).split("_")
    idx = str(index_dict[int(numbers[0])])

    if len(numbers) == 1:
        numbers.append(idx)
    else:
        numbers[1] = idx
    return "_".join(numbers)

def check_if_not_cloned_address(elem):
    numbers = str(elem).split("_")
    return len(numbers) == 1

def get_idx_from_address(address):
    parts = address.split("_")
    idx = parts[1]
    return int(idx)


# Two stacks are equivalent if they share the same jump elements in the same positions
# of each stack. This function is used to return the same element if it is a jump element,
# or None otherwise. This is useful for applying a mask to compare two different stacks.
def mask_not_jump_elements(x, blocks_info):
    # An element is a jump element if it is a tuple (which means it comes from a PUSHx instruction),
    # its associated pushed value (x[0]) belongs to the set of blocks and it is not 0, as there's never
    # a jump to block 0 and this value tends to appear really often.
    if isinstance(x, tuple) and (x[0] in blocks_info) and x[0] != 0:
        return x[0]
    else:
        return None

# For checking if they are same stack, we just focus on
# tuples that contains a block address
def check_if_same_stack(stack1, stack2, blocks_info):
    s1_aux = list(map(lambda x: mask_not_jump_elements(x, blocks_info), stack1))
    s2_aux = list(map(lambda x: mask_not_jump_elements(x, blocks_info), stack2))
    # print "S1"
    # print s1_aux
    # print "S2"
    # print s2_aux
    return s1_aux == s2_aux

def show_graph(blocks_input):
    for address in blocks_input:
        print("Bloque: ")
        print (address)
        print("Comes from: ")
        print (blocks_input[address].get_comes_from())
        print("List jump: ")
        print (blocks_input[address].get_list_jumps())
        print("Jump target: ")
        print (blocks_input[address].get_jump_target())
        print("Falls to: ")
        print (blocks_input[address].get_falls_to())
        print("Filtered Stack: ")
        for stack in blocks_input[address].get_stacks():
            print (list(filter(lambda x: isinstance(x,tuple) and (x[0] in blocks_input) and x[0]!=0, stack)))
        print("Real stack:")
        print (blocks_input[address].get_stacks())
        

''' Given a node and where it comes from, checks all relevant info is consistent'''
def check_node_consistency(blocks_dict, initial_address, comes_from_address, visited_nodes):
    
    current_block = blocks_dict[initial_address]

    comes_from = current_block.get_comes_from()

    # List containing all the values checked
    conds = []
    
    # Always same condition: check if previous block is in comes_from list
    conds.append(comes_from_address in comes_from)
    
    if initial_address not in visited_nodes:
        
        t = current_block.get_block_type()

        jumps_to = current_block.get_jump_target()
        falls_to = current_block.get_falls_to()

        visited_nodes.append(initial_address)

        # Conditional jump: check comes_from + falls to node + jump target node
        if t == "conditional":

            conds.append(check_node_consistency(blocks_dict,falls_to, initial_address,visited_nodes))
            conds.append(check_node_consistency(blocks_dict,jumps_to, initial_address,visited_nodes))

            # print("conditional check")

       # Unconditional jump : check length of jump list + comes_from + 
       # jumps target is the element of jump list + jump target node +
       # falls_to == None
        elif t == "unconditional":

            jump_list = current_block.get_list_jumps()
            
            conds.append(len(jump_list) == 1)
            conds.append(jumps_to in jump_list)
            conds.append(check_node_consistency(blocks_dict,jumps_to, initial_address, visited_nodes))
            conds.append(falls_to == None)
            # print("Falls_to")
            # print(falls_to)

            # print("unconditional check")
        
        # Falls to node: check comes_from + next_node + jumps_to == None
        elif t == "falls_to":
            
            conds.append(check_node_consistency(blocks_dict, falls_to, initial_address, visited_nodes))
            conds.append(jumps_to == 0)

            # print("Jumps to")
            # print(jumps_to)

            # print("falls to check")
            
        # Terminal node: only check comes_from

        else:
            pass
            # print("terminal node to check")
        
    # If visited, as we've checked that node before, we just need to make sure
    # comes_from has current node.

    else:
        # print("already checked")
        pass
    # print(initial_address)
    # print(conds)
    return reduce(lambda i,j: i and j, conds)

''' Given a dictionary containing all blocks from graph, checks if all the info
is coherent '''
def check_graph_consistency(blocks_dict, initial_address = 0):
    visited_nodes = [initial_address]
    initial_block = blocks_dict[initial_address]

    t = initial_block.get_block_type()

    jumps_to = initial_block.get_jump_target()
    falls_to = initial_block.get_falls_to()

    conds = []

    # Conditional jump: call check_node with falls_to && jump_target && all visited nodes are blocks
    # are the ones in block_dict
    if t == "conditional":
         
         conds.append(check_node_consistency(blocks_dict,falls_to, initial_address,visited_nodes))
         conds.append(check_node_consistency(blocks_dict,jumps_to, initial_address,visited_nodes))
         
         # print("initial node: conditional")
         
    # Unconditional jump : check length of jump list && comes_from && 
    # jumps target is the element of jump list && jump target node &&
    # falls_to == None
    elif t == "unconditional":
         
         jump_list = current_block.get_list_jumps()
         
         conds.append(len(jumps_list) == 1)
         conds.append(jumps_to in jump_list)
         conds.append(check_node_consistency(blocks_dict,jumps_to, initial_address, visited_nodes))
         conds.append(falls_to == None)

         # print("initial node: unconditional")
         
    # Falls to node: visited nodes == blocks_dict.keys && check  next_node  && jumps_to == None
    elif t == "falls_to":
        
         conds.append(check_node_consistency(blocks_dict, falls_to, initial_address, visited_nodes))
         conds.append(jumps_to == 0)
         
         # print("initial node: falls to")
         
    # Terminal node: only check there's no other block
    else:
         pass
         # print("initial Node: terminal node")

    # Check all visited nodes are the same in the dictionary

    conds.append(visited_nodes.sort() == blocks_dict.keys().sort())

    # print(conds)
    
    return reduce(lambda i,j: i and j, conds)


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
    opcodes = []

    ops = instructions.split(" ")
    i = 0
    while(i<len(ops)):
        op = ops[i]
        if not op.startswith("PUSH"):
            opcodes.append(op.strip())
        else:
            val = ops[i+1]
            opcodes.append(op+" "+val)
            i=i+1
        i+=1

    f.close()
    
    return opcodes,input_stack

def all_integers(variables):
    int_vals = []
    try:
        for v in variables:
            x = int(v)
            int_vals.append(x)
        return True, int_vals
    except:
        return False,variables

def all_symbolic(variables):
    for v in variables:
        try:
            x = int(v)
            return False
        except:
            sym = True
    return True
# '''
# It computes the index of each state variable to know its solidity name
# state variable is a list with the state variables g0..gn
# '''
# def process_name_state_variables(state_variables,source_map):
#     index_state_variables = {}
#     i = 1
#     prev_var = state_variables[0]
#     while(i < len(state_variables)):


# Given a string, returns closing parentheses index that closes first parenthese,
# assuming parentheses are well-placed.
def find_first_closing_parentheses(string):
    idx_ini = string.find("(") + 1
    filtered_string = string[idx_ini:]
    cont = 1
    while cont > 0:
        opening_index = filtered_string.find("(")
        closing_index = filtered_string.find(")")
        if opening_index == -1:
            return idx_ini + closing_index
        elif opening_index < closing_index:
            cont = cont+1
            idx_ini = idx_ini + opening_index + 1
            filtered_string = filtered_string[opening_index+1:]
        else:
            cont = cont-1
            if cont == 0:
                return idx_ini + closing_index
            else:
                idx_ini = idx_ini + closing_index + 1
                filtered_string = filtered_string[closing_index+1:]
    raise ValueError("Parentheses are not consistent")

def get_solc_executable(version):
    if version == "v4":
        return "solc"
    elif version == "v5":
        return "solcv5"
    elif version == "v6":
        return "solcv6"
    elif version == "v7":
        return "solcv7"
    elif version == "v8":
        return "solcv8"


def distinct_ebso(a,b):
    try:
        int_a = int(a)
        int_b = int(b)
        return int_a != int_b

    except:
        if a.find(b)!=-1 or b.find(a)!=-1:
            return True
        else:
            return False

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
