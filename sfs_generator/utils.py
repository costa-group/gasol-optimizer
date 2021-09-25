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
