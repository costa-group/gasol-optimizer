import sfs_generator.opcodes as opcodes

'''
It takes the name of a file containing the optimized version of a
block and extracts the id of the block from the name of the file.
'''

def get_block_id(file_name):

    p = file_name.find("block")
    end = file_name.find("_",p)

    block_id = file_name[p:end]

    return block_id

def get_contract_name(file_name):
    elems = file_name.split("_")
    if elems[2].startswith("block"):
        return elems[1]
    else:
        raise Exception("Check contract name")

def is_integer(num):
    try:
        val = int(num)
        return True
    except:
        return False

def get_block_cost(opcodes_list):
    val = 0
    for op in opcodes_list:
        if op == "MULMOD":
            gas = 10
        else:
            gas = opcodes.get_ins_cost(op.strip())
        val+=gas
    return val

def compute_clousure(deps):
    clousure = {}
    for e in deps:
        f = e[0]
        visited = compute_clousure_dir(f,deps,[])
        clousure[f] = visited

    sol = []
    for f in clousure:
        pairs = list(map(lambda x: (f,x), clousure[f]))
        sol+=pairs
        
    return sol

def compute_clousure_dir(v,deps,visited):
    candidates = list(filter(lambda x: x[0] == v, deps))
    for c in candidates:
        if c[1] not in visited:
            visited.append(c[1])
            compute_clousure_dir(c[1],deps,visited)
    return visited
