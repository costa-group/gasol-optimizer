import opcodes 

'''
It takes the name of a file containing the optimized version of a
block and extracts the id of the block from the name of the file.
'''

def get_block_id(file_name):

    p = file_name.find("block")
    end = file_name.find("_",p)

    block_id = file_name[p:end]

    print(block_id)
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
    print(opcodes_list)
    for op in opcodes_list:
        if op == "MULMOD":
            gas = 10
        else:
            gas = opcodes.get_syrup_cost(op.strip())
        val+=gas
    return val
