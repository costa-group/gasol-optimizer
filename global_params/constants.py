split_block = {"LOG0","LOG1","LOG2","LOG3","LOG4","CALLDATACOPY","CODECOPY","EXTCODECOPY","RETURNDATACOPY",
               "CALL","STATICCALL","DELEGATECALL","CREATE","CREATE2","ASSIGNIMMUTABLE"}

store_instructions = {"SSTORE","MSTORE","MSTORE8"}

def append_store_instructions_to_split():
    global split_block

    split_block = split_block + store_instructions