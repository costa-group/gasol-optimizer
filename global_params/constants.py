beginning_block = {"tag", "JUMPDEST"}

end_block = {"JUMP","JUMPI","STOP","RETURN","REVERT","INVALID","SELFDESTRUCT"}

split_block = {"LOG0","LOG1","LOG2","LOG3","LOG4","CALLDATACOPY","CODECOPY","EXTCODECOPY","RETURNDATACOPY",
               "CALL","STATICCALL","DELEGATECALL","CREATE","CREATE2","ASSIGNIMMUTABLE", "GAS"}

store_instructions = {"SSTORE","MSTORE","MSTORE8"}

# We set the maximum k dup and swap instructions
# can have.

max_k_dup = 16
max_k_swap = 16

# Maximum size integers have in the EVM

int_limit = 2**256

# Flag to consider PUSH0 opcode in the optimization process
push0_enabled = True


def append_store_instructions_to_split():
    global split_block
    split_block = split_block.union(store_instructions)


def _set_push0(val: bool) -> None:
    global push0_enabled
    push0_enabled = val
