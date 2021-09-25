# Statistics utils

# Adapted directly from https://github.com/ethereum/solidity/blob/develop/libsolutil/Numeric.h
# Returns the number of bytes needed for encoding a number. Used for determining x in PUSHx instructions
def number_encoding_size(number):
    i = 0
    while number != 0:
        i += 1
        number = number >> 8
    return i