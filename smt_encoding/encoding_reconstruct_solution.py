from encoding_utils import *
from encoding_files import write_encoding


# Given a list that contains info from the sequence, transforms it into
# their corresponding constraints. This list is of the form [el_0, el_1, ..., el_n]
# where el_i could be a number > 0 or a negative number <= 0. In the first case, the number
# corresponds to the theta value of the corresponding instruction t_i. In the former one,
# it corresponds to the negative value that it's pushed (note that pushed values are between 0 and 2**256-1).
def generate_encoding_from_log_json_dict(sequence_dict, initial_idx=0):
    for pos, value in enumerate(sequence_dict):
        # If it's > 0, we just encode the theta value.
        if value > 0:
            write_encoding(add_assert(add_eq(t(int(pos) + initial_idx), value)))
        # If it's <= 0, then we know the corresponding theta value is 0, and aj is equal to -value.
        else:
            write_encoding(add_assert(add_eq(a(int(pos) + initial_idx), -value)))
            write_encoding(add_assert(add_eq(t(int(pos)+initial_idx), 0)))
