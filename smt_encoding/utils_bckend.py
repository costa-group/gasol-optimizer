import re
# Miscellanea methods

# We add a | | to string variables, as these variables are usually
# of the form s(i) and SMT-Lib cannot accept those names. If it
# is numeric, no bars are added.

def add_bars_and_index_to_string(string, idx=0):
    if type(string) == str:
        if idx == 0:
            return '|' + str(string) + '|'
        else:
            # We obtain number from the string and replace it by summing idx
            new_number = int(re.search('\d+', string).group()) + idx
            return '|' + re.sub("\d+", str(new_number), string) + "|"
    else:
        return string


# Given a string, we return the string PUSH if the string is
# of the form PUSHx, or returns the same string otherwise.
def generate_generic_push_instruction(string):
    if string.startswith('PUSH'):
        return 'PUSH'
    return string