import copy
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

def is_hex(s):
    try:
        int(s, 16)
        return True
    except ValueError:
        return False

def compute_final_stack_from_solution(initial_stack, user_instr, instr_seq):
    final_stack = copy.deepcopy(initial_stack)
    for instr in instr_seq:
        if is_hex(instr):
            final_stack.insert(0, int(instr, 16))
        elif instr.startswith("SWAP"):
            index = int(instr.lstrip("SWAP"))
            final_stack[0], final_stack[index] = final_stack[index], final_stack[0]
        elif instr.startswith("DUP"):
            index = int(instr.lstrip("DUP"))
            final_stack.insert(0, final_stack[index - 1])
        elif instr.startswith("POP"):
            final_stack.pop(0)
        else:
            current_instrs = list(filter(lambda x: x['id'].startswith(instr), user_instr))
            correct_instr = False
            for current_instr in current_instrs:
                if current_instr['commutative']:
                    inpt_stack = current_instr['inpt_sk']
                    if (inpt_stack[0] != final_stack[0] or inpt_stack[1] != final_stack[1]) and\
                            (inpt_stack[0] != final_stack[0] or inpt_stack[1] != final_stack[1]):
                        continue
                    else:
                        final_stack.pop(0)
                        final_stack.pop(0)
                        correct_instr = True
                else:
                    all_right = True
                    for i, stack_elem in enumerate(current_instr['inpt_sk']):
                        if stack_elem != final_stack[i]:
                            all_right = False
                            break
                    if all_right:
                        for _ in current_instr['inpt_sk']:
                            final_stack.pop(0)
                        correct_instr = True
                if not correct_instr:
                    continue
                if current_instr['outpt_sk']:
                    final_stack.insert(0, current_instr['outpt_sk'][0])

            if not correct_instr:
                raise ValueError("No instruction matches " + str(current_instrs) + " with stack " + str(final_stack))
    return final_stack

