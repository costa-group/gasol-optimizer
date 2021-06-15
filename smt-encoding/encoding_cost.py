from encoding_utils import *
from encoding_files import write_encoding
from utils_bckend import generate_generic_push_instruction

# Soft constraints

# Label name for soft constraints
label_name = 'gas'

# Bool name for encoding a previous solution
previous_solution_var = 'b'


def generate_previous_solution_statement(b0, theta_dict, instr_seq):
    instr_seq_with_generic_push = list(map(generate_generic_push_instruction, instr_seq))
    and_variables = []
    for i, instr in enumerate(instr_seq_with_generic_push):
        and_variables.append(add_eq(t(i), theta_dict[instr]))
    for i in range(len(instr_seq_with_generic_push), b0):
        and_variables.append(add_eq(t(i), theta_dict['NOP']))
    write_encoding(add_assert(add_eq(previous_solution_var, add_and(*and_variables))))


# Generates the soft constraints contained in the paper.
def paper_soft_constraints(b0, bs, user_instr, theta_dict, is_barcelogic=False, instr_seq=None, previous_solution_weight=-1):
    if instr_seq is None:
        instr_seq = []
    write_encoding("; Soft constraints from paper")
    instr_costs = generate_costs_ordered_dict(bs, user_instr, theta_dict)
    disjoin_sets = generate_disjoint_sets_from_cost(instr_costs)
    previous_cost = 0
    or_variables = []
    bool_variables = []
    if previous_solution_weight != -1:
        bool_variables.append(previous_solution_var)
        write_encoding(declare_boolvar(previous_solution_var))
        generate_previous_solution_statement(b0, theta_dict, instr_seq)
        write_encoding(add_assert_soft(add_not(previous_solution_var), previous_solution_weight, label_name,
                                       is_barcelogic))
    for gas_cost in disjoin_sets:
        # We skip the first set of instructions, as they have
        # no soft constraint associated. Neverthelss, we add
        # opcodes with cost 0 to the set of variables till p
        if gas_cost == 0:
            for instr in disjoin_sets[gas_cost]:
                or_variables.append(instr)
            continue

        wi = gas_cost - previous_cost

        # Before adding current associated opcodes, we generate
        # the constraints for each tj.
        for j in range(b0):
            write_encoding(add_assert_soft(add_or(*[*bool_variables, *list(map(lambda var: add_eq(t(j), var), or_variables))]),
                                           wi, label_name, is_barcelogic))
        for instr in disjoin_sets[gas_cost]:
            or_variables.append(instr)

        # We update previous_cost
        previous_cost = gas_cost


# Method for generating an alternative model for soft constraints. This method is similar to the previous one,
# but instead it is based on inequalities and shorter constraints. See new paper for more details
def alternative_soft_constraints(b0, bs, user_instr, theta_dict, is_barcelogic=False):
    write_encoding("; Alternative soft constraints model")
    instr_costs = generate_costs_ordered_dict(bs, user_instr, theta_dict)

    # For every instruction and every position in the sequence, we add a soft constraint
    for theta_instr, gas_cost in instr_costs.items():
        if gas_cost == 0:
            continue

        for j in range(b0):
            write_encoding(add_assert_soft(add_not(add_eq(t(j), theta_instr)), gas_cost, label_name, is_barcelogic))


# Method for generating the soft constraints in which the number of instructions is minimized.
# As we want to minimize the number of instructions, it is equivalent to state that we want to maximize
# the number of NOP instructions. Therefore, it can be easily encoded.
# Note that this does not imply gas optimality, there are some examples that contradict this claim.
# For instance, CALLVALUE CALLVALUE and CALLVALUE DUP1 share the same number of instructions, but the first one
# is optimal whereas the second is not.
def number_instructions_soft_constraints(b0, theta_nop, is_barcelogic):
    write_encoding("; Soft constraints for optimizing the number of instructions")

    for j in range(b0):
        write_encoding(add_assert_soft(add_eq(t(j), theta_nop), 1, label_name, is_barcelogic))