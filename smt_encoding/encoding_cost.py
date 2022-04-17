import collections
import re

from smt_encoding.encoding_files import write_encoding
import smt_encoding.encoding_utils as encoding_utils
from smt_encoding.encoding_utils import (a, generate_disjoint_sets_from_cost, t)
from smt_encoding.smtlib_utils import (add_and, add_assert, add_assert_soft,
                                       add_eq, add_leq, add_lt, add_not,
                                       add_or)
from smt_encoding.utils_bckend import generate_generic_push_instruction
import itertools

# Soft constraints

# Label name for soft constraints
label_name = 'gas'

# Bool name for encoding a previous solution
previous_solution_var = 'b'

def generate_size_costs_ordered_dict(theta_dict_instr):
    nop_dict = {theta_dict_instr["NOP"] : 0}
    push_dict = {theta_dict_instr[instr_id] : 5  for instr_id in filter(lambda x: x.startswith("PUSH") or x.startswith("ASSIGNIMMUTABLE"), theta_dict_instr.keys())}
    non_push_dict = {theta_dict_instr[instr_id] : 1 for instr_id in set(theta_dict_instr.keys()).difference(set(nop_dict.keys()).union(set(push_dict.keys())))}
    instr_costs = dict(itertools.chain(non_push_dict.items(), push_dict.items(), nop_dict.items()))
    return collections.OrderedDict(sorted(instr_costs.items(), key=lambda x: x[1]))


def generate_gas_costs_ordered_dict(user_instr, theta_dict):
    basic_costs = {theta_dict["PUSH"]: 3, theta_dict["POP"]: 2, theta_dict["NOP"]: 0}
    swap_costs = {theta_dict[instr_id] : 3 for instr_id in filter(lambda instr_id: instr_id.startswith("SWAP") ,
                                                                  theta_dict.keys())}
    dup_costs = {theta_dict[instr_id]: 3 for instr_id in
                  filter(lambda instr_id: instr_id.startswith("DUP"), theta_dict.keys())}
    instr_costs = dict(itertools.chain(basic_costs.items(), swap_costs.items(), dup_costs.items()))
    for instr in user_instr:
        instr_costs[theta_dict[instr['id']]] = instr['gas']
    return collections.OrderedDict(sorted(instr_costs.items(), key=lambda x: x[1]))


# Method for generating an alternative model for soft constraints. This method is similar to the previous one,
# but instead it is based on inequalities and shorter constraints. See new paper for more details
def direct_soft_constraints(instr_costs, first_position_dict, last_position_dict, is_barcelogic=False):
    # For every instruction and every position in the sequence, we add a soft constraint
    for theta_instr, size_cost in instr_costs.items():
        if size_cost == 0:
            continue

        for j in range(first_position_dict[theta_instr], last_position_dict[theta_instr]):
            write_encoding(add_assert_soft(add_not(add_eq(t(j), theta_instr)), size_cost, label_name, is_barcelogic))


def _select_by_position(j, variables, first_position_dict, last_position_dict):
    return list(filter(lambda var_theta: first_position_dict[var_theta] <= j < last_position_dict[var_theta] , variables))


def generate_or_constraints_with_bounds(or_variables, first_position_dict, last_position_dict, wi, is_barcelogic=False):
    min_index = max(map(lambda theta_instr: first_position_dict[theta_instr], or_variables))
    max_index = min(map(lambda theta_instr: last_position_dict[theta_instr], or_variables))

    for j in range(min_index, max_index):
        possible_theta_instr = _select_by_position(j, or_variables, first_position_dict, last_position_dict)
        write_encoding(add_assert_soft(add_or(*map(lambda var: add_eq(t(j), var), possible_theta_instr)),
                                       wi, label_name, is_barcelogic))


# Generates the soft constraints contained in the paper.
def group_soft_constraints(instr_costs, first_position_dict, last_position_dict, is_barcelogic=False):
    disjoin_sets = generate_disjoint_sets_from_cost(instr_costs)
    previous_cost = 0
    or_variables = []

    for gas_cost in disjoin_sets:
        # We skip the first set of instructions, as they have
        # no soft constraint associated. Nevertheless, we add
        # opcodes with cost 0 to the set of variables till p
        if gas_cost == 0:
            for instr in disjoin_sets[gas_cost]:
                or_variables.append(instr)
            continue

        wi = gas_cost - previous_cost

        # Before adding current associated opcodes, we generate
        # the constraints for each tj.
        generate_or_constraints_with_bounds(or_variables, first_position_dict, last_position_dict, wi, is_barcelogic)

        for instr in disjoin_sets[gas_cost]:
            or_variables.append(instr)

        # We update previous_cost
        previous_cost = gas_cost


def gas_group_constraints(user_instr, theta_instr, first_position_dict, last_position_dict, is_barcelogic = False):
    gas_instr_costs = generate_gas_costs_ordered_dict(user_instr, theta_instr)
    group_soft_constraints(gas_instr_costs, first_position_dict, last_position_dict, is_barcelogic)


def gas_direct_constraints(user_instr, theta_instr, first_position_dict, last_position_dict, is_barcelogic = False):
    gas_instr_costs = generate_gas_costs_ordered_dict(user_instr, theta_instr)
    direct_soft_constraints(gas_instr_costs, first_position_dict, last_position_dict, is_barcelogic)


def size_group_constraints(theta_instr, first_position_dict, last_position_dict, is_barcelogic = False):
    size_instr_costs = generate_size_costs_ordered_dict(theta_instr)
    group_soft_constraints(size_instr_costs, first_position_dict, last_position_dict, is_barcelogic)


def size_direct_constraints(theta_instr, first_position_dict, last_position_dict, is_barcelogic = False):
    size_instr_costs = generate_size_costs_ordered_dict(theta_instr)
    direct_soft_constraints(size_instr_costs, first_position_dict, last_position_dict, is_barcelogic)


def generate_previous_solution_statement(b0, theta_dict, instr_seq):
    instr_seq_with_generic_push = list(map(generate_generic_push_instruction, instr_seq))
    and_variables = []
    for i, instr in enumerate(instr_seq_with_generic_push):
        and_variables.append(add_eq(t(i), theta_dict[instr]))
    for i in range(len(instr_seq_with_generic_push), b0):
        and_variables.append(add_eq(t(i), theta_dict['NOP']))
    write_encoding(add_assert(add_eq(previous_solution_var, add_and(*and_variables))))


def generate_statement_from_previous_solutions(b0, theta_dict, instr_seq):
    and_variables = []
    for i, element in enumerate(instr_seq):
        if type(element) == int:
            and_variables.append(add_and(add_eq(t(i), theta_dict["PUSH"]), add_eq(a(i), element)))
        else:
            and_variables.append(add_eq(t(i), theta_dict[element]))
    for i in range(len(instr_seq), b0):
        and_variables.append(add_eq(t(i), theta_dict['NOP']))
    return add_and(*and_variables)


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
        # bool_variables.append(previous_solution_var)
        # write_encoding(declare_boolvar(previous_solution_var))
        # generate_previous_solution_statement(b0, theta_dict, instr_seq)
        # write_encoding(add_assert_soft(add_not(previous_solution_var), previous_solution_weight, label_name, is_barcelogic))
        write_encoding(add_assert_soft(generate_statement_from_previous_solutions(b0, theta_dict, instr_seq), 1, label_name, is_barcelogic))

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


# Method for generating the soft constraints in which the size of the bytecode is minimized.
# NOP instructions have a 0 cost associated, PUSH-related instructions have a size of 2 associated,
# and the remaining ones have cost 1 associated
def byte_size_soft_constraints_simple(b0, usr_instr, theta_dict, is_barcelogic=False):
    instr_costs = generate_size_cost(theta_dict)
    disjoin_sets = generate_disjoint_sets_from_cost(instr_costs)

    previous_cost = 0
    or_variables = []
    bool_variables = []

    write_encoding("; Soft constraints for optimizing the size of the opcodes in bytes")

    for gas_cost in disjoin_sets:
        # We skip the first set of instructions, as they have
        # no soft constraint associated. Nevertheless, we add
        # opcodes with cost 0 to the set of variables till p
        if gas_cost == 0:
            for instr in disjoin_sets[gas_cost]:
                or_variables.append(instr)
            continue

        wi = gas_cost - previous_cost

        # Before adding current associated opcodes, we generate
        # the constraints for each tj.
        for j in range(b0):
            write_encoding(
                add_assert_soft(add_or(*[*bool_variables, *list(map(lambda var: add_eq(t(j), var), or_variables))]),
                                wi, label_name, is_barcelogic))
        for instr in disjoin_sets[gas_cost]:
            or_variables.append(instr)

        # We update previous_cost
        previous_cost = gas_cost


def byte_cost_yul_operations(theta_id, theta_value):
    if theta_id == "NOP":
        return theta_value, 0
    elif theta_id.startswith("ASSIGNIMMUTABLE"):
        return theta_value, 36
    elif not theta_id.startswith("PUSH") or theta_id.startswith("tag"):
        return theta_value, 1
    elif theta_id.startswith("PUSH#[$]") or theta_id.startswith("PUSHSIZE") \
            or theta_id.startswith("PUSHDATA") or theta_id.startswith("PUSH[$]") or theta_id.startswith("PUSHTAG"):
        return theta_value, 5
    elif theta_id.startswith("PUSHLIB") or theta_id.startswith("PUSHDEPLOYADDRESS"):
        return theta_value, 21
    elif theta_id.startswith("PUSHIMMUTABLE"):
        return theta_value, 32


def generate_statement_for_push(j, idx, theta_push):
    if idx == 1:
        lb = 0
    else:
        lb = 1 << (8 * (idx - 1))
    ub = (1 << (8 * idx))
    return add_and(add_eq(t(j), theta_push), add_leq(lb, a(j)), add_lt(a(j), ub))

# Method for generating the soft constraints in which the size of the bytecode is minimized.
# NOP instructions have a 0 cost associated, PUSH-related instructions have a size of 2 associated,
# and the remaining ones have cost 1 associated
def byte_size_soft_constraints_complex(b0, theta_dict, is_barcelogic=False):
    byte_tuples = filter(lambda x: x is not None, [byte_cost_yul_operations(theta_id, theta_value) for theta_id, theta_value in theta_dict.items()])
    cost_dict = dict(byte_tuples)
    for i in range(1, 33):
        cost_dict['PUSH' + str(i)] = i + 1
    ordered_cost_dict = collections.OrderedDict(sorted(cost_dict.items(), key=lambda t: t[1]))
    disjoin_sets = dict(generate_disjoint_sets_from_cost(ordered_cost_dict))
    previous_cost = 0
    or_variables = []
    push_instructions = []

    write_encoding("; Soft constraints for optimizing the size of the opcodes in bytes")

    for gas_cost in disjoin_sets:
        # We skip the first set of instructions, as they have
        # no soft constraint associated. Nevertheless, we add
        # opcodes with cost 0 to the set of variables till p
        if gas_cost == 0:
            for instr in disjoin_sets[gas_cost]:
                if type(instr) == int:
                    or_variables.append(instr)
                else:
                    push_match = re.match(re.compile("PUSH([0-9]+)"), instr)
                    push_instructions.append(int(push_match.group(1)))
            continue

        wi = gas_cost - previous_cost

        # Before adding current associated opcodes, we generate
        # the constraints for each tj.
        for j in range(b0):
            or_statements = list(map(lambda var: add_eq(t(j), var), or_variables))
            push_statements = list(map(lambda idx: generate_statement_for_push(j, idx, theta_dict["PUSH"]), push_instructions))
            write_encoding(
                add_assert_soft(add_or(*[*push_statements, *or_statements]),
                                wi, label_name, is_barcelogic))

        for instr in disjoin_sets[gas_cost]:
            if type(instr) == int:
                or_variables.append(instr)
            else:
                push_match = re.match(re.compile("PUSH([0-9]+)"), instr)
                push_instructions.append(int(push_match.group(1)))

        # We update previous_cost
        previous_cost = gas_cost