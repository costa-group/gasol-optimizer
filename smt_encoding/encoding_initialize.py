import global_params.constants as constants
from smt_encoding.encoding_files import write_encoding
from smt_encoding.encoding_utils import a, add_eq, l, t, u, x
from smt_encoding.smtlib_utils import (add_and, add_assert, add_not,
                                       declare_boolvar, declare_intvar)

# Methods for initializing the variables

def initialize_s_vars(variables):
    s_vars = [declare_intvar(var) for var in variables]
    return s_vars


def initialize_u_vars(bs, b0, initial_idx=0):
    u_vars = [declare_boolvar(u(i,j)) for i in range(bs) for j in range(initial_idx, b0+1+initial_idx)]
    return u_vars


def initialize_x_vars(bs, b0, initial_idx=0):
    x_vars = [declare_intvar(x(i,j)) for i in range(bs) for j in range(initial_idx, b0+1+initial_idx)]
    return x_vars


def initialize_t_vars(b0, initial_idx=0):
    t_vars = [declare_intvar(t(i)) for i in range(initial_idx, b0+initial_idx)]
    return t_vars


def initialize_a_vars(b0, initial_idx=0):
    a_vars = [declare_intvar(a(i)) for i in range(initial_idx, b0+initial_idx)]
    return a_vars

def initialize_l_vars(l_theta_values):
    l_vars = [declare_intvar(l(theta_value)) for theta_value in l_theta_values]
    return l_vars


def initialize_variables(variables, bs, b0, theta_mem, initial_idx=0):
    write_encoding(*initialize_s_vars(variables))
    write_encoding(*initialize_u_vars(bs, b0, initial_idx))
    write_encoding(*initialize_x_vars(bs, b0, initial_idx))
    write_encoding(*initialize_t_vars(b0, initial_idx))
    write_encoding(*initialize_a_vars(b0, initial_idx))
    write_encoding(*initialize_l_vars(theta_mem.values()))


# Method for generating variable assignment (SV)

def variables_assignment_constraint(variables, initial_idx=0):
    write_encoding("; Variables assignment")
    for i, var in enumerate(variables):
        statement = add_eq(var, constants.int_limit + i + initial_idx)
        write_encoding(add_assert(statement))


# Methods for defining how the stack at the beginning is (B)

def initial_stack_encoding(initial_stack, bs, initial_idx=0):
    write_encoding("; Initial stack constraints")

    for alpha, variable in enumerate(initial_stack):
        write_encoding(add_assert(add_and(u(alpha, initial_idx), add_eq(x(alpha, initial_idx), variable))))

    for beta in range(len(initial_stack), bs):
        write_encoding(add_assert(add_not(u(beta, initial_idx))))


# Methods for defining how the stack at the end is (E)


def final_stack_encoding(final_stack, bs, b0, initial_idx=0):
    write_encoding("; Final stack constraints")

    for alpha, variable in enumerate(final_stack):
        write_encoding(add_assert(add_and(u(alpha, b0+initial_idx), add_eq(x(alpha, b0+initial_idx), variable))))

    for beta in range(len(final_stack), bs):
        write_encoding(add_assert(add_not(u(beta, b0+initial_idx))))
