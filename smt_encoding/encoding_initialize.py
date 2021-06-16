from encoding_files import write_encoding
from encoding_utils import *

# Methods for initializing the variables

def _initialize_s_vars(variables):
    for var in variables:
        write_encoding(declare_intvar(var))


def _initialize_u_vars(bs, b0, initial_idx=0):
    for i in range(bs):
        for j in range(initial_idx, b0+1+initial_idx):
            write_encoding(declare_boolvar(u(i,j)))


def _initialize_x_vars(bs, b0, initial_idx=0):
    for i in range(bs):
        for j in range(initial_idx, b0+1+initial_idx):
            write_encoding(declare_intvar(x(i,j)))


def _initialize_t_vars(b0, initial_idx=0):
    for i in range(initial_idx, b0+initial_idx):
        write_encoding(declare_intvar(t(i)))


def _initialize_a_vars(b0, initial_idx=0):
    for i in range(initial_idx, b0+initial_idx):
        write_encoding(declare_intvar(a(i)))


def initialize_variables(variables, bs, b0, initial_idx=0):
    _initialize_s_vars(variables)
    _initialize_u_vars(bs, b0, initial_idx)
    _initialize_x_vars(bs, b0, initial_idx)
    _initialize_t_vars(b0, initial_idx)
    _initialize_a_vars(b0, initial_idx)


# Method for generating variable assignment (SV)

def variables_assignment_constraint(variables, initial_idx=0):
    write_encoding("; Variables assignment")
    for i, var in enumerate(variables):
        statement = add_eq(var, int_limit + i + initial_idx)
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
