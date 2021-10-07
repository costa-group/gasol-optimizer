from encoding_utils import *
from encoding_files import write_encoding

# Methods for generating the constraints for both memory and storage (Ls)

def _mem_variable_equivalence_constraint(j, theta_store):
    left_term = add_eq(t(j), theta_store)
    right_term = add_eq(l(theta_store), j)
    write_encoding(add_assert(add_eq(left_term, right_term)))


# Note that the instructions must verify store1 < store2
def _store_store_order_constraint(theta_store1, theta_store2):
    write_encoding(add_assert(add_lt(l(theta_store1), l(theta_store2))))


# Note that the instructions must verify store < load
def _store_load_order_constraint(j, theta_store, theta_load):
    left_term = add_eq(t(j), theta_load)
    right_term = add_lt(l(theta_store), j)
    write_encoding(add_assert(add_implies(left_term, right_term)))


# Note that the instructions must verify load < store
def _load_store_order_constraint(j, theta_load, theta_store):
    left_term = add_eq(t(j), theta_load)
    right_term = add_lt(j, l(theta_store))
    write_encoding(add_assert(add_implies(left_term, right_term)))


def memory_model_constraints(b0, order_tuples, theta_dict, theta_mem, initial_idx=0):
    initial_possible_idx = initial_idx
    final_possible_idx = b0 + initial_idx

    write_encoding("; Memory constraints using l variables for stores")
    for _, theta_store in theta_mem.items():
        write_encoding(add_assert(add_and(add_leq(initial_possible_idx, l(theta_store)), add_lt(l(theta_store), final_possible_idx))))
        for j in range(initial_possible_idx, final_possible_idx):
            _mem_variable_equivalence_constraint(j, theta_store)

    # Order tuples contains those elements that are related
    for el1, el2 in order_tuples:

        # In order to identify which constraint must be applied, we check whether each element
        # is a store or not (i.e. it belongs to the keys of theta mem)
        is_store_1 = el1 in theta_dict.keys()
        is_store_2 = el2 in theta_dict.keys()

        theta_val_1 = theta_dict[el1]
        theta_val_2 = theta_dict[el2]

        if is_store_1:
            # Case Store-Store:
            if is_store_2:
                _store_store_order_constraint(theta_val_1, theta_val_2)
            # Case Store-Load:
            else:
                for j in range(initial_possible_idx, final_possible_idx):
                    _store_load_order_constraint(j, theta_val_1, theta_val_2)
        # Case Load-Store:
        else:
            for j in range(initial_possible_idx, final_possible_idx):
                _load_store_order_constraint(j, theta_val_1, theta_val_2)


def memory_model_constraints_l_variables_store(b0, order_tuples, theta_dict, theta_mem, initial_idx=0):
    initial_possible_idx = initial_idx
    final_possible_idx = b0 + initial_idx

    write_encoding("; Memory constraints using l variables for stores")
    for _, theta_store in theta_mem.items():
        write_encoding(add_assert(add_and(add_leq(initial_possible_idx, l(theta_store)), add_lt(l(theta_store), final_possible_idx))))
        for j in range(initial_possible_idx, final_possible_idx):
            _mem_variable_equivalence_constraint(j, theta_store)

    # Order tuples contains those elements that are related
    for el1, el2 in order_tuples:

        # In order to identify which constraint must be applied, we check whether each element
        # is a store or not (i.e. it belongs to the keys of theta mem)
        is_store_1 = el1 in theta_dict.keys()
        is_store_2 = el2 in theta_dict.keys()

        theta_val_1 = theta_dict[el1]
        theta_val_2 = theta_dict[el2]

        if is_store_1:
            # Case Store-Store:
            if is_store_2:
                _store_store_order_constraint(theta_val_1, theta_val_2)
            # Case Store-Load:
            else:
                for j in range(initial_possible_idx, final_possible_idx):
                    _store_load_order_constraint(j, theta_val_1, theta_val_2)
        # Case Load-Store:
        else:
            for j in range(initial_possible_idx, final_possible_idx):
                _load_store_order_constraint(j, theta_val_1, theta_val_2)