"""
Generates the shuffling for the stacks in the running example
"""
import itertools
import json
import sys
from pathlib import Path
from typing import List, Dict, Set

global i

cfg = {"B1": ["B3", "B4"],
       "B3": ["B4"],
       "B4": ["B5"],
       "B5": ["B6", "B7"],
       "B6": [],
       "B7": ["B9"],
       "B8": ["B9"],
       "B9": ["B8", "B10"],
       "B10": ["B5"]}

multiple_successors = {"B1", "B5", "B9"}

def combine_jsons(original_folder: str):
    """
    Combines all SFS JSON into a single element
    """
    combined_json = {}

    for file_ in Path(original_folder).glob("*.json"):
        with open(file_, 'r') as f:
            json_file = json.load(f)
        combined_json[Path(Path(file_).name).stem] = json_file

    return combined_json

def store_jsons(combined_json: Dict[str, Dict], target_folder: Path):
    target_folder.mkdir(exist_ok=True, parents=True)
    for file_name, json_d in combined_json.items():
        with open(target_folder.joinpath(f"{file_name}.json"), 'w') as f:
            json.dump(json_d, f)


def apply_permutation(elements: List, permutation: List, is_output_multiple: bool):
    # We keep the topmost element
    preffix = [elements[0]] if is_output_multiple else []
    shift = len(preffix)
    print(elements, permutation, shift)
    return preffix + [elements[new_position + shift] for new_position in permutation]

def shuffle_blocks(current_block: str, combined_json: Dict[str, Dict],
                   already: Set, final_folder: Path):
    """
    To shuffle the blocks, we choose the output stack, shuffle it and propagate
    the changes to the input stacks of the successors
    """
    already.add(current_block)
    current_sfs = combined_json[current_block]

    # Multiple successors means that we have to ignore the first element
    if current_block in multiple_successors:
        stack_to_consider = current_sfs["tgt_ws"][1:]
        has_multiple = True
    else:
        stack_to_consider = current_sfs["tgt_ws"]
        has_multiple = False

    original_output_stack = current_sfs["tgt_ws"].copy()

    original_input_stacks = {next_block: combined_json[next_block]["src_ws"].copy() for next_block in cfg[current_block]}

    # We produce all permutations
    positions = [i for i in range(len(stack_to_consider))]
    for permutation in itertools.permutations(positions):
        print(current_block, permutation)

        # We modify the output stack and input stacks accordingly.
        # We use the original inputs we had already stored
        current_sfs["tgt_ws"] = apply_permutation(original_output_stack, permutation, has_multiple)

        for next_block in cfg[current_block]:
            print(next_block)
            combined_json[next_block]["src_ws"] = apply_permutation(original_input_stacks[next_block],
                                                                    permutation, False)

        # At this point, we register the permutation
        global i
        store_jsons(combined_json, final_folder.joinpath(f"permutation_{i}"))
        i += 1

        # Now we try to propagate the changes
        for next_block in cfg[current_block]:

            # We ignore terminal blocks because it is strange
            # to perform operations at that level
            # Also some special cases
            if next_block not in already and len(cfg[next_block]) > 0 and next_block not in ["B3"]:
                shuffle_blocks(next_block, combined_json, already, final_folder)

if __name__ == "__main__":
    original_folder = Path(sys.argv[1])
    target_folder = Path(sys.argv[2])
    combined_jsons = combine_jsons(original_folder)
    i = 0
    shuffle_blocks("B1", combined_jsons, set(), target_folder)
