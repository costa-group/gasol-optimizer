"""
Module to show the stacks from a group of csvs
"""
import sys
import json
from pathlib import Path
from typing import List


def print_split_aligned(labels, data_lists, padding=4):
    # Convert lists to strings first to measure their length
    list_strs = [str(lst) for lst in data_lists]

    # Calculate the maximum width for each "column"
    max_label_w = max(len(label) for label in labels)
    max_list_w = max(len(s) for s in list_strs)

    for label, list_str in zip(labels, list_strs):
        # Left-align label:  f"{label:<{max_label_w}}"
        # Right-align list: f"{list_str:>{max_list_w}}"
        # Separate them with the chosen padding
        print(f"{label:<{max_label_w}}:{' ' * padding}{list_str:>{max_list_w}}")


def load_stacks(original_folder: str):
    """

    """
    combined_info = {}

    for file_ in Path(original_folder).glob("*.json"):
        with open(file_, 'r') as f:
            json_file = json.load(f)
        filename = Path(Path(file_).name).stem
        combined_info[filename] = [[f'{filename} input', json_file["src_ws"]],
                                   [f'{filename} output', json_file["tgt_ws"]]]

    labels, lines = [], []
    for filename in sorted(combined_info, key=(lambda x: int(x[1:]))):
        for stack_info in combined_info[filename]:
            label, line = stack_info
            labels.append(label)
            lines.append(line)

    return labels, lines


if __name__ == "__main__":
    labels, stacks = load_stacks(sys.argv[1])
    print_split_aligned(labels, stacks)
