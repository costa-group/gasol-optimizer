#!/usr/bin/env python3

import glob
import os
import pathlib
import pandas as pd
from copy import deepcopy
import re
import argparse


def associated_results_by_criteria(gasol_selected, general_criteria):
    initial_result = 0
    for gasol_dict in gasol_selected:
        if not pd.isna(gasol_dict[general_criteria]):
            initial_result += gasol_dict[general_criteria]
    return initial_result


def select_best_rows(gasol1_selected, gasol2_selected, gasol3_selected, statistics, criteria):
    # Blocks > 40 will not be considered for gasol1, so timeout is determine by gasol2 selected and gasol3 selected
    if gasol1_selected == [] or gasol1_selected[0]['init_progr_len'] > 40:
        gasol1_selected = []

        time_spent = max(associated_results_by_criteria(gasol2_selected, 'solver_time_in_sec'),
                         associated_results_by_criteria(gasol3_selected, 'solver_time_in_sec'))

    else:
        time_spent = gasol1_selected[0]['solver_time_in_sec']

    if gasol1_selected == [] or gasol1_selected[0]['no_model_found']:
        return None

    if criteria == "gas":
        select = "saved_gas"
        other_select = "saved_bytes"
    else:
        select = "saved_bytes"
        other_select = "saved_gas"

    if not gasol1_selected:
        savings_1 = -1
    else:
        savings_1 = associated_results_by_criteria(gasol1_selected, select)

    savings_2 = associated_results_by_criteria(gasol2_selected, select)
    savings_3 = associated_results_by_criteria(gasol3_selected, select)

    new_row = {'solver_time_in_sec': time_spent}

    if savings_1 > savings_2:
        new_row[select] = savings_1
        new_row[other_select] = associated_results_by_criteria(gasol1_selected, other_select)
        statistics["version_1"] = statistics.get("version_1", 0) + 1

    elif savings_2 > savings_3:
        new_row[select] = savings_2
        new_row[other_select] = associated_results_by_criteria(gasol2_selected, other_select)
        statistics["version_2"] = statistics.get("version_2", 0) + 1

    else:
        new_row[select] = savings_3
        new_row[other_select] = associated_results_by_criteria(gasol3_selected, other_select)
        statistics["version_3"] = statistics.get("version_3", 0) + 1

    return new_row


if __name__ == "__main__":

    parser = argparse.ArgumentParser()
    parser.add_argument("-path", metavar='path', action='store', type=str,
                        help="", required=True)
    parser.add_argument("-dependency", metavar='dependency', action='store', type=str,
                        help="", required=True)
    parser.add_argument("-criteria", metavar='criteria', action='store', type=str,
                        help="", required=True)
    parser.add_argument("-final", metavar='final', action='store', type=str,
                        help="", required=True)

    args = parser.parse_args()
    parent_directory = args.path
    csv_list = args.dependency
    criteria = args.criteria
    final_path = args.final

    gasol1_files = glob.glob(parent_directory + "gas_gasol1/oms_10s/*.csv")
    gasol2_files = glob.glob(parent_directory + "gas_gasol2/oms_10s/*.csv")
    gasol3_files = glob.glob(parent_directory + "gas_gasol3/oms_10s/*.csv")
    gasol4_files = glob.glob(parent_directory + "gas_gasol4/oms_10s/*.csv")

    dependency_files = glob.glob(csv_list + "*.csv")

    sol_dir = final_path + "gas-gasol-combined/oms_10s/"
    pathlib.Path(sol_dir).mkdir(parents=True, exist_ok=True)

    statistics_rows = []

    for gasol1_file in gasol1_files:
        gasol2_file = list(filter(lambda x: gasol1_file.split("/")[-1] == x.split("/")[-1], gasol2_files))[0]
        gasol3_file = list(filter(lambda x: gasol1_file.split("/")[-1] == x.split("/")[-1], gasol3_files))[0]
        gasol4_file = list(filter(lambda x: gasol1_file.split("/")[-1] == x.split("/")[-1], gasol4_files))[0]

        dependency_file = \
        list(filter(lambda x: re.search(re.compile(gasol1_file.split("/")[-1].split("_")[0]), x) is not None,
                    dependency_files))[0]
        combined_file = sol_dir + gasol1_file.split("/")[-1]
        rows_list = []

        gasol1_filtered = []
        gasol2_filtered = []
        gasol3_filtered = []
        gasol4_filtered = []

        gasol1_rows = pd.read_csv(gasol1_file).to_dict('records')
        gasol2_rows = pd.read_csv(gasol2_file).to_dict('records')
        gasol3_rows = pd.read_csv(gasol3_file).to_dict('records')
        gasol4_rows = pd.read_csv(gasol4_file).to_dict('records')

        dependency_rows = pd.read_csv(dependency_file).to_dict('records')

        statistics = {'version_1': 0, 'version_2': 0, 'version_3': 0}

        for dependency_row in dependency_rows:
            not_split = list(filter(lambda x: x != '', dependency_row['Completo'].split(' ')))
            gasol1_selected = list(filter(lambda x: (x['block_id'] + ".json") in not_split, gasol1_rows))

            partition = list(filter(lambda x: x != '', dependency_row['Particion'].split(' ')))
            gasol2_selected = list(filter(lambda x: (x['block_id'] + ".json") in partition, gasol2_rows))

            split_files = list(filter(lambda x: x != '', dependency_row['Syrup'].split(' ')))
            gasol3_selected = list(filter(lambda x: (x['block_id'] + ".json") in split_files, gasol3_rows))

            gasol4_selected = list(filter(lambda x: (x['block_id'] + ".json") in split_files, gasol3_rows))

            new_row = select_best_rows(gasol1_selected, gasol2_selected, gasol3_selected, statistics, criteria)
            if new_row is not None:
                new_row['name'] = not_split[0]
                rows_list.append(new_row)
                gasol1_filtered.extend(gasol1_selected)
                gasol2_filtered.extend(gasol2_selected)
                gasol3_filtered.extend(gasol3_selected)
                gasol4_filtered.extend(gasol4_selected)

        gasol1_filtered_file = final_path + "gas_gasol1_filtered/oms_10s/" + gasol1_file.split("/")[-1]
        gasol2_filtered_file = final_path + "gas_gasol2_filtered/oms_10s/" + gasol1_file.split("/")[-1]
        gasol3_filtered_file = final_path + "gas_gasol3_filtered/oms_10s/" + gasol1_file.split("/")[-1]
        gasol4_filtered_file = final_path + "gas_gasol4_filtered/oms_10s/" + gasol1_file.split("/")[-1]

        pathlib.Path(final_path + "gas_gasol1_filtered/oms_10s/").mkdir(parents=True, exist_ok=True)
        pathlib.Path(final_path + "gas_gasol2_filtered/oms_10s/").mkdir(parents=True, exist_ok=True)
        pathlib.Path(final_path + "gas_gasol3_filtered/oms_10s/").mkdir(parents=True, exist_ok=True)
        pathlib.Path(final_path + "gas_gasol4_filtered/oms_10s/").mkdir(parents=True, exist_ok=True)

        df = pd.DataFrame(rows_list, columns=['name', 'saved_gas', 'solver_time_in_sec', 'saved_bytes'])
        df.to_csv(combined_file)

        df = pd.DataFrame(gasol1_filtered)
        df.to_csv(gasol1_filtered_file)

        df = pd.DataFrame(gasol2_filtered)
        df.to_csv(gasol2_filtered_file)

        df = pd.DataFrame(gasol3_filtered)
        df.to_csv(gasol3_filtered_file)

        df = pd.DataFrame(gasol4_filtered)
        df.to_csv(gasol4_filtered_file)

        statistics['name'] = gasol1_file.split("/")[-1]
        statistics_rows.append(statistics)
    df2 = pd.DataFrame(statistics_rows, columns=['name', 'version_1', 'version_2', 'version_3'])
    df2.to_csv(final_path + "statistics.csv")


