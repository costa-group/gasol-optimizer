import re


def analyze_file_oms(solution):
    pattern = re.compile("\(gas ([0-9]*)\)")
    for match in re.finditer(pattern, solution):
        number = int(match.group(1))
        pattern2 = re.compile("range")
        if re.search(pattern2, solution):
            return number, False
        return number, True


def submatch_z3(string):
    subpattern = re.compile("\(interval (.*) (.*)\)")
    for submatch in re.finditer(subpattern, string):
        return int(submatch.group(2))
    return -1


def analyze_file_z3(solution):
    pattern = re.compile("\(gas (.*)\)")
    for match in re.finditer(pattern, solution):
        number = submatch_z3(match.group(1))
        if number == -1:
            return int(match.group(1)), True
        else:
            return number, False


def submatch_barcelogic(string):
    subpattern = re.compile("\(cost (.*)\)")
    for submatch in re.finditer(subpattern, string):
        return int(submatch.group(1))
    return -1


def analyze_file_barcelogic(solution):
    pattern = re.compile("\(optimal (.*)\)")
    for match in re.finditer(pattern, solution):
        return int(match.group(1)), True
    return submatch_barcelogic(solution), False


def analyze_file(solution, solver):
    if solver == "oms":
        return analyze_file_oms(solution)
    elif solver == "z3":
        return analyze_file_z3(solution)
    else:
        return analyze_file_barcelogic(solution)


def get_tout_found_per_solver(solution, solver):
    if solver == "z3":
        return re.search(re.compile("model is not"), solution)
    elif solver == "barcelogic":
        target_gas_cost, _ = analyze_file_barcelogic(solution)
        return target_gas_cost == -1
    else:
        return re.search(re.compile("not enabled"), solution)