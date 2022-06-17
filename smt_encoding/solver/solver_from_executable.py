import os
import resource
import shlex
import subprocess
import re

from abc import abstractmethod
from smt_encoding.solver.solver import Solver, Function, OptimizeOutcome
from smt_encoding.constraints.assertions import AssertHard, AssertSoft, Formula_T
from smt_encoding.constraints.function import Sort, ExpressionReference
from typing import List, Dict, Optional, Union


sort_to_str = {Sort.integer: 'Int', Sort.boolean: 'Bool', Sort.uninterpreted: 'S', Sort.uninterpreted_theta: 'T'}


def run_command(cmd):
    FNULL = open(os.devnull, 'w')
    solc_p = subprocess.Popen(shlex.split(cmd), stdout=subprocess.PIPE,
                              stderr=FNULL)
    return solc_p.communicate()[0].decode()


def run_and_measure_command(cmd):
    usage_start = resource.getrusage(resource.RUSAGE_CHILDREN)
    solution = run_command(cmd)
    usage_stop = resource.getrusage(resource.RUSAGE_CHILDREN)
    return solution, usage_stop.ru_utime + usage_stop.ru_stime - usage_start.ru_utime - usage_start.ru_stime


def translate_formula(formula: Formula_T) -> str:
    if type(formula) == int:
        return str(formula)
    elif type(formula) == bool:
        if formula:
            return "true"
        else:
            return "false"
    elif type(formula) == ExpressionReference:
        return str(formula) if len(formula.arguments) == 0 else \
            f"({str(formula.func)} {' '.join(translate_formula(arg) for arg in formula.arguments)})"
    else:
        return f"({formula.connector_name}  {' '.join((translate_formula(argument) for argument in formula.arguments))})"


def translate_assert_hard(hard_constraint: AssertHard) -> str:
    return translate_formula(hard_constraint.formula)


class SolverFromExecutable(Solver):

    def __init__(self, solver_path: str, file_path: str):
        self._solver_path = solver_path
        self._file_path = file_path

        self._logic = None
        self._options = dict()
        self._sorts = []
        self._soft: List[AssertSoft] = []
        self._hard: List[AssertHard] = []
        self._functions: Dict[str, Function] = dict()
        self._model = None
        self._time = 0

    def set_logic(self, logic: str) -> None:
        self._logic = logic

    def set_option(self, option: str, value: str) -> None:
        self._options[option] = value

    def declare_sort(self, sort_name: Sort) -> None:
        self._sorts.append(sort_name)

    def assert_hard(self, *hard_constraints: AssertHard):
        self._hard.extend(hard_constraints)

    def assert_soft(self, *soft_constraint: AssertSoft):
        self._soft.extend(soft_constraint)

    def declare_function(self, *functions: Function):
        for function in functions:
            self._functions[function.name] = function

    @abstractmethod
    def write_soft(self, soft_constraint: AssertSoft) -> str:
        pass

    @abstractmethod
    def load_model(self) -> List[str]:
        pass

    @abstractmethod
    def cost_function(self) -> Optional[str]:
        pass

    @abstractmethod
    def command_line(self) -> str:
        pass

    def to_smt2(self) -> str:
        sentences = [f"(set-logic {self._logic})"]
        sentences.extend(f"(set-option :{option} {value})" for option, value in self._options.items())
        sentences.extend(f"(declare-sort {sort_to_str[sort]} 0)" for sort in self._sorts)
        sentences.extend(f"(declare-fun {function.name} ({' '.join((sort_to_str[sort] for sort in function.domain))}) "
                         f"{sort_to_str[function.range]})" for function in self._functions.values())
        sentences.extend(f"(assert {translate_assert_hard(hard_constraint)})" for hard_constraint in self._hard)
        sentences.extend(self.write_soft(soft_constraint) for soft_constraint in self._soft)
        cost_sentence = self.cost_function()

        if cost_sentence is not None:
            sentences.append(cost_sentence)

        sentences.append("(check-sat)")
        sentences.extend(self.load_model())
        return '\n'.join(sentences)

    @abstractmethod
    def optimization_outcome(self) -> OptimizeOutcome:
        pass

    def check_sat(self) -> OptimizeOutcome:
        """
        Execute the SMT solver
        """
        if self._logic is None:
            raise ValueError("Logic has not been set to any value")

        smt2_format = self.to_smt2()
        with open(self._file_path, 'w') as f:
            f.write(smt2_format)

        model, total_time = run_and_measure_command(self.command_line())
        self._model = model
        self._time = total_time
        return self.optimization_outcome()

    def get_model(self):
        if self._model is None:
            raise ValueError("No model has been generated yet")
        return self._model

    def get_objectives(self):
        return "a"

    @abstractmethod
    def get_value_pattern(self, var_name: str) -> str:
        """
        Generates the corresponding pattern string for obtaining a value from the model,
        so that calling re.search().group(1) returns the corresponding representation

        :return: the pattern verifying the condition
        """
        pass

    def get_value(self, variable: Union[Function, str]) -> str:
        if self._model is None:
            raise ValueError("No model has been generated yet")

        # Format:〈function_def 〉 ::= 〈symbol〉(〈sorted_var〉∗) 〈sort〉〈term〉
        pattern = re.compile(self.get_value_pattern(str(variable)))
        occurrence = re.search(pattern, self._model)
        if occurrence is not None:
            return occurrence.group(1)
        else:
            raise ValueError("Invalid variable")