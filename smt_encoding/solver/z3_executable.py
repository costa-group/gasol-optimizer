from smt_encoding.solver.solver import OptimizeOutcome
from smt_encoding.solver.solver_from_executable import SolverFromExecutable, AssertSoft, List, translate_formula
from global_params.paths import z3_exec
import re


class Z3Executable(SolverFromExecutable):

    def __init__(self, file_path: str):
        super(Z3Executable, self).__init__(z3_exec, file_path)

    def write_soft(self, soft_constraint: AssertSoft) -> str:
        if soft_constraint.group is None:
            return f"(assert-soft {translate_formula(soft_constraint.formula)} :weight {str(soft_constraint.weight)})"
        else:
            return f"(assert-soft {translate_formula(soft_constraint.formula)} :weight {str(soft_constraint.weight)} " \
                   f":id {soft_constraint.group})"

    def load_model(self) -> List[str]:
        return ["(get-objectives)", "(get-model)"]

    def cost_function(self) -> None:
        return None

    def optimization_outcome(self) -> OptimizeOutcome:
        if self._model is None:
            raise ValueError("Check-sat has not been called")
        if "error" in self._model:
            return OptimizeOutcome.no_model
        elif "interval" in self._model:
            return OptimizeOutcome.non_optimal
        else:
            return OptimizeOutcome.optimal

    def command_line(self) -> str:
        return f"{z3_exec} -smt2 {self._file_path}"

    def get_value_pattern(self, var_name: str) -> str:
        return f"\(define-fun {re.escape(var_name)} \(.*\) \S+\n\s*(.+)\)"
