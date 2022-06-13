from smt_encoding.solver.solver_from_executable import SolverFromExecutable, AssertSoft, List, translate_formula, Function
from global_params.paths import oms_exec
import re


class OMSExecutable(SolverFromExecutable):

    def __init__(self, file_path: str):
        super(OMSExecutable, self).__init__(oms_exec, file_path)
        # Need this option to produce models
        self.set_option("produce-models", "true")

    def write_soft(self, soft_constraint: AssertSoft) -> str:
        if soft_constraint.group is None:
            return f"(assert-soft {translate_formula(soft_constraint.formula)} :weight {str(soft_constraint.weight)})"
        else:
            return f"(assert-soft {translate_formula(soft_constraint.formula)} :weight {str(soft_constraint.weight)} " \
                   f":id {soft_constraint.group})"

    def load_model(self) -> List[str]:
        return ["(get-objectives)", "(get-model)"]

    def cost_function(self) -> str:
        return "(minimize cost)"

    def command_line(self) -> str:
        return f"{oms_exec} {self._file_path} -optimization=True"

    def get_value_pattern(self, var_name: str) -> str:
        return f"\(define-fun {re.escape(var_name)} \(.*\) \S+ (.+)\)"
