from smt_encoding.solver.solver_from_executable import SolverFromExecutable, AssertSoft, List, translate_formula
from global_params.paths import z3_exec


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
        return ["(get-model)"]

    def cost_function(self) -> str:
        return ""

    def command_line(self) -> str:
        return f"{z3_exec} -smt2 {self._file_path}"

