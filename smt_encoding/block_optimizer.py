from smt_encoding.complete_encoding.synthesis_full_encoding import FullEncoding, SMS_T, Namespace, Sort
from smt_encoding.solver.solver import Solver, OptimizeOutcome
from smt_encoding.solver.oms_executable import OMSExecutable
from smt_encoding.solver.z3_executable import Z3Executable
from typing import List, Tuple
import global_params.paths as paths
import pathlib


class BlockOptimizer:

    def __init__(self, block_id: str, sms: SMS_T, flags: Namespace, timeout: int = 10, initial_idx: int = 0):
        self._sms = sms
        self._flags = flags
        self._initial_idx = initial_idx
        self._block_id = block_id
        self._tout = timeout
        self._initialize_solver()

    def _choose_solver(self) -> Solver:
        encoding_file = f"{paths.smt_encoding_path}/{self._block_id}_encoding_{self._flags.solver}.smt2"
        self._encoding_file = encoding_file

        if self._flags.solver == "oms":
            return OMSExecutable(encoding_file)
        else:
            return Z3Executable(encoding_file)

    def _initialize_solver(self) -> None:
        solver = self._choose_solver()
        solver.set_timeout(self._tout)

        full_encoding = FullEncoding(self._sms, self._flags, self._initial_idx)
        self._full_encoding = full_encoding

        hard_constraints, soft_constraints = full_encoding.generate_full_encoding()

        solver.assert_hard(hard_constraints)
        solver.assert_soft(soft_constraints)

        declared_functions = full_encoding.functions_declared()

        if self._flags.encode_terms.startswith("uninterpreted"):
            # Uninterpreted encoding needs to declare two sorts: one for evm elements (Sort.uninterpreted) and one
            # for theta values (Sort.uninterpreted_theta)

            if any(function.range == Sort.uninterpreted for function in declared_functions):
                solver.declare_sort(Sort.uninterpreted)

            if any(function.range == Sort.uninterpreted_theta for function in declared_functions):
                solver.declare_sort(Sort.uninterpreted_theta)

            # Logic depends on whether there is some on the sort integer or not (QF_UFIDL) or not (QF_UF)
            # TODO: allow memory instructions to be dealt directly with UF, by adding alternative memory encoding
            if any(function.range == Sort.integer for function in declared_functions):
                solver.set_logic("QF_UFIDL")
            else:
                solver.set_logic("QF_UF")
        else:
            solver.set_logic("QF_IDL")

        solver.declare_function(*declared_functions)
        self._solver = solver

    def optimize_block(self) -> Tuple[OptimizeOutcome, float, List[str]]:
        pathlib.Path(paths.smt_encoding_path).mkdir(parents=True, exist_ok=True)
        optimization_outcome = self._solver.check_sat()
        time = self._solver.time_statistics()

        if optimization_outcome == OptimizeOutcome.no_model or optimization_outcome == OptimizeOutcome.unsat:
            return optimization_outcome, time, []
        return optimization_outcome, time, self._rebuild_block_from_solver()

    def generate_intermediate_files(self) -> None:
        pathlib.Path(paths.smt_encoding_path).mkdir(parents=True, exist_ok=True)
        with open(self._encoding_file, 'w') as f:
            for sentence in self._solver.to_smt2():
                print(sentence, file=f)

    def _rebuild_block_from_solver(self) -> List[str]:
        bounds = self._full_encoding._bounds
        theta_to_instr = self._full_encoding.theta_to_instr
        theta_val_encoding_to_instr = dict()

        if self._flags.encode_terms == "uninterpreted_uf":
            # Theta values are UF, so the getting the associated values returns a representation on that internal value.
            # Thus, we are going to associate that representation with the instr
            for theta_val, instr in theta_to_instr.items():
                theta_val_encoding_to_instr[self._solver.get_value(f"theta_{str(theta_val)}")] = instr
        else:
            # Otherwise, theta values appear in the encoding exactly as their numerical value
            theta_val_encoding_to_instr = {str(theta_val): instr for theta_val, instr in theta_to_instr.items()}

        return [theta_val_encoding_to_instr[self._solver.get_value(f"t_{j}")].id
                for j in range(bounds.first_position_sequence, bounds.last_position_sequence + 1)]
