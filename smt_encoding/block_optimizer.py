import copy

from smt_encoding.complete_encoding.synthesis_full_encoding import FullEncoding, SMS_T, Namespace, Sort
from smt_encoding.solver.solver import Solver, OptimizeOutcome
from smt_encoding.solver.oms_executable import OMSExecutable
from smt_encoding.solver.z3_executable import Z3Executable
from sfs_generator.asm_bytecode import AsmBytecode
from typing import List, Tuple
import global_params.paths as paths
import pathlib


class BlockOptimizer:

    def __init__(self, block_id: str, sms: SMS_T, flags: Namespace, initial_idx: int = 0):
        self._sms = sms
        self._flags = flags
        self._initial_idx = initial_idx
        self._block_id = block_id
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
        solver.set_timeout(self._flags.tout)

        full_encoding = FullEncoding(self._sms, self._flags, self._initial_idx)
        self._full_encoding = full_encoding

        declared_functions, hard_constraints, soft_constraints = full_encoding.generate_full_encoding()

        if self._flags.encode_terms == "uninterpreted":
            # Uninterpreted encoding needs to declare two sorts: one for evm elements (Sort.uninterpreted) and one
            # for theta values (Sort.uninterpreted_theta)
            solver.declare_sort(Sort.uninterpreted)
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
        solver.assert_hard(*hard_constraints)
        solver.assert_soft(*soft_constraints)
        self._solver = solver

    def optimize_block(self) -> Tuple[OptimizeOutcome, float, List[AsmBytecode]]:
        pathlib.Path(paths.smt_encoding_path).mkdir(parents=True, exist_ok=True)
        optimization_outcome = self._solver.check_sat()
        time = self._solver.time_statistics()

        if optimization_outcome == OptimizeOutcome.no_model:
            return optimization_outcome, time, []
        return optimization_outcome, time, self._rebuild_block_from_solver()

    def generate_intermediate_files(self) -> None:
        pathlib.Path(paths.smt_encoding_path).mkdir(parents=True, exist_ok=True)
        with open(self._encoding_file, 'w') as f:
            f.write(self._solver.to_smt2())

    def _rebuild_block_from_solver(self) -> List[AsmBytecode]:
        bounds = self._full_encoding._bounds
        theta_to_instr = self._full_encoding.theta_to_instr
        theta_val_encoding_to_instr = dict()
        asm_instructions = []

        if self._flags.encode_terms == "uninterpreted":
            # Theta values are UF, so the getting the associated values returns a representation on that internal value.
            # Thus, we are going to associate that representation with the instr
            for theta_val, instr in theta_to_instr.items():
                theta_val_encoding_to_instr[self._solver.get_value(f"theta_{str(theta_val)}")] = instr
        else:
            # Otherwise, theta values appear in the encoding exactly as their numerical value
            theta_val_encoding_to_instr = {str(theta_val): instr for theta_val, instr in theta_to_instr.items()}

        for j in range(bounds.first_position_sequence, bounds.last_position_sequence + 1):
            t_j = self._solver.get_value(f"t_{j}")
            associated_instr = theta_val_encoding_to_instr[t_j]

            # NOP instructions are not considered in the solution
            if associated_instr.id == "NOP":
                continue

            # If push basic, then we need to retrieve also a_j
            if associated_instr.id == "PUSH":
                a_j = self._solver.get_value(f"a_{j}")
                value = hex(int(a_j))[2:]
                asm_instructions.append(AsmBytecode(-1, -1, -1, associated_instr.opcode_name, value))
            # If it is a PUSH instruction, we need to convert the value to hexadecimal
            elif associated_instr.opcode_name == "PUSH":
                value = hex(int(associated_instr.value))[2:]
                asm_instructions.append(AsmBytecode(-1, -1, -1, associated_instr.opcode_name, value))
            else:
                asm_instructions.append(AsmBytecode(-1, -1, -1, associated_instr.opcode_name, associated_instr.value))

        return asm_instructions