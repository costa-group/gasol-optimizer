from argparse import Namespace
from typing import Any


class OptimizationParams:
    """
    Parameters needed for GASOL's optimization pipeline
    """

    def __init__(self):
        # The fields declaration follow the same order as in gasol_asm's
        # argument parser

        # File that contains the code to optimize (either .txt file or
        # the output from the compiler)
        self.input_file = None

        # Format for input
        self.input_format = None

        # Contract name to optimize
        self.contract = None

        # File to optimize the optimized code
        self.optimized_file = None

        # CSV file to store the optimization results for each sequence
        self.seqs_file = None

        # CSV file to store the optimization results for each block
        self.blocks_file = None

        # Whether we want to produce only the associated
        # sfs files or enable the whole pipeline
        self.optimization_enabled = None

        self.dot_generation = False

        # Whether to keep the intermediate files generated throughout the
        # optimization process
        self.keep_files = None

        # Flag for output information
        # TODO: verbose levels
        self.verbose = None

        # Enable log generation
        self.generate_log = None

        # Filename for the log file
        self.log_file = None

        # Optimization from a log file
        self.from_log = None

        # Choose Max-SMT solver (barcelogic, z3, oms)
        self.smt_solver = None

        # Timeout per block: 2 * (1 + #STORE)
        self.timeout = None

        # If enabled, overwrites the default formula and fixes
        # the specified timeout in self.timeout
        self.direct_timeout = None

        # Enable PUSH0 is included in the ISA
        self.push0 = None

        # Rules that increase the bytes-size are enabled or not
        self.size_rules_enabled = None

        # Simplification rules (or Peephole optimizations) enabled
        self.rules_enabled = None

        # Split when STORE instructions are detected (initial version of SYRUP)
        self.split_storage = None

        # Split at STORE instructions when the considered block
        # surpasses certain #instrs (> 24 instructions)
        self.split_partition = None

        # SMT solver encoding options
        self.memory_encoding = None
        self.push_basic = None
        self.pop_uninterpreted = None
        self.order_bounds = None
        self.empty = None
        self.encode_terms = None
        # Terminal blocks: ends with STOP or REVERT. The requirements
        # for optimization can be relaxed, as we only need to ensure
        # the memory operations are applied and the args for those operations
        # are computed in the right order
        self.terminal = None
        # Encoding based on ac
        self.ac_solver = False

        # Criteria: gas, length, size
        self.criteria = None

        # Direct inequalities
        self.direct_soft = None
        self.at_most = None
        self.pushed_once = None
        self.no_output_before_pop = None
        self.order_conflicts = None

        # Whether the bound predictor model is used
        self.bound_select = False

        # Whether the model to skip blocks (that are likely not
        # to be optimized further) is used
        self.opt_select = False

        # Model Query objects for NGS
        self.optimized_predictor_model = None
        self.bound_model = None

        self.forves_enabled = None

        self.block_name = ""
        self.block_name_prefix = ""
        self.dep_mem_info = {}

        # Greedy extensions
        self.ub_greedy = None
        self.greedy = None
        self.no_simp = True
        self.debug_flag = False
        self.dzn = False
        self.minstack = False

        self.length_bound = False
        self.gcc_bounds = False
        self.unary_shrink = False
        self.binary_shrink = False
        self.pop_unused = False

    def parse_args(self, parsed_args: Namespace):
        self.input_file = parsed_args.input_path

        # Distinguish cases
        if "block" in parsed_args:
            self.input_format = "plain" if parsed_args.block else "sfs" \
                if parsed_args.sfs else "single-asm" if parsed_args.json_asm else "asm"
        else:
            self.input_format = "asm"

        if "contract" in parsed_args:
            self.contract = parsed_args.contract
        else:
            self.contract = None

        if "seq_csv_path" in parsed_args:
            self.seqs_file = parsed_args.seq_csv_path
        else:
            self.seqs_file = "seqs.csv"

        if "blocks_file" in parsed_args:
            self.blocks_file = parsed_args.blocks_file
        else:
            self.blocks_file = "blocks.csv"

        self.optimization_enabled = parsed_args.backend
        self.keep_files = parsed_args.intermediate or not parsed_args.backend
        self.verbose = parsed_args.debug_flag

        self.dot_generation = parsed_args.dot_generation

        # Log options
        self.generate_log = parsed_args.log
        self.log_file = parsed_args.log_stored_final
        # TODO: introduce a flag to signal the optimization is produced from a log file
        #  and reuse log file both for storing and retrieving instead
        self.from_log = parsed_args.log_path

        # Basic options for Max-SMT
        self.smt_solver = parsed_args.solver
        self.timeout = parsed_args.tout
        self.direct_timeout = parsed_args.direct_timeout
        self.push0 = parsed_args.push0_enabled
        self.rules_enabled = not parsed_args.no_simp

        # Split options
        self.split_storage = parsed_args.storage
        self.split_partition = parsed_args.partition

        # Hard constraints
        self.memory_encoding = parsed_args.memory_encoding
        self.push_basic = parsed_args.push_basic

        if "pop_uninterpreted" in parsed_args:
            self.pop_uninterpreted = parsed_args.pop_uninterpreted
        else:
            self.pop_uninterpreted = not parsed_args.pop_basic
        self.order_bounds = parsed_args.order_bounds
        self.empty = parsed_args.empty
        self.encode_terms = parsed_args.encode_terms
        self.terminal = parsed_args.terminal
        self.ac_solver = parsed_args.ac_solver

        # Soft constraints
        self.criteria = "size" if parsed_args.size else "length" if parsed_args.length else "gas"

        # Could be adapted
        self.size_rules_enabled = True

        if "direct_soft" in parsed_args:
            self.direct_soft = parsed_args.direct_soft
        else:
            self.direct_soft = parsed_args.direct

        self.at_most = parsed_args.at_most
        self.pushed_once = parsed_args.pushed_once
        self.no_output_before_pop = parsed_args.no_output_before_pop
        self.order_conflicts = parsed_args.order_conflicts

        self.bound_select = parsed_args.bound_select
        self.opt_select = parsed_args.opt_select

        if "forves_enabled" in parsed_args:
            self.forves_enabled = parsed_args.forves_enabled
        else:
            self.forves_enabled = False

        # Greedy options
        self.greedy = parsed_args.greedy
        self.ub_greedy = parsed_args.ub_greedy

        if "no_simp" in parsed_args:
            self.no_simp = parsed_args.no_simp

        if "debug_flag" in parsed_args:
            self.debug_flag = parsed_args.debug_flag

        self.dzn = parsed_args.dzn
        self.minstack = parsed_args.minstack
        self.length_bound = parsed_args.length_bound
        self.gcc_bounds = parsed_args.gcc_bounds
        self.unary_shrink = parsed_args.unary_shrink
        self.binary_shrink = parsed_args.binary_shrink
        self.pop_unused = parsed_args.pop_unused
        self.split_block = parsed_args.split_block
