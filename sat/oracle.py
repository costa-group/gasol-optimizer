#!/usr/bin/env python
# -*- coding:utf-8 -*-
##
## oracle.py
##
##  Created on: Nov 1, 2022
##      Author: Alexey Ignatiev
##      E-mail: alexey.ignatiev@monash.edu
##

#
# ==============================================================================
from pysat.examples.lbx import LBX
from pysat.examples.lsu import LSU, LSUPlus
from pysat.examples.mcsls import MCSls
from pysat.examples.rc2 import RC2, RC2Stratified, blomap
from pysat.solvers import Solver
import resource
import subprocess
import tempfile


#
# ==============================================================================
class Optimizer(object):
    """
        SAT-based optimizer. It can use either a MaxSAT solver or an MCS
        enumerator.
    """

    def __init__(self, encoding, vpool, options):
        """
            Initialiser.
        """
        self.oracle = None
        self.enc = encoding
        self.formula = encoding.formula
        self.options = options
        self.soln = None

        if options.approach not in ('rc2', 'lsu', 'sat', 'lbx', 'mcsls'):
            # expecting external MaxSAT solver
            self.oracle = None
            self.time = 0.
            self.oracle_time = self.ext_time()

        elif options.approach in ('rc2'):
            if options.blo != 'none' and max(self.formula.wght) > min(self.formula.wght):
                MXS = RC2Stratified
            else:
                MXS = RC2

            self.oracle = MXS(self.formula, solver=options.solver,
                              adapt=options.adapt,
                              exhaust=options.exhaust, incr=False,
                              minz=options.minz, trim=options.trim,
                              verbose=options.verbose)
            # selecting the right blo strategy
            if isinstance(self.oracle, RC2Stratified):
                self.oracle.bstr = blomap[options.blo]

        elif options.approach == 'lsu':
            if len(self.formula.atms):
                self.oracle = LSUPlus(self.formula, solver=options.solver,
                                      verbose=options.verbose)
            else:
                self.oracle = LSU(self.formula, solver=options.solver,
                                  verbose=options.verbose)

        elif options.approach == 'sat':
            self.oracle = Solver(name=options.solver,
                                 bootstrap_with=self.formula.hard,
                                 use_timer=True)
            for am in self.formula.atms:
                self.oracle.add_atmost(am[0], am[1])
            self.oracle.oracle_time = self.oracle.time_accum

        elif options.approach == 'lbx':
            self.oracle = LBX(self.formula, solver_name=options.solver,
                              use_cld=options.dcalls, use_timer=True)
        else:  # mcsls
            self.oracle = MCSls(self.formula, solver_name=options.solver,
                                use_cld=options.dcalls, use_timer=True)

    def __del__(self):
        """
            Destructor.
        """

        self.delete()

    def __enter__(self):
        """
            'with' constructor.
        """

        return self

    def __exit__(self, exc_type, exc_value, traceback):
        """
            'with' destructor.
        """

        self.delete()

    def delete(self):
        """
            Explicit destructor of the solver.
        """

        if self.oracle:
            self.oracle.delete()
            self.oracle = None

    def compute(self):
        """
            Solve the problem.
        """

        if self.options.approach not in ('rc2', 'lsu', 'sat', 'lbx', 'mcsls'):
            model = self.compute_ext()
            if self.options.verbose > 1:
                if self.options.verbose > 2:
                    self.soln = filter(lambda v: v > 0, model)
                    self.enc.solution(self.soln, program_only=True)

        elif self.options.approach == 'rc2':
            model = self.oracle.compute()
            if self.options.verbose > 1:
                if self.options.verbose > 2:
                    self.soln = filter(lambda v: v > 0, model)
                    self.enc.solution(self.soln, program_only=True)
        elif self.options.approach == 'lsu':
            self.oracle.solve()
            model = self.oracle.get_model()
        elif self.options.approach == 'sat':
            model = self.compute_sat()
        else:
            mcses = []
            for i, mcs in enumerate(self.oracle.enumerate()):
                cost = sum([self.formula.wght[cl_id - 1] for cl_id in mcs])
                if self.options.verbose:
                    print('c MCS:', ' '.join([str(cl_id) for cl_id in mcs]), '0')

                    if self.options.verbose > 1:
                        print('c cost:', cost)

                # converting the MCS to the corresponding model
                mss = sorted(set(range(1, len(self.formula.soft) + 1)) - set(mcs))
                self.oracle.oracle.solve(assumptions=[self.formula.soft[i - 1][0] for i in mss])
                model = self.oracle.oracle.get_model()

                mcses.append([cost, mcs, model])

                if self.options.enum and i + 1 == self.options.enum:
                    break

                self.oracle.block(mcs)

            # taking the best model so far
            model = min(mcses, key=lambda pair: pair[0])[2]

        # returning the positive variables only
        assert model is not None, 'No model is computed!'
        self.soln = filter(lambda v: v > 0, model)

        if self.options.verbose:
            if self.options.approach in ('rc2', 'lsu', 'sat', 'lbx', 'mcsls'):
                print('c solving time: {0:.4f}'.format(self.oracle.oracle_time()))
            else:
                print('c solving time: {0:.4f}'.format(self.ext_time()))
            print("Optimal", flush=True)

        return self.soln

    def compute_sat(self):
        """
            Iterative SAT-based approach.
        """

        soft = [cl[0] for cl in self.formula.soft]

        # detecting unit cores
        nof_dropped = 0
        for l in soft:
            st, props = self.oracle.propagate(assumptions=[l], phase_saving=2)
            if not st:
                nof_dropped += 1
                self.oracle.add_clause([-l])
            else:
                break

        if self.options.verbose > 1:
            print('c lb:', nof_dropped)

        # setting phases before each SAT call
        if self.options.phases:
            self.oracle.set_phases(literals=soft)

        if self.options.init and self.enc.bcode.osol:
            phases = []  # all the phases corresponding to the upper bound

            for step, opcode in enumerate(self.enc.bcode.osol):
                arg = None
                if opcode.startswith('DUP'):
                    arg = int(opcode[3:].strip()) - 1
                elif opcode.startswith('SWAP'):
                    arg = int(opcode[4:].strip())

                obj = tuple(['op', step, opcode] + ([arg] if arg is not None else []))
                assert obj in self.enc.vpool.obj2id.keys()
                phases.append(self.enc.vpool.obj2id[obj])

            # setting the upper bound solution
            assert self.oracle.propagate(assumptions=phases, phase_saving=2)[0]
            # assert self.oracle.solve(assumptions=phases)

        # main loop
        clen = len(str(len(soft)))
        while self.oracle.solve() == True:
            model = self.oracle.get_model()

            # dropping unnecessary iterations
            while soft and model[abs(soft[-1] - 1)] == soft[-1]:
                self.oracle.add_clause([soft.pop()])

            if self.options.verbose > 1:
                print('o {0:>{width}}; time: {1:.4f}s'.format(len(soft), self.oracle.oracle_time(), width=clen))

                if self.options.verbose > 2:
                    self.soln = filter(lambda v: v > 0, model)
                    self.enc.solution(self.soln, program_only=True)

            full_len = self.enc.lenlb + len(soft)
            assert full_len <= self.enc.bcode.mlen

            if full_len == self.enc.bcode.minlen:
                break

            if self.options.bounds:
                for op, slen in self.enc.bcode.sufflen.items():
                    if self.options.wasm and self.enc.bcode.inst[op].small_zeroary() or \
                            not self.options.wasm and self.enc.bcode.inst[op].type == 'PUSH':
                        # PUSH can occur multiple times
                        self.oracle.add_clause([self.enc.opdone(full_len - slen - 1, op)])
                    else:
                        for step in range(full_len - slen, full_len):
                            self.oracle.add_clause([-self.enc.op(step, op)])

            # next bound to try
            if soft:
                self.oracle.add_clause([soft.pop()])
            else:
                break

        return model

    def compute_ext(self):
        """
            Solve using an external MaxSAT solver.
        """

        with tempfile.NamedTemporaryFile(suffix='.wcnf') as fp:
            comments = self.formula.comments[:]
            self.formula.comments = []
            self.formula.to_file(fp.name)
            self.formula.comments = comments[:]

            self.time = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime + \
                        resource.getrusage(resource.RUSAGE_SELF).ru_utime

            command = self.options.approach.split() + [fp.name]
            outp = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            outp = outp.communicate()[0].decode(encoding='ascii').split('\n')

            self.time = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime + \
                        resource.getrusage(resource.RUSAGE_SELF).ru_utime - self.time

        # going backwards in the log and extracting the model
        for line in range(len(outp) - 1, -1, -1):
            line = outp[line]
            if line.startswith('v '):
                model = line[2:].split()
                if len(model) == 1:  # new model line format
                    model = [i * (2 * int(l) - 1) for i, l in enumerate(model[0], 1)]
                else:  # old model line format
                    model = [int(l) for l in model]

        return model

    def ext_time(self):
        """
            Returning time spent by the external solver.
        """

        return self.time
