#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## options.py
##
##  Created on: Oct 26, 2022
##      Author: Alexey Ignatiev
##      E-mail: alexey.ignatiev@monash.edu
##

#
#==============================================================================
import getopt
import os
from pysat.solvers import SolverNames
from pysat.card import *
import sys


#
#==============================================================================
class Options(object):
    """
        Command-line options handler for the mxevm solver.
    """

    # cardinality encodings
    encmap = {
        'pw': EncType.pairwise,
        'bw': EncType.bitwise,
        'seqc': EncType.seqcounter,
        'cardn': EncType.cardnetwrk,
        'sortn': EncType.sortnetwrk,
        'ladder': EncType.ladder,
        'tot': EncType.totalizer,
        'mtot': EncType.mtotalizer,
        'kmtot': EncType.kmtotalizer,
        'native': EncType.native
    }

    def __init__(self, opt_args):
        """
            Initialiser.
        """

        self.adapt = False
        self.approach = 'maxsat'
        self.bprop = False
        self.bounds = False
        self.cenc = 'seqc'
        self.csv = False
        self.corner = False
        self.config = 'none'
        self.dcalls = False
        self.dump = False
        self.enum = 1
        self.fprop = False
        self.blo = 'none'
        self.init = False
        self.lenlb = False
        self.minz = False
        self.mlen = None
        self.nods = False
        self.nodummy = True
        self.nofocc = False
        self.objf = 'none'
        self.pdeps = False
        self.phases = False
        self.pop_prev = False
        self.rgsz = None
        self.solver = 'g3'
        self.sksz = None
        self.ponly = False
        self.tail = False
        self.trim = 0
        self.verbose = 0
        self.wasm = False
        self.exhaust = False
        self.files = None

        # parsing the command line
        self.parse(opt_args)

    def parse(self, opt_args):
        """
            Does the parsing.
        """

        try:
            opts, args = getopt.getopt(opt_args,
                                    '1Aa:bBcCdDe:E:fhil:LmM:nNo:pPR:s:S:t:Tvwx',
                                    ['adapt', 'all', 'allow-dummy',
                                     'approach=', 'backprop', 'bounds', 'csv',
                                     'corner', 'config=', 'dcalls', 'dump',
                                     'enc=', 'enum=', 'forwprop', 'help',
                                     'init', 'blo=', 'lb', 'minimize',
                                     'maxlen=', 'nods','nofocc', 'obj=',
                                     'pdeps', 'phases', 'ponly', 'pop-prev',
                                     'regsz=', 'solver=', 'stacksz=', 'trim=',
                                     'tail', 'verbose', 'wasm', 'exhaust'])
        except getopt.GetoptError as err:
            sys.stderr.write(str(err).capitalize())
            self.usage()
            sys.exit(1)

        all_flags = False

        for opt, arg in opts:
            if opt in ('-1', '--adapt'):
                self.adapt = True
            elif opt in ('-a', '--approach'):
                self.approach = str(arg)
            elif opt in ('-A', '--all'):
                all_flags = True
            elif opt == '--allow-dummy':
                self.nodummy = False
            elif opt in ('-b', '--backprop'):
                self.bprop = True
            elif opt in ('-B', '--bounds'):
                self.bounds = True
            elif opt in ('-c', '--csv'):
                self.csv = True
            elif opt in ('-C', '--corner'):
                self.corner = True
            elif opt == '--config':
                self.config = str(arg)
            elif opt in ('-d', '--dcalls'):
                self.dcalls = True
            elif opt in ('-D', '--dump'):
                self.dump = True
            elif opt in ('-e', '--cardenc'):
                self.cenc = str(arg)
            elif opt in ('-E', '--enum'):
                self.enum = str(arg)
                if self.enum != 'all':
                    self.enum = int(self.enum)
            elif opt in ('-f', '--forwprop'):
                self.fprop = True
            elif opt in ('-h', '--help'):
                self.usage()
                sys.exit(0)
            elif opt in ('-i', '--init'):
                self.init = True
            elif opt in ('-l', '--blo'):
                self.blo = str(arg)
            elif opt in ('-L', '--lb'):
                self.lenlb = True
            elif opt in ('-m', '--minimize'):
                self.minz = True
            elif opt in ('-M', '--maxlen'):
                self.mlen = str(arg)
                self.mlen = None if self.mlen == 'none' else int(self.mlen)
            elif opt in ('-n', '--nods'):
                self.nods = True
            elif opt in ('-N', '--nofocc'):
                self.nofocc = True
            elif opt in ('-o', '--obj'):
                self.objf = str(arg)
            elif opt in ('-p', '--pdeps'):
                self.pdeps = True
            elif opt in ('-P', '--phases'):
                self.phases = True
            elif opt == '--ponly':
                self.ponly = True
            elif opt == '--pop-prev':
                self.pop_prev = True
            elif opt in ('-R', '--regsz'):
                self.rgsz = str(arg)
                self.rgsz = None if self.rgsz == 'none' else int(self.rgsz)
            elif opt in ('-s', '--solver'):
                self.solver = str(arg)
            elif opt in ('-S', '--stacksz'):
                self.sksz = str(arg)
                self.sksz = None if self.sksz == 'none' else int(self.sksz)
            elif opt in ('-t', '--trim'):
                self.trim = int(arg)
            elif opt in ('-T', '--tail'):
                self.tail = True
            elif opt in ('-v', '--verbose'):
                self.verbose += 1
            elif opt in ('-w', '--wasm'):
                self.wasm = True
            elif opt in ('-x', '--exhaust'):
                self.exhaust = True
            else:
                assert False, 'Unhandled option: {0} {1}'.format(opt, arg)

        self.cenc = self.encmap[self.cenc]

        # using minicard's native implementation of AtMost1 constraints
        if self.solver in SolverNames.minicard or \
                self.solver in SolverNames.gluecard3 or \
                self.solver in SolverNames.gluecard4:
            self.cenc = self.encmap['native']
        else:
            assert self.cenc != self.encmap['native'], 'Only Minicard-like solvers can handle cardinality constraints natively'

        if self.config == 'none':
            self.config = None

        if self.config:
            if self.config == 'all':
                all_flags = True
                self.config = None
            elif self.config == 'allbutf':
                all_flags = True
            else:
                # base configuration
                self.bounds = True
                self.corner = True
                self.lenlb = True
                self.nofocc = True
                self.pdeps = True
                self.pop_prev = True
                self.tail = True

                if self.approach == 'sat':
                    self.phases = True
                elif self.approach == 'rc2':
                    self.adapt = True
                elif self.approach in ('lbx', 'mcsls'):
                    self.dcalls = True

                if self.config in ('e', 'f', 'g'):
                    # these are separated in dependency parsing
                    pass
                elif self.config == 'h':
                    # forward and backward value propagation
                    self.bprop = True
                    self.fprop = True

        if all_flags:
            self.bounds = True
            self.bprop = True
            self.corner = True
            self.fprop = True
            self.lenlb = True
            self.nofocc = True
            self.pdeps = True
            self.pop_prev = True
            self.tail = True

            if self.approach == 'sat':
                self.phases = True
            elif self.approach == 'rc2':
                self.adapt = True
            elif self.approach in ('lbx', 'mcsls'):
                self.dcalls = True

        # finally, saving the file names
        self.files = args

    def usage(self):
        """
            Prints usage message.
        """

        print('Usage:', os.path.basename(sys.argv[0]), '[options] json-file')
        print('Options:')
        print('        -1, --adapt                Try to detect AtMost1 constraints')
        print('        -A, --all                  Apply all the flags relevant for a selected approach')
        print('        -a, --approach=<string>    Problem solving approach')
        print('                                   Available values: lbx, lsu, mcsls, rc2, sat (default = rc2)')
        print('        --allow-dummy              Allow dummy instructions to appear in the program')
        print('        -b, --backprop             Apply back-propagation constraints')
        print('        -B, --bounds               Detect and applies bounds on the operations positions')
        print('        -c, --csv                  Print solution in CSV')
        print('        -C, --corner               Apply corner/edge constraints')
        print('        --config=<string>          Run one of the configurations for the paper')
        print('                                   Available values: none, base, e, f, g, h, all (default = none)')
        print('                                   \'none\' includes no flags')
        print('                                   \'base\' equals \'a\'+\'b\'+\'c\'+\'d\'')
        print('                                   \'all\' equals \'-A\'')
        print('        -d, --dcalls               Apply clause D calls')
        print('        -D, --dump                 Dump encoding to stderr')
        print('        -e, --cardenc=<string>     Cardinality encoding to use')
        print('                                   Available values: bw, cardn, kmtot, ladder, mtot, pw, seqc, sortn, tot (default = seqc)')
        print('        -E, --enum=<string>        How many solutions to compute')
        print('                                   Available values: [1 .. all] (default: 1)')
        print('        -f, --forwprop             Apply forward-propagation constraints')
        print('        -h, --help                 Show this message')
        print('        -i, --init                 Bootstrap the solver with the initial solution (if exists)')
        print('        -l, --blo                  Use BLO and stratification')
        print('                                   Available values: basic, div, cluster, none, full (default = none)')
        print('        -L, --lb                   Compute and apply a lower bound on the program length')
        print('        -m, --minimize             Use a heuristic unsatisfiable core minimizer')
        print('        -M, --maxlen=<int>         Update the maximum number of instructions')
        print('                                   Available values: [1 .. INT_MAX], none (default: none)')
        print('        -n, --nods                 Do not allow DUP and SWAP instructions')
        print('        -N, --nofocc               Enforce the number of occurrences per operation')
        print('        -o, --obj=<string>         Objective function to use')
        print('                                   Available values: none, gas, len, size (default = none)')
        print('        -p, --pdeps                Analyse operation dependency and precedence')
        print('        -P, --phases               Apply phase saving in SAT solver')
        print('        --ponly                    Simple output (program only with no stack)')
        print('        --pop-prev                 Enforce operations preceding any POP to be either POP, STORE, or SWAP')
        print('        -R, --regsz=<int>          Update the maximum number of registers')
        print('                                   Available values: [1 .. INT_MAX], none (default: none)')
        print('        -s, --solver=<string>      SAT solver to use')
        print('                                   Available values: g3, g4, lgl, mcb, mcm, mpl, m22, mc, mgh (default = g3)')
        print('        -S, --stacksz=<int>        Update the maximum stack size')
        print('                                   Available values: [1 .. INT_MAX], none (default: none)')
        print('        -t, --trim=<int>           How many times to trim unsatisfiable cores')
        print('                                   Available values: [0 .. INT_MAX] (default = 0)')
        print('        -T, --tail                 Apply stack tail analysis')
        print('        -v, --verbose              Be verbose')
        print('        -w, --wasm                 Enable WASM mode')
        print('        -x, --exhaust              Exhaust new unsatisfiable cores')
