#!/usr/bin/env python3
"""
MARCO MUS/MCS Enumerator - Python wrapper for Tweety
Based on Z3's MARCO algorithm for enumerating Minimal Unsatisfiable Subsets (MUS)
and Maximal Satisfying Subsets (MSS/MCS).

Usage:
    python marco.py <input.cnf> [--mus-only] [--mss-only]

Input format: DIMACS CNF
Output: MUS and MSS sets
"""

import sys
import argparse
from z3 import *


def get_id(x):
    """Get unique ID for Z3 AST node"""
    return Z3_get_ast_id(x.ctx.ref(), x.as_ast())


class SubsetSolver:
    """Solver for checking subsets of constraints"""

    def __init__(self, constraints):
        self.constraints = constraints
        self.n = len(constraints)
        self.s = Solver()
        self.varcache = {}
        self.idcache = {}

        for i in range(self.n):
            self.s.add(Implies(self.c_var(i), constraints[i]))

    def c_var(self, i):
        """Get control variable for constraint i"""
        if i not in self.varcache:
            v = Bool(str(self.constraints[abs(i)]))
            self.idcache[get_id(v)] = abs(i)
            if i >= 0:
                self.varcache[i] = v
            else:
                self.varcache[i] = Not(v)
        return self.varcache[i]

    def check_subset(self, seed):
        """Check if subset of constraints is satisfiable"""
        assumptions = self.to_c_lits(seed)
        return (self.s.check(assumptions) == sat)

    def to_c_lits(self, seed):
        """Convert seed to control literals"""
        return [self.c_var(i) for i in seed]

    def complement(self, aset):
        """Return complement of set"""
        return set(range(self.n)).difference(aset)

    def seed_from_core(self):
        """Extract seed from unsat core"""
        core = self.s.unsat_core()
        return [self.idcache[get_id(x)] for x in core]

    def shrink(self, seed):
        """Shrink seed to MUS"""
        current = set(seed)
        for i in seed:
            if i not in current:
                continue
            current.remove(i)
            if not self.check_subset(current):
                current = set(self.seed_from_core())
            else:
                current.add(i)
        return current

    def grow(self, seed):
        """Grow seed to MSS"""
        current = list(seed)
        for i in self.complement(current):
            current.append(i)
            if not self.check_subset(current):
                current.pop()
        return current


class MapSolver:
    """Map solver for guiding MUS/MSS search"""

    def __init__(self, n):
        self.solver = Solver()
        self.n = n
        self.all_n = set(range(n))

    def next_seed(self):
        """Get next seed from model"""
        if self.solver.check() == unsat:
            return None
        seed = self.all_n.copy()
        model = self.solver.model()
        for x in model:
            if is_false(model[x]):
                seed.remove(int(x.name()))
        return list(seed)

    def complement(self, aset):
        """Return complement of set"""
        return self.all_n.difference(aset)

    def block_down(self, frompoint):
        """Block down from set"""
        comp = self.complement(frompoint)
        self.solver.add(Or([Bool(str(i)) for i in comp]))

    def block_up(self, frompoint):
        """Block up from set"""
        self.solver.add(Or([Not(Bool(str(i))) for i in frompoint]))


def enumerate_sets(csolver, mapsolver, mus_only=False, mss_only=False):
    """Enumerate MUS and MSS sets"""
    results = {'MUS': [], 'MSS': []}

    while True:
        seed = mapsolver.next_seed()
        if seed is None:
            break

        if csolver.check_subset(seed):
            # Found MSS
            if not mus_only:
                MSS = csolver.grow(seed)
                results['MSS'].append(sorted(MSS))
            else:
                MSS = seed
            mapsolver.block_down(MSS)
        else:
            # Found MUS
            if not mss_only:
                seed = csolver.seed_from_core()
                MUS = csolver.shrink(seed)
                results['MUS'].append(sorted(MUS))
            else:
                MUS = seed
            mapsolver.block_up(MUS)

    return results


def parse_dimacs_cnf(filename):
    """Parse DIMACS CNF file and convert to Z3 constraints"""
    clauses = []
    var_map = {}
    max_var = 0

    with open(filename, 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('c') or line.startswith('%') or line.startswith('0'):
                continue
            if line.startswith('p'):
                # p cnf <nvars> <nclauses>
                parts = line.split()
                max_var = int(parts[2])
                continue

            # Parse clause
            literals = [int(x) for x in line.split() if x != '0']
            if not literals:
                continue

            # Create Z3 variables if needed
            for lit in literals:
                var_num = abs(lit)
                if var_num not in var_map:
                    var_map[var_num] = Bool(f'x{var_num}')

            # Build clause as disjunction
            clause_lits = []
            for lit in literals:
                var_num = abs(lit)
                if lit > 0:
                    clause_lits.append(var_map[var_num])
                else:
                    clause_lits.append(Not(var_map[var_num]))

            if len(clause_lits) == 1:
                clauses.append(clause_lits[0])
            else:
                clauses.append(Or(clause_lits))

    return clauses


def main():
    parser = argparse.ArgumentParser(description='MARCO MUS/MCS Enumerator')
    parser.add_argument('input_file', help='Input file in DIMACS CNF format')
    parser.add_argument('--mus-only', action='store_true', help='Enumerate only MUS')
    parser.add_argument('--mss-only', action='store_true', help='Enumerate only MSS/MCS')
    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose output')

    args = parser.parse_args()

    try:
        # Parse input
        constraints = parse_dimacs_cnf(args.input_file)

        if not constraints:
            print("Error: No constraints found in input file", file=sys.stderr)
            return 1

        # Run MARCO
        csolver = SubsetSolver(constraints)
        msolver = MapSolver(n=csolver.n)
        results = enumerate_sets(csolver, msolver, args.mus_only, args.mss_only)

        # Output results
        if not args.mss_only:
            for mus in results['MUS']:
                if args.verbose:
                    print(f"U {mus}")
                else:
                    print("U", " ".join(str(i) for i in mus))

        if not args.mus_only:
            for mss in results['MSS']:
                if args.verbose:
                    print(f"S {mss}")
                else:
                    print("S", " ".join(str(i) for i in mss))

        return 0

    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        return 1


if __name__ == '__main__':
    sys.exit(main())
