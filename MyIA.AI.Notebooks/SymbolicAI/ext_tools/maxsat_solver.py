#!/usr/bin/env python3
"""
MaxSAT Solver - Python wrapper for Tweety using PySAT RC2
Solves Maximum Satisfiability problems using the RC2 algorithm.

Usage:
    python maxsat_solver.py <input.wcnf>

Input format: Weighted DIMACS CNF (WCNF)
    - Hard clauses start with weight = top_weight
    - Soft clauses have finite weights
Output: Optimal solution and cost
"""

import sys
import argparse
from pysat.examples.rc2 import RC2
from pysat.formula import WCNF


def parse_wcnf(filename):
    """Parse Weighted DIMACS CNF file"""
    wcnf = WCNF()

    with open(filename, 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('c'):
                continue

            if line.startswith('p'):
                # p wcnf <nvars> <nclauses> <top_weight>
                parts = line.split()
                if len(parts) >= 5:
                    wcnf.topw = int(parts[4])
                continue

            # Parse weighted clause: <weight> <lit1> <lit2> ... <litn> 0
            parts = [int(x) for x in line.split()]
            if not parts or parts[-1] != 0:
                continue

            weight = parts[0]
            clause = parts[1:-1]  # Exclude weight and trailing 0

            if weight == wcnf.topw:
                # Hard clause
                wcnf.append(clause, weight=None)
            else:
                # Soft clause
                wcnf.append(clause, weight=weight)

    return wcnf


def solve_maxsat(wcnf, verbose=False):
    """Solve MaxSAT using RC2 algorithm"""
    try:
        with RC2(wcnf) as solver:
            # Compute optimal solution
            model = solver.compute()

            if model is None:
                return None, None

            # Get cost
            cost = solver.cost

            return model, cost

    except Exception as e:
        if verbose:
            print(f"Error during solving: {e}", file=sys.stderr)
        return None, None


def main():
    parser = argparse.ArgumentParser(description='MaxSAT Solver (RC2)')
    parser.add_argument('input_file', help='Input file in Weighted DIMACS CNF format')
    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose output')
    parser.add_argument('--enumerate', '-e', type=int, metavar='K', help='Enumerate top-K solutions')

    args = parser.parse_args()

    try:
        # Parse input
        wcnf = parse_wcnf(args.input_file)

        if args.verbose:
            print(f"Loaded WCNF: {wcnf.nv} variables, {len(wcnf.hard)} hard clauses, {len(wcnf.soft)} soft clauses", file=sys.stderr)

        if args.enumerate:
            # Enumerate top-K solutions
            with RC2(wcnf) as solver:
                solutions = []
                for i, model in enumerate(solver.enumerate(), start=1):
                    cost = solver.cost
                    solutions.append((model, cost))
                    if args.verbose:
                        print(f"Solution {i}: cost={cost}", file=sys.stderr)
                    if i >= args.enumerate:
                        break

                # Output all solutions
                print(f"s OPTIMUM FOUND")
                for idx, (model, cost) in enumerate(solutions, start=1):
                    print(f"o {cost}")
                    print(f"v {' '.join(str(lit) for lit in model)} 0")
        else:
            # Single solution
            model, cost = solve_maxsat(wcnf, args.verbose)

            if model is None:
                print("s UNSATISFIABLE")
                return 1

            # Output in DIMACS format
            print(f"s OPTIMUM FOUND")
            print(f"o {cost}")
            print(f"v {' '.join(str(lit) for lit in model)} 0")

        return 0

    except FileNotFoundError:
        print(f"Error: File '{args.input_file}' not found", file=sys.stderr)
        return 1
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        if args.verbose:
            import traceback
            traceback.print_exc()
        return 1


if __name__ == '__main__':
    sys.exit(main())
