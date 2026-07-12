#!/usr/bin/env python3
"""
SAT Solver - Python wrapper using PySAT with modern solvers
Provides access to championship-winning SAT solvers via a unified interface.

Available Solvers (via PySAT):
    - CaDiCaL 1.9.5: From Armin Biere (Kissat's author), SAT Competition winner
    - CryptoMiniSat 5: XOR-aware solver, champion in cryptographic instances
    - Glucose 4.2.1: Fast for industrial benchmarks
    - Lingeling: Predecessor to CaDiCaL, very stable
    - MapleSAT variants: Competition winners 2016-2018

Usage:
    python sat_solver.py <input.cnf> [--solver cadical195] [--all-solutions]

Input format: DIMACS CNF
Output: SAT/UNSAT with model if satisfiable

Features:
    - Multiple solver backends
    - Solution enumeration
    - Assumption-based solving
    - Performance statistics
"""

import sys
import argparse
import time
from typing import List, Optional, Tuple, Iterator

try:
    from pysat.solvers import Solver, SolverNames
    from pysat.formula import CNF
    PYSAT_AVAILABLE = True
except ImportError:
    PYSAT_AVAILABLE = False


# Solver preference order (best performers first)
RECOMMENDED_SOLVERS = [
    ('cadical195', 'CaDiCaL 1.9.5 - SAT Competition champion'),
    ('cryptominisat5', 'CryptoMiniSat 5 - XOR-aware solver'),
    ('glucose42', 'Glucose 4.2.1 - Fast industrial solver'),
    ('maplechrono', 'MapleChrono - Chronological backtracking'),
    ('lingeling', 'Lingeling - Very stable solver'),
    ('minisat22', 'MiniSat 2.2 - Classic reference solver'),
]


def parse_dimacs_cnf(filename: str) -> Tuple[int, List[List[int]]]:
    """
    Parse DIMACS CNF file.

    Returns:
        Tuple of (num_variables, clauses)
    """
    clauses = []
    num_vars = 0

    with open(filename, 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('c') or line.startswith('%'):
                continue
            if line.startswith('p'):
                parts = line.split()
                if len(parts) >= 4:
                    num_vars = int(parts[2])
                continue

            # Parse clause
            literals = [int(x) for x in line.split() if x != '0']
            if literals:
                clauses.append(literals)

    return num_vars, clauses


def solve_sat(
    clauses: List[List[int]],
    solver_name: str = 'cadical195',
    assumptions: Optional[List[int]] = None,
    verbose: bool = False
) -> Tuple[bool, Optional[List[int]], dict]:
    """
    Solve SAT problem using specified solver.

    Args:
        clauses: List of clauses (each clause is a list of literals)
        solver_name: Name of the solver to use
        assumptions: Optional list of assumption literals
        verbose: Print debug information

    Returns:
        Tuple of (is_satisfiable, model, statistics)
    """
    if not PYSAT_AVAILABLE:
        return False, None, {'error': 'PySAT not installed'}

    stats = {
        'solver': solver_name,
        'num_clauses': len(clauses),
        'num_variables': max(abs(lit) for clause in clauses for lit in clause) if clauses else 0,
    }

    start_time = time.time()

    try:
        with Solver(name=solver_name, bootstrap_with=clauses) as solver:
            if verbose:
                print(f"Using solver: {solver_name}", file=sys.stderr)
                print(f"Clauses: {len(clauses)}, Variables: {stats['num_variables']}", file=sys.stderr)

            # Solve with optional assumptions
            if assumptions:
                result = solver.solve(assumptions=assumptions)
            else:
                result = solver.solve()

            stats['solve_time'] = time.time() - start_time

            if result:
                model = solver.get_model()
                stats['status'] = 'SAT'
                return True, model, stats
            else:
                stats['status'] = 'UNSAT'
                # Try to get unsat core if assumptions were used
                if assumptions:
                    core = solver.get_core()
                    stats['unsat_core'] = core
                return False, None, stats

    except Exception as e:
        stats['error'] = str(e)
        stats['solve_time'] = time.time() - start_time
        return False, None, stats


def enumerate_solutions(
    clauses: List[List[int]],
    solver_name: str = 'cadical195',
    max_solutions: int = 10,
    verbose: bool = False
) -> Iterator[List[int]]:
    """
    Enumerate multiple solutions using blocking clauses.

    Args:
        clauses: List of clauses
        solver_name: Solver to use
        max_solutions: Maximum number of solutions to find
        verbose: Print debug information

    Yields:
        Solutions (models) as lists of literals
    """
    if not PYSAT_AVAILABLE:
        return

    working_clauses = [clause[:] for clause in clauses]
    count = 0

    with Solver(name=solver_name, bootstrap_with=working_clauses) as solver:
        while count < max_solutions:
            if not solver.solve():
                break

            model = solver.get_model()
            yield model
            count += 1

            # Add blocking clause to exclude this solution
            blocking_clause = [-lit for lit in model]
            solver.add_clause(blocking_clause)


def benchmark_solvers(clauses: List[List[int]], timeout: float = 10.0) -> dict:
    """
    Benchmark all available solvers on the given problem.

    Args:
        clauses: SAT problem clauses
        timeout: Maximum time per solver

    Returns:
        Dictionary of solver results
    """
    results = {}

    for solver_name, description in RECOMMENDED_SOLVERS:
        try:
            start = time.time()
            is_sat, model, stats = solve_sat(clauses, solver_name)
            elapsed = time.time() - start

            if elapsed > timeout:
                results[solver_name] = {'status': 'TIMEOUT', 'time': elapsed}
            else:
                results[solver_name] = {
                    'status': 'SAT' if is_sat else 'UNSAT',
                    'time': elapsed,
                    'description': description
                }
        except Exception as e:
            results[solver_name] = {'status': 'ERROR', 'error': str(e)}

    return results


def main():
    parser = argparse.ArgumentParser(
        description='SAT Solver using PySAT (CaDiCaL, CryptoMiniSat, Glucose, etc.)',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Available solvers:
  cadical195     CaDiCaL 1.9.5 - SAT Competition champion (default)
  cryptominisat5 CryptoMiniSat 5 - XOR-aware solver
  glucose42      Glucose 4.2.1 - Fast industrial solver
  maplechrono    MapleChrono - Chronological backtracking
  lingeling      Lingeling - Very stable solver
  minisat22      MiniSat 2.2 - Classic reference solver

Examples:
  python sat_solver.py problem.cnf
  python sat_solver.py problem.cnf --solver cryptominisat5
  python sat_solver.py problem.cnf --all-solutions --max 5
  python sat_solver.py problem.cnf --benchmark
        """
    )
    parser.add_argument('input_file', help='Input file in DIMACS CNF format')
    parser.add_argument('--solver', '-s', default='cadical195',
                        help='Solver to use (default: cadical195)')
    parser.add_argument('--all-solutions', '-a', action='store_true',
                        help='Enumerate all solutions')
    parser.add_argument('--max', '-m', type=int, default=10,
                        help='Maximum number of solutions (default: 10)')
    parser.add_argument('--benchmark', '-b', action='store_true',
                        help='Benchmark all solvers')
    parser.add_argument('--verbose', '-v', action='store_true',
                        help='Verbose output')
    parser.add_argument('--list-solvers', '-l', action='store_true',
                        help='List available solvers and exit')

    args = parser.parse_args()

    if not PYSAT_AVAILABLE:
        print("Error: PySAT not installed. Run: pip install python-sat", file=sys.stderr)
        return 1

    if args.list_solvers:
        print("Available SAT solvers:")
        for name, desc in RECOMMENDED_SOLVERS:
            print(f"  {name:15s} - {desc}")
        return 0

    try:
        # Parse input
        num_vars, clauses = parse_dimacs_cnf(args.input_file)

        if args.verbose:
            print(f"Loaded CNF: {num_vars} variables, {len(clauses)} clauses", file=sys.stderr)

        if args.benchmark:
            # Benchmark all solvers
            print(f"Benchmarking on {args.input_file}...")
            results = benchmark_solvers(clauses)
            print("\nResults:")
            for solver, data in sorted(results.items(), key=lambda x: x[1].get('time', float('inf'))):
                status = data['status']
                time_str = f"{data.get('time', 0):.4f}s" if 'time' in data else 'N/A'
                print(f"  {solver:15s}: {status:6s} ({time_str})")
            return 0

        if args.all_solutions:
            # Enumerate solutions
            print(f"s SATISFIABLE")
            count = 0
            for model in enumerate_solutions(clauses, args.solver, args.max, args.verbose):
                count += 1
                positive_lits = [lit for lit in model if lit > 0]
                print(f"v {' '.join(str(lit) for lit in model)} 0")
            if count == 0:
                print("s UNSATISFIABLE")
                return 1
            print(f"c Found {count} solution(s)")
            return 0

        # Single solution
        is_sat, model, stats = solve_sat(clauses, args.solver, verbose=args.verbose)

        if is_sat:
            print("s SATISFIABLE")
            print(f"v {' '.join(str(lit) for lit in model)} 0")
            if args.verbose:
                print(f"c Solve time: {stats.get('solve_time', 0):.4f}s", file=sys.stderr)
        else:
            print("s UNSATISFIABLE")
            if 'unsat_core' in stats:
                print(f"c UNSAT core: {stats['unsat_core']}")
            return 1

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
