#!/usr/bin/env python3
"""
Script de calibration SAT avec timeout pour trouver des configurations
où chaque solveur gagne au moins un test.
"""

import time
import signal
import sys
from concurrent.futures import ThreadPoolExecutor, TimeoutError as FuturesTimeout
from pysat.solvers import Solver
from pysat.formula import CNF
import random

# Timeout par test en secondes
TEST_TIMEOUT = 10

def solve_with_timeout(solver_name: str, cnf: CNF, timeout: float) -> tuple:
    """Résout avec timeout, retourne (temps, sat, timeout_flag)"""
    with ThreadPoolExecutor(max_workers=1) as executor:
        start = time.perf_counter()
        try:
            with Solver(name=solver_name, bootstrap_with=cnf) as solver:
                future = executor.submit(solver.solve)
                result = future.result(timeout=timeout)
                elapsed = time.perf_counter() - start
                return (elapsed, result, False)
        except FuturesTimeout:
            return (timeout, None, True)
        except Exception as e:
            return (0, None, f"Error: {e}")

# ============ GÉNÉRATEURS DE PROBLÈMES ============

def generate_pigeonhole(pigeons: int, holes: int) -> CNF:
    """Pigeonhole principle: n pigeons dans n-1 trous (UNSAT)"""
    cnf = CNF()
    def var(p, h): return p * holes + h + 1

    # Chaque pigeon dans au moins un trou
    for p in range(pigeons):
        cnf.append([var(p, h) for h in range(holes)])

    # Pas deux pigeons dans le même trou
    for h in range(holes):
        for p1 in range(pigeons):
            for p2 in range(p1 + 1, pigeons):
                cnf.append([-var(p1, h), -var(p2, h)])

    return cnf

def generate_random_ksat(n_vars: int, k: int = 3, ratio: float = 4.26, seed: int = None) -> CNF:
    """Random k-SAT avec ratio clauses/variables"""
    if seed is not None:
        random.seed(seed)
    cnf = CNF()
    n_clauses = int(n_vars * ratio)
    for _ in range(n_clauses):
        clause = []
        vars_chosen = random.sample(range(1, n_vars + 1), k)
        for v in vars_chosen:
            clause.append(v if random.random() > 0.5 else -v)
        cnf.append(clause)
    return cnf

def generate_queens(n: int) -> CNF:
    """N-Queens encodage CNF"""
    cnf = CNF()
    def var(r, c): return r * n + c + 1

    # Au moins une reine par ligne
    for r in range(n):
        cnf.append([var(r, c) for c in range(n)])

    # Au plus une par ligne, colonne, diagonales
    for r in range(n):
        for c1 in range(n):
            for c2 in range(c1 + 1, n):
                cnf.append([-var(r, c1), -var(r, c2)])

    for c in range(n):
        for r1 in range(n):
            for r2 in range(r1 + 1, n):
                cnf.append([-var(r1, c), -var(r2, c)])

    for r in range(n):
        for c in range(n):
            for d in range(1, n):
                if r + d < n and c + d < n:
                    cnf.append([-var(r, c), -var(r + d, c + d)])
                if r + d < n and c - d >= 0:
                    cnf.append([-var(r, c), -var(r + d, c - d)])

    return cnf

def generate_graph_coloring(n_vertices: int, n_colors: int, edge_prob: float, seed: int = None) -> CNF:
    """Graph coloring aléatoire"""
    if seed is not None:
        random.seed(seed)
    cnf = CNF()
    def var(v, c): return v * n_colors + c + 1

    # Chaque sommet a au moins une couleur
    for v in range(n_vertices):
        cnf.append([var(v, c) for c in range(n_colors)])

    # Au plus une couleur par sommet
    for v in range(n_vertices):
        for c1 in range(n_colors):
            for c2 in range(c1 + 1, n_colors):
                cnf.append([-var(v, c1), -var(v, c2)])

    # Arêtes aléatoires: sommets adjacents != même couleur
    for v1 in range(n_vertices):
        for v2 in range(v1 + 1, n_vertices):
            if random.random() < edge_prob:
                for c in range(n_colors):
                    cnf.append([-var(v1, c), -var(v2, c)])

    return cnf

def generate_latin_square(n: int, n_fixed: int = 0, seed: int = None) -> CNF:
    """Latin Square partiel - chaque valeur une fois par ligne/colonne"""
    if seed is not None:
        random.seed(seed)
    cnf = CNF()
    def var(r, c, v): return r * n * n + c * n + v + 1

    # Chaque cellule a au moins une valeur
    for r in range(n):
        for c in range(n):
            cnf.append([var(r, c, v) for v in range(n)])

    # Au plus une valeur par cellule
    for r in range(n):
        for c in range(n):
            for v1 in range(n):
                for v2 in range(v1 + 1, n):
                    cnf.append([-var(r, c, v1), -var(r, c, v2)])

    # Chaque valeur une fois par ligne
    for r in range(n):
        for v in range(n):
            for c1 in range(n):
                for c2 in range(c1 + 1, n):
                    cnf.append([-var(r, c1, v), -var(r, c2, v)])

    # Chaque valeur une fois par colonne
    for c in range(n):
        for v in range(n):
            for r1 in range(n):
                for r2 in range(r1 + 1, n):
                    cnf.append([-var(r1, c, v), -var(r2, c, v)])

    # Fixer quelques cellules aléatoirement
    if n_fixed > 0:
        cells = [(r, c) for r in range(n) for c in range(n)]
        random.shuffle(cells)
        for i in range(min(n_fixed, len(cells))):
            r, c = cells[i]
            v = random.randint(0, n - 1)
            cnf.append([var(r, c, v)])

    return cnf

# ============ BENCHMARK ============

SOLVERS = ['cadical195', 'glucose42', 'minisat22']
SOLVER_SHORT = {'cadical195': 'CaDiCaL', 'glucose42': 'Glucose', 'minisat22': 'MiniSat'}

def benchmark_config(name: str, cnf: CNF, timeout: float = TEST_TIMEOUT) -> dict:
    """Benchmark un problème sur tous les solveurs"""
    results = {'name': name, 'vars': cnf.nv, 'clauses': len(cnf.clauses)}
    times = {}
    winner = None
    best_time = float('inf')

    for solver in SOLVERS:
        elapsed, sat, timed_out = solve_with_timeout(solver, cnf, timeout)
        short = SOLVER_SHORT[solver]

        if timed_out:
            times[short] = f"TIMEOUT ({timeout}s)"
        elif isinstance(timed_out, str):
            times[short] = timed_out
        else:
            times[short] = f"{elapsed*1000:.1f}ms"
            results['sat'] = sat
            if elapsed < best_time:
                best_time = elapsed
                winner = short

    results['times'] = times
    results['winner'] = winner
    results['best_time'] = best_time
    return results

def print_result(r: dict):
    """Affiche un résultat de benchmark"""
    sat_str = "SAT" if r.get('sat') else "UNSAT" if r.get('sat') is False else "?"
    print(f"\n{r['name']}")
    print(f"  Variables: {r['vars']}, Clauses: {r['clauses']}, Result: {sat_str}")
    print(f"  Times: {r['times']}")
    print(f"  Winner: {r['winner']} ({r['best_time']*1000:.1f}ms)" if r['winner'] else "  No winner (timeout)")

# ============ CONFIGURATIONS À TESTER ============

def run_calibration():
    print("=" * 60)
    print("CALIBRATION SAT SOLVERS - Recherche de variété")
    print("=" * 60)

    all_results = []

    # === Test 1: Pigeonhole (UNSAT) - différentes tailles ===
    print("\n--- PIGEONHOLE (UNSAT) ---")
    for pigeons in [8, 9, 10, 11]:
        holes = pigeons - 1
        r = benchmark_config(f"Pigeonhole {pigeons}->{holes}", generate_pigeonhole(pigeons, holes))
        print_result(r)
        all_results.append(r)

    # === Test 2: Random 3-SAT - différents ratios ===
    print("\n--- RANDOM 3-SAT ---")
    for n_vars in [200, 250, 300]:
        for ratio in [3.5, 3.8, 4.0, 4.26, 4.5]:
            r = benchmark_config(
                f"Random 3-SAT {n_vars}v ratio={ratio}",
                generate_random_ksat(n_vars, k=3, ratio=ratio, seed=42)
            )
            print_result(r)
            all_results.append(r)

    # === Test 3: N-Queens (SAT) - différentes tailles ===
    print("\n--- N-QUEENS (SAT) ---")
    for n in [30, 35, 40, 45, 50]:
        r = benchmark_config(f"{n}-Queens", generate_queens(n))
        print_result(r)
        all_results.append(r)

    # === Test 4: Graph Coloring ===
    print("\n--- GRAPH COLORING ---")
    for n_vertices in [60, 80, 100]:
        for n_colors in [4, 5, 6]:
            for edge_prob in [0.10, 0.15, 0.20]:
                r = benchmark_config(
                    f"GraphColor {n_vertices}v {n_colors}c prob={edge_prob}",
                    generate_graph_coloring(n_vertices, n_colors, edge_prob, seed=42)
                )
                print_result(r)
                all_results.append(r)

    # === Test 5: Latin Square ===
    print("\n--- LATIN SQUARE ---")
    for n in [8, 10, 12, 14]:
        for n_fixed in [0, 5, 10]:
            r = benchmark_config(
                f"LatinSquare {n}x{n} fixed={n_fixed}",
                generate_latin_square(n, n_fixed, seed=42)
            )
            print_result(r)
            all_results.append(r)

    # === RÉSUMÉ ===
    print("\n" + "=" * 60)
    print("RÉSUMÉ - Configurations avec variété")
    print("=" * 60)

    wins = {'CaDiCaL': [], 'Glucose': [], 'MiniSat': []}
    for r in all_results:
        if r['winner']:
            wins[r['winner']].append((r['name'], r['best_time']))

    for solver, configs in wins.items():
        print(f"\n{solver} gagne ({len(configs)} tests):")
        for name, t in configs[:5]:  # Top 5
            print(f"  - {name}: {t*1000:.1f}ms")

    # Proposer une configuration variée
    print("\n" + "=" * 60)
    print("CONFIGURATION SUGGÉRÉE")
    print("=" * 60)

    # Chercher un test par solveur avec temps raisonnable (100ms-2s)
    suggested = {}
    for solver in ['CaDiCaL', 'Glucose', 'MiniSat']:
        candidates = [(r['name'], r['best_time'], r) for r in all_results
                      if r['winner'] == solver and 0.1 <= r['best_time'] <= 2.0]
        if candidates:
            # Prendre celui avec le temps le plus proche de 500ms
            best = min(candidates, key=lambda x: abs(x[1] - 0.5))
            suggested[solver] = best
            print(f"{solver}: {best[0]} ({best[1]*1000:.0f}ms)")

    return all_results, suggested

if __name__ == "__main__":
    run_calibration()
