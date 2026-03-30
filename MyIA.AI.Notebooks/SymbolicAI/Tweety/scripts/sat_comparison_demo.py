#!/usr/bin/env python3
"""
Demonstration amelioree de comparaison des solveurs SAT
Compare les performances sur des problemes SAT classiques de difficulte croissante
"""

import time
import random
from typing import List, Tuple

try:
    from pysat.solvers import Solver, SolverNames
    PYSAT_AVAILABLE = True
except ImportError:
    PYSAT_AVAILABLE = False
    print("ERREUR: python-sat non installe. Executez: pip install python-sat")
    exit(1)


def generate_pigeonhole(n_pigeons: int, n_holes: int) -> List[List[int]]:
    """
    Genere le probleme du pigeonnier: n pigeons dans n-1 trous (UNSAT classique)

    Variables: x_{i,j} = pigeon i dans trou j (1 <= i <= n_pigeons, 1 <= j <= n_holes)
    Encoding: variable x_{i,j} = (i-1)*n_holes + j
    """
    clauses = []

    # 1. Chaque pigeon doit aller dans au moins un trou
    for i in range(1, n_pigeons + 1):
        clause = [(i-1) * n_holes + j for j in range(1, n_holes + 1)]
        clauses.append(clause)

    # 2. Aucun trou ne peut contenir plus d'un pigeon
    for j in range(1, n_holes + 1):
        for i1 in range(1, n_pigeons + 1):
            for i2 in range(i1 + 1, n_pigeons + 1):
                var1 = (i1-1) * n_holes + j
                var2 = (i2-1) * n_holes + j
                clauses.append([-var1, -var2])

    return clauses


def generate_nqueens_sat(n: int) -> List[List[int]]:
    """
    Encode le probleme des N-Reines en SAT

    Variables: x_{i,j} = reine en position (i,j) (1 <= i,j <= n)
    Encoding: variable x_{i,j} = (i-1)*n + j
    """
    clauses = []

    def var(i, j):
        return (i-1) * n + j

    # 1. Au moins une reine par ligne
    for i in range(1, n + 1):
        clauses.append([var(i, j) for j in range(1, n + 1)])

    # 2. Au plus une reine par ligne
    for i in range(1, n + 1):
        for j1 in range(1, n + 1):
            for j2 in range(j1 + 1, n + 1):
                clauses.append([-var(i, j1), -var(i, j2)])

    # 3. Au plus une reine par colonne
    for j in range(1, n + 1):
        for i1 in range(1, n + 1):
            for i2 in range(i1 + 1, n + 1):
                clauses.append([-var(i1, j), -var(i2, j)])

    # 4. Au plus une reine par diagonale (/)
    for d in range(-(n-2), n-1):
        positions = []
        for i in range(1, n + 1):
            j = i - d
            if 1 <= j <= n:
                positions.append((i, j))
        for idx1, (i1, j1) in enumerate(positions):
            for i2, j2 in positions[idx1 + 1:]:
                clauses.append([-var(i1, j1), -var(i2, j2)])

    # 5. Au plus une reine par diagonale (\)
    for d in range(2, 2*n):
        positions = []
        for i in range(1, n + 1):
            j = d - i
            if 1 <= j <= n:
                positions.append((i, j))
        for idx1, (i1, j1) in enumerate(positions):
            for i2, j2 in positions[idx1 + 1:]:
                clauses.append([-var(i1, j1), -var(i2, j2)])

    return clauses


def generate_random_3sat(n_vars: int, ratio: float = 4.26) -> List[List[int]]:
    """
    Genere un probleme 3-SAT aleatoire

    Args:
        n_vars: Nombre de variables
        ratio: Ratio clauses/variables (4.26 = seuil de transition de phase)
    """
    n_clauses = int(n_vars * ratio)
    clauses = []

    for _ in range(n_clauses):
        # 3 litteraux aleatoires differents
        lits = random.sample(range(1, n_vars + 1), 3)
        # Negation aleatoire
        clause = [lit * (1 if random.random() < 0.5 else -1) for lit in lits]
        clauses.append(clause)

    return clauses


def generate_graph_coloring(n_vertices: int, edges: List[Tuple[int, int]], n_colors: int) -> List[List[int]]:
    """
    Encode le probleme de coloration de graphe en SAT

    Variables: x_{v,c} = sommet v a la couleur c
    """
    clauses = []

    def var(v, c):
        return (v-1) * n_colors + c

    # 1. Chaque sommet doit avoir au moins une couleur
    for v in range(1, n_vertices + 1):
        clauses.append([var(v, c) for c in range(1, n_colors + 1)])

    # 2. Chaque sommet a au plus une couleur
    for v in range(1, n_vertices + 1):
        for c1 in range(1, n_colors + 1):
            for c2 in range(c1 + 1, n_colors + 1):
                clauses.append([-var(v, c1), -var(v, c2)])

    # 3. Sommets adjacents doivent avoir des couleurs differentes
    for u, v in edges:
        for c in range(1, n_colors + 1):
            clauses.append([-var(u, c), -var(v, c)])

    return clauses


def benchmark_problem(name: str, clauses: List[List[int]], solvers: List[str]) -> dict:
    """
    Benchmark un probleme SAT avec plusieurs solveurs
    """
    n_vars = max(abs(lit) for clause in clauses for lit in clause) if clauses else 0
    n_clauses = len(clauses)

    print(f"\n--- {name} ---")
    print(f"Variables: {n_vars}, Clauses: {n_clauses}, Ratio: {n_clauses/n_vars:.2f}" if n_vars > 0 else "Probleme vide")

    results = {}

    for solver_name in solvers:
        try:
            start = time.perf_counter()
            with Solver(name=solver_name, bootstrap_with=clauses) as solver:
                result = solver.solve()
                elapsed_ms = (time.perf_counter() - start) * 1000

                status = "SAT" if result else "UNSAT"

                # Pour les petits problemes SAT, montrer un modele partiel
                if result and n_vars <= 20:
                    model = solver.get_model()
                    positive_vars = sorted([lit for lit in model if lit > 0])
                    model_str = str(positive_vars[:10])
                    if len(positive_vars) > 10:
                        model_str = model_str[:-1] + ", ...]"
                    print(f"  {solver_name:15s}: {status:5s} en {elapsed_ms:7.3f}ms, modele={model_str}")
                else:
                    print(f"  {solver_name:15s}: {status:5s} en {elapsed_ms:7.3f}ms")

                results[solver_name] = {'status': status, 'time_ms': elapsed_ms}

        except Exception as e:
            print(f"  {solver_name:15s}: ERREUR - {e}")
            results[solver_name] = {'status': 'ERROR', 'error': str(e)}

    return results


def main():
    """Demonstration principale"""

    if not PYSAT_AVAILABLE:
        return

    print("=" * 70)
    print("COMPARAISON DE SOLVEURS SAT - Problemes Classiques")
    print("=" * 70)

    # Detecter les solveurs disponibles
    available_solvers = ['cadical195', 'glucose42', 'minisat22']
    solvers_to_test = []

    for solver in available_solvers:
        try:
            # Test rapide de disponibilite
            with Solver(name=solver, bootstrap_with=[[1]]) as s:
                s.solve()
            solvers_to_test.append(solver)
        except:
            pass

    if not solvers_to_test:
        print("ERREUR: Aucun solveur disponible")
        return

    print(f"\nSolveurs testes: {', '.join(solvers_to_test)}\n")

    # ===== Test 1: Probleme SAT trivial (pour reference) =====
    clauses_simple = [[1, 2], [-1, 3], [2, -3]]
    benchmark_problem("Test 1: SAT Simple (3 clauses, 3 variables)",
                     clauses_simple, solvers_to_test)

    # ===== Test 2: Probleme UNSAT trivial =====
    clauses_unsat = [[1], [-1]]
    benchmark_problem("Test 2: UNSAT Trivial (contradiction directe)",
                     clauses_unsat, solvers_to_test)

    # ===== Test 3: Pigeonhole Principle (UNSAT classique) =====
    # 5 pigeons dans 4 trous - demontre la difficulte UNSAT
    clauses_pigeon = generate_pigeonhole(5, 4)
    benchmark_problem("Test 3: Pigeonhole 5->4 (UNSAT, ~40 clauses)",
                     clauses_pigeon, solvers_to_test)

    # ===== Test 4: 8-Reines (SAT classique) =====
    clauses_queens = generate_nqueens_sat(8)
    benchmark_problem("Test 4: 8-Reines (SAT, ~500 clauses)",
                     clauses_queens, solvers_to_test)

    # ===== Test 5: Random 3-SAT au seuil critique =====
    random.seed(42)  # Pour reproductibilite
    clauses_random = generate_random_3sat(50, ratio=4.26)
    benchmark_problem("Test 5: Random 3-SAT (50 vars, seuil critique 4.26)",
                     clauses_random, solvers_to_test)

    # ===== Test 6: Graph Coloring (cycle de 10 sommets, 3 couleurs) =====
    edges_cycle = [(i, i+1) for i in range(1, 10)] + [(10, 1)]
    clauses_coloring = generate_graph_coloring(10, edges_cycle, 3)
    benchmark_problem("Test 6: 3-Coloration Cycle-10 (SAT, ~150 clauses)",
                     clauses_coloring, solvers_to_test)

    # ===== Test 7: Random 3-SAT plus grand =====
    clauses_large = generate_random_3sat(100, ratio=4.26)
    benchmark_problem("Test 7: Random 3-SAT (100 vars, seuil critique)",
                     clauses_large, solvers_to_test)

    print("\n" + "=" * 70)
    print("OBSERVATIONS:")
    print("- Problemes triviaux (Tests 1-2): Tous les solveurs ~0ms")
    print("- Pigeonhole (Test 3): Demontre la difficulte UNSAT")
    print("- 8-Reines (Test 4): Probleme SAT structure classique")
    print("- Random 3-SAT (Tests 5,7): Au seuil critique (ratio 4.26)")
    print("- Les differences emergent sur les problemes >50 variables")
    print("=" * 70)


if __name__ == '__main__':
    main()
