"""
Fix App-1-NQueens: recycle student solutions into Exemple cells + new stubs.

Part of Issue #463: recyclage App-1..App-11.
"""

import json


def cell_code(source_lines):
    """Helper to create a code cell from a list of strings."""
    return {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": source_lines,
    }


def cell_md(source_lines):
    """Helper to create a markdown cell."""
    return {
        "cell_type": "markdown",
        "metadata": {},
        "source": source_lines,
    }


def fix_app1():
    path = "MyIA.AI.Notebooks/Search/Applications/CSP/App-1-NQueens.ipynb"
    with open(path, encoding="utf-8") as f:
        nb = json.load(f)

    # --- Ex1: N-Rooks via CP-SAT (cell 41, 53L) ---
    nb["cells"][41] = cell_code([
        "# Exemple resolu : N-Tours via CP-SAT\n",
        "\n",
        "import math\n",
        "import time\n",
        "\n",
        'print("Exemple : N-Tours")\n',
        'print("=" * 50)\n',
        "\n",
        "n = 8\n",
        "\n",
        "from ortools.sat.python import cp_model\n",
        "\n",
        "\n",
        "def count_nrooks_solutions_cpsat(n, time_limit_s=10):\n",
        "    model = cp_model.CpModel()\n",
        '    rooks = [model.NewIntVar(0, n - 1, f"r_{i}") for i in range(n)]\n',
        "    model.AddAllDifferent(rooks)\n",
        "\n",
        "    solver = cp_model.CpSolver()\n",
        "    solver.parameters.max_time_in_seconds = time_limit_s\n",
        "    solver.parameters.enumerate_all_solutions = True\n",
        "\n",
        "    class Counter(cp_model.CpSolverSolutionCallback):\n",
        "        def __init__(self):\n",
        "            super().__init__()\n",
        "            self.count = 0\n",
        "\n",
        "        def on_solution_callback(self):\n",
        "            self.count += 1\n",
        "\n",
        "    cb = Counter()\n",
        "    t0 = time.time()\n",
        "    status = solver.Solve(model, cb)\n",
        "    elapsed_ms = (time.time() - t0) * 1000\n",
        "    return cb.count, solver.StatusName(status), elapsed_ms\n",
        "\n",
        "\n",
        "count, status, elapsed_ms = count_nrooks_solutions_cpsat(n)\n",
        'print("(via CP-SAT)")\n',
        'print("Status solveur:", status)\n',
        'print("Solutions CP-SAT :", count)\n',
        'print("Solutions formule :", math.factorial(n), "(= N!)")\n',
        'print(f"Temps: {elapsed_ms:.1f} ms")\n',
        "\n",
        "if count == math.factorial(n):\n",
        "    print(\"OK : c'est bien N! (donc 40320 pour N=8)\")\n",
        "else:\n",
        "    print(\"Hmm, y'a un truc bizarre\")\n",
    ])

    # Insert Ex1b: N-Bishops
    nb["cells"].insert(42, cell_md([
        "### Exercice 1b : le probleme des N-Fous\n",
        "\n",
        "**Enonce** : adaptez le probleme pour placer $N$ **fous** sur un echiquier\n",
        "$N \\times N$. Les fous attaquent en diagonale.\n",
        "\n",
        "**Consignes** :\n",
        "1. Modelisez avec CP-SAT : chaque fou a une position $(x_i, y_i)$\n",
        "2. Posez les contraintes : deux fous ne peuvent partager la meme diagonale\n",
        "   ($x_i + y_i \\neq x_j + y_j$ et $x_i - y_i \\neq x_j - y_j$)\n",
        "3. Comptez le nombre de solutions pour $N = 8$ et verifiez que c'est 256\n",
    ]))

    nb["cells"].insert(43, cell_code([
        "# Exercice 1b : N-Fous via CP-SAT\n",
        "\n",
        "# TODO: modelisez le probleme des N-Fous avec CP-SAT\n",
        "# Indice : utilisez AddAllDifferent sur les sommes et differences diagonales\n",
        "\n",
        "# Votre code ici\n",
    ]))

    # After insertion (+2):
    # Old cell 42 (md Ex2) -> 44
    # Old cell 43 (code Ex2) -> 45
    # Old cell 44 (md Ex3) -> 46
    # Old cell 45 (code Ex3) -> 47

    # --- Ex2: Backtracking vs Min-Conflicts (now cell 45) ---
    nb["cells"][45] = cell_code([
        "# Exemple resolu : seuil de croisement backtracking / min-conflicts\n",
        "\n",
        "import time\n",
        "import random\n",
        "import numpy as np\n",
        "import matplotlib.pyplot as plt\n",
        "\n",
        'print("Seuil de croisement BT / Min-Conflicts")\n',
        'print("=" * 60)\n',
        "\n",
        "test_sizes = [8, 10, 12, 14, 16, 18, 20]\n",
        "n_trials = 5\n",
        "\n",
        "bt_times = []\n",
        "mc_avg_times = []\n",
        "\n",
        "for n in test_sizes:\n",
        "    # Backtracking (deterministe)\n",
        "    t0 = time.time()\n",
        "    _sol_bt, _nodes_bt = backtracking_fc(n)\n",
        "    bt_ms = (time.time() - t0) * 1000\n",
        "    bt_times.append(bt_ms)\n",
        "\n",
        "    # Min-conflicts (stochastique, moyenne sur 5 essais)\n",
        "    mc_ms_list = []\n",
        "    for trial in range(n_trials):\n",
        "        random.seed(1000 + 17 * trial + n)\n",
        "        t0 = time.time()\n",
        "        sol_mc, steps_mc, _hist = min_conflicts(n)\n",
        "        mc_ms_list.append((time.time() - t0) * 1000)\n",
        "\n",
        "    mc_mean = float(np.mean(mc_ms_list))\n",
        "    mc_avg_times.append(mc_mean)\n",
        '    print(f"{n:>4}  {bt_ms:>14.1f}  {mc_mean:>12.1f}")\n',
        "\n",
        "# Trouver le seuil\n",
        "seuil = None\n",
        "for n, bt_ms, mc_ms in zip(test_sizes, bt_times, mc_avg_times):\n",
        "    if mc_ms < bt_ms:\n",
        "        seuil = n\n",
        "        break\n",
        "\n",
        "if seuil:\n",
        '    print(f"\\nSeuil approx : N = {seuil}, min-conflicts est plus rapide")\n',
        "else:\n",
        '    print("\\nPas de croisement sur cette plage")\n',
        "\n",
        "# Plot\n",
        "fig, ax = plt.subplots(figsize=(9, 4))\n",
        "ax.plot(test_sizes, bt_times, 'o-', label='Backtracking FC+MRV')\n",
        "ax.plot(test_sizes, mc_avg_times, 's-', label='Min-Conflicts (moy 5)')\n",
        "ax.set_xlabel('N')\n",
        "ax.set_ylabel('Temps (ms)')\n",
        "ax.set_title('Croisement BT vs Min-Conflicts')\n",
        "ax.grid(True, alpha=0.3)\n",
        "ax.legend()\n",
        "plt.tight_layout()\n",
        "plt.show()\n",
    ])

    # Insert Ex2b: extended range
    nb["cells"].insert(46, cell_md([
        "### Exercice 2b : plage etendue jusqu'a N=50\n",
        "\n",
        "**Enonce** : relancez la comparaison sur une plage plus large :\n",
        "$N \\in \\{20, 25, 30, 35, 40, 45, 50\\}$.\n",
        "\n",
        "**Consignes** :\n",
        "1. Mesurez les temps de backtracking et min-conflicts pour chaque $N$\n",
        "2. Affichez le graphe et identifiez le seuil\n",
        "3. Attention : backtracking peut devenir tres lent pour $N > 30$,\n",
        "   ajoutez un `time_limit` de 30 secondes par taille\n",
    ]))

    nb["cells"].insert(47, cell_code([
        "# Exercice 2b : plage etendue\n",
        "\n",
        "# TODO: relancez la comparaison pour N = 20..50\n",
        "# Indice : meme pattern que l'exemple, mais avec un time_limit\n",
        "# pour eviter que le backtracking ne prenne trop longtemps\n",
        "\n",
        "# Votre code ici\n",
    ]))

    # After insertion (+4):
    # Old cell 44 (md Ex3) -> 48
    # Old cell 45 (code Ex3) -> 49

    # --- Ex3: Symmetry breaking (now cell 49) ---
    nb["cells"][49] = cell_code([
        "# Exemple resolu : brisure de symetrie\n",
        "\n",
        "import time\n",
        "\n",
        'print("Brisure de symetrie")\n',
        'print("=" * 50)\n',
        "\n",
        "\n",
        "def enumerate_nqueens_solutions_backtracking(n):\n",
        "    queens = [-1] * n\n",
        "    sols = []\n",
        "\n",
        "    def safe(col, row):\n",
        "        for c in range(col):\n",
        "            r = queens[c]\n",
        "            if r == row:\n",
        "                return False\n",
        "            if abs(c - col) == abs(r - row):\n",
        "                return False\n",
        "        return True\n",
        "\n",
        "    def rec(col):\n",
        "        if col == n:\n",
        "            sols.append(queens.copy())\n",
        "            return\n",
        "        for row in range(n):\n",
        "            if safe(col, row):\n",
        "                queens[col] = row\n",
        "                rec(col + 1)\n",
        "                queens[col] = -1\n",
        "\n",
        "    rec(0)\n",
        "    return sols\n",
        "\n",
        "\n",
        "def symmetries(solution):\n",
        '    """Genere les 8 symetries d\'une solution."""\n',
        "    n = len(solution)\n",
        "    pts = [(c, solution[c]) for c in range(n)]\n",
        "\n",
        "    def to_vec(points):\n",
        "        out = [-1] * n\n",
        "        for x, y in points:\n",
        "            out[x] = y\n",
        "        return out\n",
        "\n",
        "    def rot90(points):\n",
        "        return [(n - 1 - y, x) for (x, y) in points]\n",
        "\n",
        "    def refl_vert(points):\n",
        "        return [(n - 1 - x, y) for (x, y) in points]\n",
        "\n",
        "    p0 = pts\n",
        "    p1 = rot90(p0)\n",
        "    p2 = rot90(p1)\n",
        "    p3 = rot90(p2)\n",
        "    all_pts = [p0, p1, p2, p3,\n",
        "               refl_vert(p0), refl_vert(p1),\n",
        "               refl_vert(p2), refl_vert(p3)]\n",
        "    return [to_vec(p) for p in all_pts]\n",
        "\n",
        "\n",
        "def canonical_form(solution):\n",
        "    forms = [tuple(s) for s in symmetries(solution)]\n",
        "    return min(forms)\n",
        "\n",
        "\n",
        "def count_fundamental_solutions(solutions):\n",
        "    canon = set()\n",
        "    for sol in solutions:\n",
        "        canon.add(canonical_form(sol))\n",
        "    return len(canon)\n",
        "\n",
        "\n",
        "n = 8\n",
        "\n",
        "# Enumeration via CP-SAT\n",
        "from ortools.sat.python import cp_model\n",
        "\n",
        "\n",
        "def enumerate_nqueens_cpsat(n, time_limit_s=30):\n",
        "    model = cp_model.CpModel()\n",
        '    queens = [model.NewIntVar(0, n - 1, f"q_{i}") for i in range(n)]\n',
        "    model.AddAllDifferent(queens)\n",
        "    model.AddAllDifferent([queens[i] + i for i in range(n)])\n",
        "    model.AddAllDifferent([queens[i] - i for i in range(n)])\n",
        "\n",
        "    solver = cp_model.CpSolver()\n",
        "    solver.parameters.max_time_in_seconds = time_limit_s\n",
        "    solver.parameters.enumerate_all_solutions = True\n",
        "\n",
        "    class Collector(cp_model.CpSolverSolutionCallback):\n",
        "        def __init__(self):\n",
        "            super().__init__()\n",
        "            self.sols = []\n",
        "\n",
        "        def on_solution_callback(self):\n",
        "            self.sols.append([self.Value(q) for q in queens])\n",
        "\n",
        "    cb = Collector()\n",
        "    t0 = time.time()\n",
        "    solver.Solve(model, cb)\n",
        "    elapsed_ms = (time.time() - t0) * 1000\n",
        "    return cb.sols, elapsed_ms\n",
        "\n",
        "\n",
        "sols, elapsed_ms = enumerate_nqueens_cpsat(n)\n",
        'print(f"Solutions totales : {len(sols)} (temps {elapsed_ms:.1f} ms)")\n',
        "\n",
        "# Comptage par contraintes de brisure simples\n",
        "count_c = sum(\n",
        "    1 for s in sols if s[0] < s[n - 1] and s[0] < n // 2\n",
        ")\n",
        'print(f"Avec contraintes simples : {count_c}")\n',
        "\n",
        "# Solutions fondamentales (reduction par symetries)\n",
        "count_fund = count_fundamental_solutions(sols)\n",
        'print(f"Solutions fondamentales : {count_fund}")\n',
        "\n",
        "if n == 8 and count_fund == 12:\n",
        '    print("OK : on trouve bien 12 solutions fondamentales")\n',
    ])

    # Insert Ex3b: symmetry breaking via CP-SAT constraints
    nb["cells"].insert(50, cell_md([
        "### Exercice 3b : brisure de symetrie directe dans CP-SAT\n",
        "\n",
        "**Enonce** : au lieu d'enumerer toutes les solutions puis de reduire\n",
        "post-facto, ajoutez les contraintes de symetrie **directement dans le\n",
        "modele CP-SAT** pour n'enumerer que les solutions fondamentales.\n",
        "\n",
        "**Consignes** :\n",
        "1. Ajoutez les contraintes $q_0 < q_{N-1}$ et $q_0 < N/2$ au modele\n",
        "2. Enumerez les solutions et verifiez que le compte correspond\n",
        "   aux solutions fondamentales trouvees dans l'exemple\n",
        "3. Mesurez le gain de temps par rapport a l'enumeration complete\n",
    ]))

    nb["cells"].insert(51, cell_code([
        "# Exercice 3b : brisure de symetrie dans CP-SAT\n",
        "\n",
        "# TODO: creez un modele CP-SAT avec contraintes de brisure integrees\n",
        "# Indice : model.Add(queens[0] < queens[n-1])\n",
        "# et model.Add(queens[0] < n // 2)\n",
        "\n",
        "# Votre code ici\n",
    ]))

    with open(path, "w", encoding="utf-8") as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)

    print(f"App-1 updated: {len(nb['cells'])} cells (was 48, +6 new cells)")


if __name__ == "__main__":
    fix_app1()
    print("Done.")
