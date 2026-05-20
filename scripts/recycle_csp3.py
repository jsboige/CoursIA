"""
Recycle CSP-3-Advanced: convert student solutions to labeled Exemples
and create new exercise stubs with variants.

Pattern: fix_issue_420.py (PR #453, Issue #420)
Reference: Issue #463
"""

import json

path = "MyIA.AI.Notebooks/Search/Part2-CSP/CSP-3-Advanced.ipynb"

with open(path, encoding="utf-8") as f:
    nb = json.load(f)

# --- Ex1: SEND + MORE = MONEY with CP-SAT (cell[51]=md, cell[52]=code) ---
# Replace code cell[52] with Exemple resolu
nb["cells"][52] = {
    "cell_type": "code",
    "execution_count": None,
    "metadata": {},
    "outputs": [],
    "source": [
        "# Exemple resolu : SEND + MORE = MONEY avec CP-SAT\n",
        "\n",
        "model = cp_model.CpModel()\n",
        "\n",
        "# S et M != 0 (chiffres de tete). Les autres ont un domaine [0, 9].\n",
        "S = model.new_int_var(1, 9, \"S\")\n",
        "E = model.new_int_var(0, 9, \"E\")\n",
        "N = model.new_int_var(0, 9, \"N\")\n",
        "D = model.new_int_var(0, 9, \"D\")\n",
        "M = model.new_int_var(1, 9, \"M\")\n",
        "O = model.new_int_var(0, 9, \"O\")\n",
        "R = model.new_int_var(0, 9, \"R\")\n",
        "Y = model.new_int_var(0, 9, \"Y\")\n",
        "\n",
        "model.add_all_different([S, E, N, D, M, O, R, Y])\n",
        "\n",
        "SEND  = S * 1000 + E * 100 + N * 10 + D\n",
        "MORE  = M * 1000 + O * 100 + R * 10 + E\n",
        "MONEY = M * 10000 + O * 1000 + N * 100 + E * 10 + Y\n",
        "model.add(SEND + MORE == MONEY)\n",
        "\n",
        "solver = cp_model.CpSolver()\n",
        "status = solver.solve(model)\n",
        "\n",
        "if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):\n",
        "    s, e, n, d = solver.value(S), solver.value(E), solver.value(N), solver.value(D)\n",
        "    m, o, r, y = solver.value(M), solver.value(O), solver.value(R), solver.value(Y)\n",
        "    send = 1000 * s + 100 * e + 10 * n + d\n",
        "    more = 1000 * m + 100 * o + 10 * r + e\n",
        "    money = 10000 * m + 1000 * o + 100 * n + 10 * e + y\n",
        "    print(\"Assignation :\")\n",
        "    for lbl, v in zip(\"SENDMORY\", (s, e, n, d, m, o, r, y)):\n",
        "        print(f\"  {lbl} = {v}\")\n",
        "    print(f\"\\n   SEND  = {send}\")\n",
        "    print(f\" + MORE  = {more}\")\n",
        "    print(f\" -------\")\n",
        "    print(f\" = MONEY = {money}\")\n",
        "    print(f\"\\nVerification : {send} + {more} = {send + more}  (attendu {money})\")\n",
        "else:\n",
        "    print(f\"Aucune solution (status = {solver.status_name(status)})\")\n",
    ],
}

# Insert new Ex1b: CROSS + ROADS = DANGER (variant from issue #464)
new_ex1b_md = {
    "cell_type": "markdown",
    "metadata": {},
    "source": [
        "### Exercice 1 : CROSS + ROADS = DANGER\n",
        "\n",
        "**Enonce** : Resolvez le cryptarithme **CROSS + ROADS = DANGER** avec OR-Tools CP-SAT.\n",
        "\n",
        "```\n",
        "    C R O S S\n",
        "  + R O A D S\n",
        "  -----------\n",
        "  D A N G E R\n",
        "```\n",
        "\n",
        "Chaque lettre represente un chiffre distinct (0-9). C, R et D ne peuvent pas valoir 0.\n",
        "\n",
        "**Consignes** :\n",
        "1. Modelez les variables et les contraintes comme dans l'exemple ci-dessus\n",
        "2. Utilisez `add_all_different` pour garantir l'unicite des lettres\n",
        "3. Posez la contrainte arithmetique et resoudrez avec `CpSolver`\n",
        "4. Affichez la solution sous le meme format que l'exemple\n",
    ],
}

new_ex1b_code = {
    "cell_type": "code",
    "execution_count": None,
    "metadata": {},
    "outputs": [],
    "source": [
        "# Exercice 1 : CROSS + ROADS = DANGER\n",
        "\n",
        "# TODO: creez le modele CP-SAT et definissez les variables\n",
        "# Indice : lettres = C, R, O, S, A, D, N, G, E (9 lettres)\n",
        "# Indice : C, R, D != 0 (chiffres de tete)\n",
        "\n",
        "# Votre code ici\n",
    ],
}

nb["cells"].insert(53, new_ex1b_md)
nb["cells"].insert(54, new_ex1b_code)

# After insertion, Ex2 is now at [55]=md, [56]=code
# --- Ex2: N-Reines symmetries (now cells 55=md, 56=code) ---
# Replace code cell[56] with Exemple resolu
nb["cells"][56] = {
    "cell_type": "code",
    "execution_count": None,
    "metadata": {},
    "outputs": [],
    "source": [
        "# Exemple resolu : cassage de symetries pour N-Reines\n",
        "# Objectif : compter les solutions fondamentales en eliminant les 8 symetries\n",
        "# (4 rotations x 2 reflexions) du carre.\n",
        "\n",
        "def solve_nqueens_fundamental(n):\n",
        "    \"\"\"Retourne la liste des solutions fondamentales des N-Reines.\n",
        "\n",
        "    Utilise un generateur de symetries explicite : apres avoir trouve\n",
        "    une solution, on genere ses 7 symetries (rotations + reflexions)\n",
        "    et on marque celles-ci comme deja vues, afin de ne compter que\n",
        "    la premiere rencontree dans l'ordre lexicographique.\n",
        "    \"\"\"\n",
        "    model = cp_model.CpModel()\n",
        "    q = [model.new_int_var(0, n - 1, f\"q_{i}\") for i in range(n)]\n",
        "    model.add_all_different(q)\n",
        "    model.add_all_different([q[i] + i for i in range(n)])\n",
        "    model.add_all_different([q[i] - i for i in range(n)])\n",
        "\n",
        "    # Cassage partiel : forcer q[0] dans la premiere moitie\n",
        "    model.add(q[0] <= (n - 1) // 2)\n",
        "\n",
        "    class Collector(cp_model.CpSolverSolutionCallback):\n",
        "        def __init__(self, vars_):\n",
        "            super().__init__()\n",
        "            self.vars_ = vars_\n",
        "            self.solutions = []\n",
        "\n",
        "        def on_solution_callback(self):\n",
        "            self.solutions.append(tuple(self.value(v) for v in self.vars_))\n",
        "\n",
        "    solver = cp_model.CpSolver()\n",
        "    solver.parameters.enumerate_all_solutions = True\n",
        "    collector = Collector(q)\n",
        "    solver.solve(model, collector)\n",
        "\n",
        "    # Post-traitement : eliminer les symetries restantes a la main\n",
        "    def transforms(sol):\n",
        "        \"\"\"Retourne toutes les images de sol par les 8 symetries du carre.\"\"\"\n",
        "        s = list(sol)\n",
        "        results = set()\n",
        "\n",
        "        def as_tuple(cols):\n",
        "            return tuple(cols)\n",
        "\n",
        "        def reflect_h(cols):\n",
        "            return [n - 1 - r for r in cols]\n",
        "\n",
        "        def reflect_v(cols):\n",
        "            return list(reversed(cols))\n",
        "\n",
        "        def rotate_90(cols):\n",
        "            out = [0] * n\n",
        "            for c, r in enumerate(cols):\n",
        "                out[r] = n - 1 - c\n",
        "            return out\n",
        "\n",
        "        current = s[:]\n",
        "        for _ in range(4):\n",
        "            results.add(as_tuple(current))\n",
        "            results.add(as_tuple(reflect_h(current)))\n",
        "            current = rotate_90(current)\n",
        "        return results\n",
        "\n",
        "    seen = set()\n",
        "    fundamental = []\n",
        "    for sol in collector.solutions:\n",
        "        if sol in seen:\n",
        "            continue\n",
        "        fundamental.append(sol)\n",
        "        seen.update(transforms(sol))\n",
        "\n",
        "    return fundamental, len(collector.solutions)\n",
        "\n",
        "\n",
        "fundamental, total_half = solve_nqueens_fundamental(8)\n",
        "print(f\"N = 8\")\n",
        "print(f\"Solutions avec q[0] <= 3      : {total_half}\")\n",
        "print(f\"Solutions fondamentales       : {len(fundamental)}  (attendu : 12)\")\n",
        "print(f\"\\nQuelques solutions fondamentales (colonne -> ligne) :\")\n",
        "for sol in fundamental[:3]:\n",
        "    print(f\"  {sol}\")\n",
    ],
}

# Insert new Ex2b: N-Reines 12x12 with alternative symmetry breaking
new_ex2b_md = {
    "cell_type": "markdown",
    "metadata": {},
    "source": [
        "### Exercice 2 : N-Reines 12x12 et solutions fondamentales\n",
        "\n",
        "**Enonce** : Adaptez le code ci-dessus pour compter les solutions fondamentales\n",
        "du probleme des **12-Reines**.\n",
        "\n",
        "**Consignes** :\n",
        "1. Appelez `solve_nqueens_fundamental(12)` et affichez les resultats\n",
        "2. Le nombre attendu de solutions fondamentales pour N=12 est **457**\n",
        "3. Mesurez le temps d'execution avec `time.perf_counter()`\n",
        "4. (Bonus) Comparez le ratio solutions fondamentales / solutions totales pour N=8 et N=12\n",
    ],
}

new_ex2b_code = {
    "cell_type": "code",
    "execution_count": None,
    "metadata": {},
    "outputs": [],
    "source": [
        "# Exercice 2 : N-Reines 12x12\n",
        "\n",
        "# TODO: utilisez solve_nqueens_fundamental(12)\n",
        "# Indice : ajoutez import time et time.perf_counter() pour mesurer\n",
        "\n",
        "# Votre code ici\n",
    ],
}

nb["cells"].insert(57, new_ex2b_md)
nb["cells"].insert(58, new_ex2b_code)

# After insertion, Ex3 is now at [59]=md, [60]=code
# --- Ex3: Mini-TSP with Circuit (now cells 59=md, 60=code) ---
# Replace code cell[60] with Exemple resolu
nb["cells"][60] = {
    "cell_type": "code",
    "execution_count": None,
    "metadata": {},
    "outputs": [],
    "source": [
        "# Exemple resolu : Mini-TSP avec la contrainte Circuit (OR-Tools)\n",
        "\n",
        "# Matrice de distances (depot = noeud 0, clients = noeuds 1-4)\n",
        "vrp_distances = [\n",
        "    [0,  10, 15, 20, 25],  # Depot\n",
        "    [10,  0, 35, 25, 30],  # Client 1\n",
        "    [15, 35,  0, 30, 20],  # Client 2\n",
        "    [20, 25, 30,  0, 15],  # Client 3\n",
        "    [25, 30, 20, 15,  0],  # Client 4\n",
        "]\n",
        "\n",
        "n = len(vrp_distances)\n",
        "model = cp_model.CpModel()\n",
        "\n",
        "# Variables booleennes : arc[i][j] = 1 si on va de i a j\n",
        "arc = {}\n",
        "for i in range(n):\n",
        "    for j in range(n):\n",
        "        if i != j:\n",
        "            arc[(i, j)] = model.new_bool_var(f\"arc_{i}_{j}\")\n",
        "\n",
        "# Contrainte circuit\n",
        "model.add_circuit([(i, j, arc[(i, j)]) for i in range(n) for j in range(n) if i != j])\n",
        "\n",
        "# Objectif : minimiser la distance totale\n",
        "total = sum(arc[(i, j)] * vrp_distances[i][j]\n",
        "            for i in range(n) for j in range(n) if i != j)\n",
        "model.minimize(total)\n",
        "\n",
        "solver = cp_model.CpSolver()\n",
        "status = solver.solve(model)\n",
        "\n",
        "if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):\n",
        "    print(f\"Distance totale optimale : {int(solver.objective_value)}\")\n",
        "    next_node = {}\n",
        "    for i in range(n):\n",
        "        for j in range(n):\n",
        "            if i != j and solver.value(arc[(i, j)]) == 1:\n",
        "                next_node[i] = j\n",
        "    route = [0]\n",
        "    cur = 0\n",
        "    while True:\n",
        "        cur = next_node[cur]\n",
        "        route.append(cur)\n",
        "        if cur == 0:\n",
        "            break\n",
        "    labels = [\"Depot\"] + [f\"C{k}\" for k in range(1, n)]\n",
        "    print(\"Route optimale :\", \" -> \".join(labels[k] for k in route))\n",
        "\n",
        "    # Visualisation\n",
        "    angles = np.linspace(0, 2 * np.pi, n, endpoint=False)\n",
        "    xs = np.cos(angles); ys = np.sin(angles)\n",
        "    fig, ax = plt.subplots(figsize=(6, 6))\n",
        "    ax.scatter(xs, ys, s=200, c=['red'] + ['steelblue'] * (n - 1), zorder=3)\n",
        "    for k, lbl in enumerate(labels):\n",
        "        ax.annotate(lbl, (xs[k], ys[k]), textcoords='offset points',\n",
        "                    xytext=(12, 10), fontsize=11, fontweight='bold')\n",
        "    for a, b in zip(route[:-1], route[1:]):\n",
        "        ax.annotate(\"\",\n",
        "                    xy=(xs[b], ys[b]), xytext=(xs[a], ys[a]),\n",
        "                    arrowprops=dict(arrowstyle=\"->\", color='darkgreen', lw=2))\n",
        "    ax.set_aspect('equal'); ax.axis('off')\n",
        "    ax.set_title(f\"TSP - Route optimale (distance = {int(solver.objective_value)})\",\n",
        "                 fontsize=13, fontweight='bold')\n",
        "    plt.tight_layout()\n",
        "    plt.show()\n",
        "else:\n",
        "    print(f\"Aucune solution (status = {solver.status_name(status)})\")\n",
    ],
}

# Insert new Ex3b: TSP with 6 nodes and different distances
new_ex3b_md = {
    "cell_type": "markdown",
    "metadata": {},
    "source": [
        "### Exercice 3 : TSP a 6 noeuds avec contrainte Circuit\n",
        "\n",
        "**Enonce** : Modelisez et resolvez un TSP avec **1 depot et 5 clients** (6 noeuds total).\n",
        "\n",
        "Matrice de distances :\n",
        "```\n",
        "         Depot  C1  C2  C3  C4  C5\n",
        "Depot  [  0,   12, 18, 25, 30, 22]\n",
        "C1     [ 12,    0, 20, 15, 28, 35]\n",
        "C2     [ 18,   20,  0, 10, 16, 14]\n",
        "C3     [ 25,   15, 10,  0, 12, 20]\n",
        "C4     [ 30,   28, 16, 12,  0,  8]\n",
        "C5     [ 22,   35, 14, 20,  8,  0]\n",
        "```\n",
        "\n",
        "**Consignes** :\n",
        "1. Definissez la matrice de distances 6x6\n",
        "2. Creez les variables `arc[(i,j)]` et la contrainte `add_circuit`\n",
        "3. Minimisez la distance totale\n",
        "4. Affichez la route optimale et sa distance\n",
    ],
}

new_ex3b_code = {
    "cell_type": "code",
    "execution_count": None,
    "metadata": {},
    "outputs": [],
    "source": [
        "# Exercice 3 : TSP a 6 noeuds\n",
        "\n",
        "# TODO: definissez la matrice de distances 6x6\n",
        "# Indice : 6 noeuds = range(6), utiliser model.add_circuit comme ci-dessus\n",
        "\n",
        "# Votre code ici\n",
    ],
}

nb["cells"].insert(61, new_ex3b_md)
nb["cells"].insert(62, new_ex3b_code)

with open(path, "w", encoding="utf-8") as f:
    json.dump(nb, f, ensure_ascii=False, indent=1)

print(f"CSP-3 updated: {len(nb['cells'])} cells (was 57, +6 new cells)")
print("Ex1: SEND+MORE -> Exemple, new Ex1: CROSS+ROADS=DANGER")
print("Ex2: N-Reines -> Exemple, new Ex2: N-Reines 12x12")
print("Ex3: Mini-TSP -> Exemple, new Ex3: TSP 6 noeuds")
