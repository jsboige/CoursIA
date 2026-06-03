"""
Fix Issue #420: CSP-1/CSP-2 stubs ambigus ou deconnectes.

Converts student solutions to labeled "Exemple" cells and creates
new exercise stubs with proper TODO markers.
"""

import json
import sys


def fix_csp1():
    path = "MyIA.AI.Notebooks/Search/Part2-CSP/CSP-1-Fundamentals.ipynb"
    with open(path, encoding="utf-8") as f:
        nb = json.load(f)

    # --- Ex3: SEND+MORE=MONEY (cells 64=md, 65=code) ---
    # Replace code cell 65 with Exemple label
    nb["cells"][65] = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exemple resolu : SEND + MORE = MONEY\n",
            "\n",
            "from constraint import Problem, AllDifferentConstraint\n",
            "\n",
            "money = Problem()\n",
            'letters = ["S", "E", "N", "D", "M", "O", "R", "Y"]\n',
            "money.addVariables(letters, range(10))\n",
            "money.addConstraint(AllDifferentConstraint(), letters)\n",
            'money.addConstraint(lambda s: s != 0, ["S"])\n',
            'money.addConstraint(lambda m: m != 0, ["M"])\n',
            "money.addConstraint(\n",
            "    lambda S, E, N, D, M, O, R, Y:\n",
            "        1000 * S + 100 * E + 10 * N + D\n",
            "        + 1000 * M + 100 * O + 10 * R + E\n",
            "        == 10000 * M + 1000 * O + 100 * N + 10 * E + Y,\n",
            "    letters\n",
            ")\n",
            "\n",
            "sol = money.getSolution()\n",
            'print(f"Solution : {sol}")\n',
            "if sol:\n",
            '    send = 1000 * sol["S"] + 100 * sol["E"] + 10 * sol["N"] + sol["D"]\n',
            '    more = 1000 * sol["M"] + 100 * sol["O"] + 10 * sol["R"] + sol["E"]\n',
            '    total = 10000 * sol["M"] + 1000 * sol["O"] + 100 * sol["N"] + 10 * sol["E"] + sol["Y"]\n',
            '    print(f"SEND = {send},  MORE = {more},  MONEY = {total}")\n',
        ],
    }

    # Insert new Ex3b: DONALD + GERALD = ROBERT
    new_ex3b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 3b : Cryptarithme DONALD + GERALD = ROBERT\n",
            "\n",
            "**Enonce** : Resolvez le cryptarithme classique **DONALD + GERALD = ROBERT**.\n",
            "\n",
            "```\n",
            "    D O N A L D\n",
            "  + G E R A L D\n",
            "  -------------\n",
            "  R O B E R T\n",
            "```\n",
            "\n",
            "Chaque lettre represente un chiffre distinct (0-9). D et G ne peuvent pas valoir 0.\n",
            "\n",
            "**Consignes** :\n",
            "1. Utilisez `python-constraint` comme dans l'exemple ci-dessus\n",
            "2. Posez la contrainte arithmetique : $100000D + 10000O + 1000N + 100A + 10L + D$\n",
            "   $+ 100000G + 10000E + 1000R + 100A + 10L + D = 100000R + 10000O + 1000B + 100E + 10R + T$\n",
            "3. Verifiez que votre solution est unique (utilisez `getSolutions()`)\n",
        ],
    }

    new_ex3b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 3b : DONALD + GERALD = ROBERT\n",
            "\n",
            "# TODO: importez python-constraint et modelisez le probleme\n",
            "# Indice : 10 lettres distinctes = D, O, N, A, L, G, E, R, B, T\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(66, new_ex3b_md)
    nb["cells"].insert(67, new_ex3b_code)

    # --- Ex4: Sudoku 4x4 (now cells 68=md, 69=code) ---
    # Replace code cell 69 with Exemple
    nb["cells"][69] = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exemple resolu : Sudoku 4x4 avec visualisation\n",
            "\n",
            'def make_sudoku_4x4_csp(initial_grid):\n',
            '    """Cree un CSP pour un Sudoku 4x4.\n',
            "\n",
            "    Args:\n",
            "        initial_grid: liste 2D 4x4 (0 = case vide)\n",
            '    """\n',
            '    variables = [f"{i}{j}" for i in range(4) for j in range(4)]\n',
            "    domains = {}\n",
            "    neighbors = {var: [] for var in variables}\n",
            "\n",
            "    for i in range(4):\n",
            "        for j in range(4):\n",
            '            var = f"{i}{j}"\n',
            "            if initial_grid[i][j] == 0:\n",
            "                domains[var] = [1, 2, 3, 4]\n",
            "            else:\n",
            "                domains[var] = [initial_grid[i][j]]\n",
            "\n",
            "    for i1 in range(4):\n",
            "        for j1 in range(4):\n",
            '            var1 = f"{i1}{j1}"\n',
            "            related = set()\n",
            "            for j2 in range(4):\n",
            "                if j2 != j1:\n",
            '                    related.add(f"{i1}{j2}")\n',
            "            for i2 in range(4):\n",
            "                if i2 != i1:\n",
            '                    related.add(f"{i2}{j1}")\n',
            "            block_i, block_j = (i1 // 2) * 2, (j1 // 2) * 2\n",
            "            for di in range(2):\n",
            "                for dj in range(2):\n",
            "                    nb = (block_i + di, block_j + dj)\n",
            "                    if nb != (i1, j1):\n",
            '                        related.add(f"{nb[0]}{nb[1]}")\n',
            "            neighbors[var1] = sorted(related)\n",
            "\n",
            "    def sudoku_constraint(var1, val1, var2, val2):\n",
            "        i1, j1 = int(var1[0]), int(var1[1])\n",
            "        i2, j2 = int(var2[0]), int(var2[1])\n",
            "        same_row = i1 == i2\n",
            "        same_col = j1 == j2\n",
            "        same_block = (i1 // 2, j1 // 2) == (i2 // 2, j2 // 2)\n",
            "        if same_row or same_col or same_block:\n",
            "            return val1 != val2\n",
            "        return True\n",
            "\n",
            "    return CSP(variables, domains, neighbors, sudoku_constraint)\n",
            "\n",
            "\n",
            "initial = [\n",
            "    [1, 0, 0, 2],\n",
            "    [0, 0, 0, 0],\n",
            "    [0, 0, 0, 0],\n",
            "    [3, 0, 0, 4],\n",
            "]\n",
            "\n",
            "sudoku_csp = make_sudoku_4x4_csp(initial)\n",
            "solution, viz = backtracking_with_viz(sudoku_csp)\n",
            'print(f"Solution : {solution}")\n',
            'viz.draw(max_depth=5, title="Arbre de Backtracking - Sudoku 4x4")\n',
        ],
    }

    # Insert new Ex4b: Different grid
    new_ex4b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 4b : Nouvelle grille Sudoku 4x4\n",
            "\n",
            "**Enonce** : Resolvez cette nouvelle grille avec `backtracking_with_viz`.\n",
            "\n",
            "Grille initiale :\n",
            "```\n",
            "0 2 | 0 0\n",
            "0 0 | 0 3\n",
            "---------\n",
            "4 0 | 0 0\n",
            "0 0 | 1 0\n",
            "```\n",
            "\n",
            "**Consignes** :\n",
            "1. Utilisez la fonction `make_sudoku_4x4_csp` definie ci-dessus\n",
            "2. Appelez `backtracking_with_viz` pour obtenir la solution et la visualisation\n",
            "3. Affichez la solution et l'arbre de recherche\n",
        ],
    }

    new_ex4b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 4b : Nouvelle grille Sudoku 4x4\n",
            "\n",
            "# TODO: definissez la grille initiale ci-dessous\n",
            "new_grid = [\n",
            "    [0, 2, 0, 0],\n",
            "    [0, 0, 0, 3],\n",
            "    [4, 0, 0, 0],\n",
            "    [0, 0, 1, 0],\n",
            "]\n",
            "\n",
            "# TODO: creez le CSP et resolvez avec backtracking_with_viz\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(70, new_ex4b_md)
    nb["cells"].insert(71, new_ex4b_code)

    with open(path, "w", encoding="utf-8") as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)

    print(f"CSP-1 updated: {len(nb['cells'])} cells (was 71, +4 new cells)")


def fix_csp2():
    path = "MyIA.AI.Notebooks/Search/Part2-CSP/CSP-2-Consistency.ipynb"
    with open(path, encoding="utf-8") as f:
        nb = json.load(f)

    # --- Ex1: AC-3 a la main (cells 55=md, 56=code) ---
    # Replace code cell 56 with Exemple (code verification) + new exercise
    nb["cells"][56] = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exemple : Verification AC-3 par le code\n",
            "# Ce code montre le resultat d'AC-3 sur le CSP X<Y, Y!=Z.\n",
            "# Comparez avec votre trace manuelle.\n",
            "\n",
            "ex1_vars = ['X', 'Y', 'Z']\n",
            "ex1_domains = {'X': [1, 2, 3], 'Y': [1, 2, 3], 'Z': [1, 2, 3]}\n",
            "ex1_neighbors = {'X': ['Y'], 'Y': ['X', 'Z'], 'Z': ['Y']}\n",
            "\n",
            "def ex1_constraint(var1, val1, var2, val2):\n",
            '    """Contraintes : X < Y et Y != Z."""\n',
            "    pair = tuple(sorted([var1, var2]))\n",
            "    if pair == ('X', 'Y'):\n",
            "        return val1 < val2 if var1 == 'X' else val2 < val1\n",
            "    elif pair == ('Y', 'Z'):\n",
            "        return val1 != val2\n",
            "    return True\n",
            "\n",
            "csp_ex1 = CSP(ex1_vars, ex1_domains, ex1_neighbors, ex1_constraint)\n",
            "\n",
            'print("Domaines initiaux :")\n',
            "for v in ex1_vars:\n",
            '    print(f"  {v} : {csp_ex1.domains[v]}")\n',
            "\n",
            "domains_ex1 = csp_ex1.copy_domains()\n",
            "result_ex1 = ac3(csp_ex1, domains_ex1)\n",
            "\n",
            'print(f"\\nAC-3 : {\'Consistant\' if result_ex1 else \'Echec\'}")\n',
            'print("\\nDomaines finaux :")\n',
            "for v in ex1_vars:\n",
            '    print(f"  {v} : {domains_ex1[v]}")\n',
        ],
    }

    # Insert new Ex1b: Manual trace exercise
    new_ex1b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 1b : Votre trace manuelle d'AC-3\n",
            "\n",
            "En vous basant sur le resultat du code ci-dessus, remplissez le tableau\n",
            "suivant pour chaque arc traite par AC-3 :\n",
            "\n",
            "| Arc traite | Valeurs retirees | Arcs ajoutes a la file |\n",
            "|------------|-----------------|----------------------|\n",
            "| _(X,Y)_   | ...             | ...                  |\n",
            "| _(Y,X)_   | ...             | ...                  |\n",
            "| ...        | ...             | ...                  |\n",
            "\n",
            "**Puis** : verifiez votre trace en executant `ac3(csp_ex1, domains_ex1, verbose=True)`\n",
            "dans la cellule ci-dessous.\n",
        ],
    }

    new_ex1b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 1b : Verifiez votre trace manuelle\n",
            "\n",
            "# TODO: executez AC-3 avec verbose=True et comparez avec votre trace\n",
            "# Indice : utilisez csp_ex1 et domains_ex1 definis ci-dessus\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(57, new_ex1b_md)
    nb["cells"].insert(58, new_ex1b_code)

    with open(path, "w", encoding="utf-8") as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)

    print(f"CSP-2 updated: {len(nb['cells'])} cells (was 62, +2 new cells)")


if __name__ == "__main__":
    fix_csp1()
    fix_csp2()
    print("Done.")
