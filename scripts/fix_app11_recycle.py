"""
Fix App-11-Picross: Recycle student solutions into Exemple resolu + new stubs.

Issue #463: Recyclage solutions etudiants CSP Applications.
"""

import json


def fix_app11():
    path = "MyIA.AI.Notebooks/Search/Applications/CSP/App-11-Picross.ipynb"
    with open(path, encoding="utf-8") as f:
        nb = json.load(f)

    # --- Ex1: resoudre un puzzle 15x15 (cell 38=code) ---
    # Replace with Exemple resolu
    nb["cells"][38] = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exemple resolu : resoudre un puzzle 15x15\n",
            "\n",
            "puzzle_ex1 = {\n",
            "    'name': 'Exercice 15x15',\n",
            "    'rows': 15, 'cols': 15,\n",
            "    'row_clues': [[3,8], [2,1,3,1], [3,3,5], [15], [1,8,2], [2,1,1,1,5], [1,1,6], [6,4], [4,5], [6,6], [13], [1,3,3], [1,1,3,1,1], [1,2,5], [7,2,1]],\n",
            "    'col_clues': [[6,1,1], [3,1,3,2,1], [3,4,1], [1,3,4,3], [1,2,4,1], [1,6,2,2], [3,1,1,2], [6,3], [1,2,1,4], [1,3,2,6], [4,6,2], [4,6,2], [12,2], [1,5,4], [2,1,1,5]],\n",
            "}\n",
            "solution_ex1, stats_ex1 = solve_cpsat(puzzle_ex1)\n",
            "display_picross(solution_ex1, puzzle_ex1['row_clues'], puzzle_ex1['col_clues'],\n",
            "                title='Exemple 15x15 - Solution')\n",
            "plt.show()\n",
        ],
    }

    # Insert new Ex1b: different 15x15 puzzle
    new_ex1b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "#### Exercice 1b : Resolvez un nouveau puzzle 15x15\n",
            "\n",
            "Resoudre le puzzle suivant en utilisant `solve_cpsat`.\n",
            "\n",
            "**Consignes** :\n",
            "1. Definissez le dictionnaire `puzzle_ex1b` avec les indices ci-dessous\n",
            "2. Appelez `solve_cpsat` et affichez le resultat avec `display_picross`\n",
            "3. Verifiez le nombre de solutions avec `check_uniqueness`\n",
            "\n",
            "```\n",
            "Row clues: [5,5], [1,1,1,1,1], [1,1,1,1,1], [5,5], [5,5],\n",
            "           [1,1,1,1,1], [1,1,1,1,1], [5,5], [1,1,1,1,1], [1,1,1,1,1],\n",
            "           [5,5], [5,5], [1,1,1,1,1], [1,1,1,1,1], [5,5]\n",
            "Col clues: [5,5], [1,1,1,1,1], [1,1,1,1,1], [5,5], [5,5],\n",
            "           [1,1,1,1,1], [1,1,1,1,1], [5,5], [1,1,1,1,1], [1,1,1,1,1],\n",
            "           [5,5], [5,5], [1,1,1,1,1], [1,1,1,1,1], [5,5]\n",
            "```\n",
        ],
    }

    new_ex1b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 1b : Resolvez un nouveau puzzle 15x15\n",
            "\n",
            "# TODO: definissez puzzle_ex1b avec les row_clues et col_clues donnes ci-dessus\n",
            "# TODO: appelez solve_cpsat et display_picross\n",
            "# Indice : reprenez la structure de l'exemple ci-dessus\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(39, new_ex1b_md)
    nb["cells"].insert(40, new_ex1b_code)

    # After insertion, Ex2 shifted: now at 42=code
    # --- Ex2: generer un puzzle (now cell 42=code) ---
    nb["cells"][42] = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exemple resolu : generer un puzzle a partir d'initiales\n",
            "\n",
            "my_initials = np.array([\n",
            "    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],\n",
            "    [0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0],\n",
            "    [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],\n",
            "    [0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0],\n",
            "    [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],\n",
            "    [0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0],\n",
            "    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],\n",
            "], dtype=int)\n",
            "my_puzzle = create_puzzle_from_image(my_initials, 'Mes initiales')\n",
            "n_sol = check_uniqueness(my_puzzle)\n",
            "print(f'Nombre de solutions : {n_sol}')\n",
            "solution, stats = solve_cpsat(my_puzzle)\n",
            "display_picross(solution, my_puzzle['row_clues'], my_puzzle['col_clues'])\n",
            "plt.show()\n",
        ],
    }

    # Insert new Ex2b: create own initials puzzle
    new_ex2b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "#### Exercice 2b : Creez un puzzle avec vos propres initiales\n",
            "\n",
            "Concevez une image binaire representant **vos propres initiales** (ou un dessin simple)\n",
            "et generez le puzzle Picross correspondant.\n",
            "\n",
            "**Consignes** :\n",
            "1. Creez un tableau `np.array` binaire (0/1) d'au moins 8 lignes x 10 colonnes\n",
            "2. Utilisez `create_puzzle_from_image` pour generer le puzzle\n",
            "3. Verifiez l'unicite avec `check_uniqueness`\n",
            "4. Si non unique, ajoutez des cases pour desambiguiser\n",
            "5. Affichez le puzzle et sa solution\n",
        ],
    }

    new_ex2b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 2b : Creez un puzzle avec vos propres initiales\n",
            "\n",
            "# TODO: creez votre image binaire avec np.array\n",
            "# TODO: utilisez create_puzzle_from_image, check_uniqueness, solve_cpsat\n",
            "# Indice : commencez par un dessin simple (coeur, smiley, lettre)\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(43, new_ex2b_md)
    nb["cells"].insert(44, new_ex2b_code)

    # Ex3 is already a stub (cell ~46 after insertions) — leave as-is

    with open(path, "w", encoding="utf-8") as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)

    print(f"App-11 updated: {len(nb['cells'])} cells (+4 new cells)")


if __name__ == "__main__":
    fix_app11()
