"""
Fix App-6-Minesweeper: recycle student solutions into Exemple cells + new stubs.

Part of Issue #463: recyclage App-1..App-11.
"""

import json


def fix_app6():
    path = "MyIA.AI.Notebooks/Search/Applications/CSP/App-6-Minesweeper.ipynb"
    with open(path, encoding="utf-8") as f:
        nb = json.load(f)

    # --- Ex1: EnhancedCSPSolver with global constraint (cell 42) ---
    nb["cells"][42] = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exemple resolu : solveur CSP avec contrainte globale\n",
            "\n",
            "class EnhancedCSPSolver(CSPSolver):\n",
            "    def build_csp(self):\n",
            "        problem, frontier = super().build_csp()\n",
            "        if problem is None:\n",
            "            return None, frontier\n",
            "\n",
            "        # Contrainte globale : si toutes les cases inconnues sont\n",
            "        # dans la frontiere, on impose la somme exacte des mines.\n",
            "        all_unknown = [\n",
            "            (r, c)\n",
            "            for r in range(self.board.rows)\n",
            "            for c in range(self.board.cols)\n",
            "            if (r, c) not in self.board.revealed\n",
            "            and (r, c) not in self.board.flagged\n",
            "        ]\n",
            "\n",
            "        if len(all_unknown) == len(frontier) and len(frontier) > 0:\n",
            "            problem.addConstraint(\n",
            "                ExactSumConstraint(self.board.remaining_mines()),\n",
            "                list(frontier),\n",
            "            )\n",
            "\n",
            "        return problem, frontier\n",
            "\n",
            "\n",
            "# Benchmark pour comparer\n",
            "N_GAMES_EX1 = 50\n",
            "wins_std = 0\n",
            "wins_enhanced = 0\n",
            "\n",
            "print(f\"Lancement du benchmark sur {N_GAMES_EX1} parties...\")\n",
            "\n",
            "for i in range(N_GAMES_EX1):\n",
            "    seed = 4000 + i\n",
            "\n",
            "    # Test Standard\n",
            "    random.seed(seed)\n",
            "    np.random.seed(seed)\n",
            "    b1 = MinesweeperBoard(8, 8, 10, safe_cell=(4, 4))\n",
            "    b1.reveal(4, 4)\n",
            "    s1 = ProbabilisticSolver(b1)\n",
            "    if s1.play_game():\n",
            "        wins_std += 1\n",
            "\n",
            "    # Test Enhanced\n",
            "    random.seed(seed)\n",
            "    np.random.seed(seed)\n",
            "    b2 = MinesweeperBoard(8, 8, 10, safe_cell=(4, 4))\n",
            "    b2.reveal(4, 4)\n",
            "    original_csp = CSPSolver\n",
            "    import __main__\n",
            "    __main__.CSPSolver = EnhancedCSPSolver\n",
            "    s2 = ProbabilisticSolver(b2)\n",
            "    if s2.play_game():\n",
            "        wins_enhanced += 1\n",
            "    __main__.CSPSolver = original_csp\n",
            "\n",
            'print("\\nResultats :")\n',
            'print(f"Taux de victoire (Standard) : {wins_std/N_GAMES_EX1:.1%}")\n',
            'print(f"Taux de victoire (Enhanced) : {wins_enhanced/N_GAMES_EX1:.1%}")\n',
        ],
    }

    # Insert new Ex1b: alternate constraint strategy
    new_ex1b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 1b : comptage total des mines\n",
            "\n",
            "**Enonce** : au lieu d'ajouter une contrainte `ExactSumConstraint` quand toute\n",
            "la frontiere est couverte, ajoutez systematiquement une contrainte sur le\n",
            "**nombre total de mines** parmi toutes les cellules inconnues (meme celles\n",
            "hors frontiere), des le premier appel a `build_csp`.\n",
            "\n",
            "**Consignes** :\n",
            "1. Creez une classe `GlobalMineCountSolver(CSPSolver)` qui surcharge `build_csp`\n",
            "2. Ajoutez une contrainte `ExactSumConstraint` sur toutes les variables inconnues\n",
            "3. Lancez le meme benchmark que l'exemple et comparez les taux de victoire\n",
        ],
    }

    new_ex1b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 1b : contrainte globale systematique\n",
            "\n",
            "# TODO: creez la classe GlobalMineCountSolver et lancez le benchmark\n",
            "# Indice : ajoutez ExactSumConstraint sur toutes les variables inconnues,\n",
            "# pas seulement celles de la frontiere\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(43, new_ex1b_md)
    nb["cells"].insert(44, new_ex1b_code)

    # After insertion, indices shifted by +2:
    # Old cell 43 (md Ex2) -> 45
    # Old cell 44 (code Ex2) -> 46
    # Old cell 45 (md Ex3) -> 47
    # Old cell 46 (code Ex3) -> 48

    # --- Ex2: LazyMinesweeperBoard (now cell 46) ---
    nb["cells"][46] = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exemple resolu : generation differee des mines\n",
            "\n",
            "class LazyMinesweeperBoard(MinesweeperBoard):\n",
            "    def __init__(self, rows=8, cols=8, n_mines=10):\n",
            "        self.rows = rows\n",
            "        self.cols = cols\n",
            "        self.n_mines = n_mines\n",
            "        self.revealed = set()\n",
            "        self.flagged = set()\n",
            "        self.game_over = False\n",
            "        self.won = False\n",
            "        self.mines_placed = False\n",
            "        self.mines = set()\n",
            "        self.numbers = np.zeros((rows, cols), dtype=int)\n",
            "\n",
            "    def _place_mines(self, safe_cell):\n",
            "        all_cells = [(r, c) for r in range(self.rows)\n",
            "                     for c in range(self.cols)]\n",
            "        excluded = {safe_cell}\n",
            "        excluded.update(self.get_neighbors(*safe_cell))\n",
            "\n",
            "        candidates = [cell for cell in all_cells\n",
            "                      if cell not in excluded]\n",
            "        self.mines = set(\n",
            "            random.sample(candidates, min(self.n_mines, len(candidates)))\n",
            "        )\n",
            "\n",
            "        self.numbers = np.zeros((self.rows, self.cols), dtype=int)\n",
            "        for r in range(self.rows):\n",
            "            for c in range(self.cols):\n",
            "                if (r, c) not in self.mines:\n",
            "                    self.numbers[r, c] = sum(\n",
            "                        1 for nr, nc in self.get_neighbors(r, c)\n",
            "                        if (nr, nc) in self.mines\n",
            "                    )\n",
            "        self.mines_placed = True\n",
            "\n",
            "    def reveal(self, r, c):\n",
            "        if not self.mines_placed:\n",
            "            self._place_mines((r, c))\n",
            "        return super().reveal(r, c)\n",
            "\n",
            "\n",
            "# Test de la generation differee\n",
            "random.seed(42)\n",
            "board_lazy = LazyMinesweeperBoard(8, 8, 10)\n",
            'print(\"Avant reveal :\", len(board_lazy.mines), \"mines\")\n',
            "board_lazy.reveal(0, 0)\n",
            'print(\"Apres reveal :\", len(board_lazy.mines), \"mines\")\n',
            'draw_board(board_lazy, title="Generation differee (clic en 0,0)")\n',
            "plt.show()\n",
        ],
    }

    # Insert new Ex2b: safe zone variant
    new_ex2b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 2b : zone de securite configurable\n",
            "\n",
            "**Enonce** : modifiez `MinesweeperBoard` pour que la zone de securite lors du\n",
            "premier clic soit configurable : au lieu d'exclure les 8 voisins, l'utilisateur\n",
            "choisit le rayon d'exclusion.\n",
            "\n",
            "**Consignes** :\n",
            "1. Creez une classe `ConfigurableSafeBoard(MinesweeperBoard)` avec un parametre\n",
            "   `safe_radius` (par defaut 1 = voisins directs, 0 = seule la case cliquee)\n",
            "2. Generez les mines apres le premier clic, en excluant toutes les cases dans\n",
            "   le rayon donne\n",
            "3. Testez avec `safe_radius=2` sur une grille 10x10, 15 mines, premier clic en (5,5)\n",
        ],
    }

    new_ex2b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 2b : zone de securite configurable\n",
            "\n",
            "# TODO: creez la classe ConfigurableSafeBoard avec safe_radius\n",
            "# Indice : get_neighbors fonctionne en rayon 1,\n",
            "# pour rayon > 1 il faut iterer les offsets (dr, dc) avec max(|dr|,|dc|) <= radius\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(47, new_ex2b_md)
    nb["cells"].insert(48, new_ex2b_code)

    # After insertion, indices shifted by +4 total from original:
    # Old cell 45 (md Ex3) -> 49
    # Old cell 46 (code Ex3) -> 50

    # --- Ex3: 16x16 benchmark (now cell 50) ---
    nb["cells"][50] = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exemple resolu : benchmark 16x16\n",
            "\n",
            "N_GAMES_16 = 30\n",
            "wins_16 = 0\n",
            "total_time_16 = 0\n",
            "total_guesses_16 = 0\n",
            "\n",
            "for game_id in range(N_GAMES_16):\n",
            "    random.seed(3000 + game_id)\n",
            "    np.random.seed(3000 + game_id)\n",
            "    board_16 = MinesweeperBoard(16, 16, 40, safe_cell=(8, 8))\n",
            "    board_16.reveal(8, 8)\n",
            "    solver_16 = ProbabilisticSolver(board_16)\n",
            "    start = time.time()\n",
            "    won = solver_16.play_game()\n",
            "    total_time_16 += time.time() - start\n",
            "    if won:\n",
            "        wins_16 += 1\n",
            "    total_guesses_16 += solver_16.decisions['guess']\n",
            "\n",
            'print("16x16 (40 mines) :")\n',
            'print(f"  Victoires : {wins_16}/{N_GAMES_16}")\n',
            'print(f"  Temps moyen : {total_time_16/N_GAMES_16*1000:.0f} ms")\n',
            'print(f"  Devinettes moyennes : {total_guesses_16/N_GAMES_16:.1f}")\n',
        ],
    }

    # Insert new Ex3b: expert difficulty 30x16
    new_ex3b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 3b : difficulte experte (30x16, 99 mines)\n",
            "\n",
            "**Enonce** : testez le solveur sur la difficulte \"experte\" du Demineur\n",
            "(grille 30x16 avec 99 mines). Mesurez les memes indicateurs.\n",
            "\n",
            "**Consignes** :\n",
            "1. Lancez 20 parties sur grille 30x16, 99 mines, premier clic au centre\n",
            "2. Affichez le taux de victoire, le temps moyen et les devinettes moyennes\n",
            "3. Comparez avec les resultats 8x8 et 16x16 obtenus plus haut\n",
        ],
    }

    new_ex3b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 3b : difficulte experte\n",
            "\n",
            "# TODO: lancez le benchmark 30x16 avec 99 mines\n",
            "# Indice : utilisez le meme pattern que l'exemple 16x16\n",
            "# avec MinesweeperBoard(30, 16, 99, safe_cell=(15, 8))\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(51, new_ex3b_md)
    nb["cells"].insert(52, new_ex3b_code)

    with open(path, "w", encoding="utf-8") as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)

    print(f"App-6 updated: {len(nb['cells'])} cells (was 49, +6 new cells)")


if __name__ == "__main__":
    fix_app6()
    print("Done.")
