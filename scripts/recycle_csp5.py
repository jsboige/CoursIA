"""
Recycle CSP-5-Optimization exercises (Issue #463).

Converts 4 student solutions into labeled "Exemple resolu" cells
and creates new exercise stubs with variant data.
"""

import json


def main():
    path = "MyIA.AI.Notebooks/Search/Part2-CSP/CSP-5-Optimization.ipynb"
    with open(path, encoding="utf-8") as f:
        nb = json.load(f)

    # --- Exercise layout (45 cells) ---
    # [35] md  : "## 7. Exercices" header
    # [36] code: Ex1 Multi-Knapsack solution
    # [37] md  : Ex2 Bin Packing conflicts enonce
    # [38] code: Ex2 Bin Packing conflicts solution
    # [39] md  : Ex3 Portfolio risk enonce
    # [40] code: Ex3 Portfolio risk solution
    # [41] md  : Ex4 Cutting Stock reuse enonce
    # [42] code: Ex4 Cutting Stock reuse solution
    # [43] md  : References
    # [44] md  : Conclusion

    # ================================================================
    # Ex1: Multi-Knapsack → Exemple resolu (cell 36)
    # ================================================================
    old_src = nb["cells"][36]["source"]
    # Prepend "Exemple resolu" label
    if old_src[0].startswith("# Exercice 1"):
        old_src[0] = old_src[0].replace("# Exercice 1", "# Exemple resolu : Multi-Knapsack")
    else:
        old_src.insert(0, "# Exemple resolu : Multi-Knapsack (plusieurs sacs)\n")
    nb["cells"][36]["source"] = old_src
    nb["cells"][36]["outputs"] = []
    nb["cells"][36]["execution_count"] = None

    # Insert Ex1b: Multi-Knapsack with 12 items and 3 bags
    ex1b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 1b : Multi-Knapsack avec 3 sacs\n",
            "\n",
            "**Enonce** : Resolvez un probleme de Multi-Knapsack avec **12 objets** et **3 sacs**\n",
            "de capacites [12, 18, 10].\n",
            "\n",
            "Donnees :\n",
            "- Poids  : `[3, 6, 2, 4, 8, 5, 7, 1, 9, 3, 4, 6]`\n",
            "- Valeurs: `[5, 9, 3, 7, 12, 8, 10, 2, 14, 4, 6, 11]`\n",
            "- Capacites des 3 sacs : `[12, 18, 10]`\n",
            "\n",
            "**Consignes** :\n",
            "1. Utilisez `solve_multi_knapsack` definie dans l'exemple ci-dessus\n",
            "2. Affichez le contenu de chaque sac, sa charge et sa valeur\n",
            "3. Verifiez qu'aucun objet n'est place dans plus d'un sac\n",
        ],
    }

    ex1b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 1b : Multi-Knapsack avec 3 sacs\n",
            "\n",
            "# TODO: definissez les nouvelles donnees (12 objets, 3 sacs)\n",
            "new_weights = [3, 6, 2, 4, 8, 5, 7, 1, 9, 3, 4, 6]\n",
            "new_values  = [5, 9, 3, 7, 12, 8, 10, 2, 14, 4, 6, 11]\n",
            "new_caps    = [12, 18, 10]\n",
            "\n",
            "# TODO: appelez solve_multi_knapsack et affichez les resultats\n",
            "# Indice : utilisez la meme fonction que dans l'exemple\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(37, ex1b_md)
    nb["cells"].insert(38, ex1b_code)

    # ================================================================
    # Ex2: Bin Packing with conflicts → Exemple resolu (now cell 40)
    # ================================================================
    old_src2 = nb["cells"][40]["source"]
    if old_src2[0].startswith("# Exercice 2"):
        old_src2[0] = old_src2[0].replace("# Exercice 2", "# Exemple resolu : Bin Packing avec conflits")
    else:
        old_src2.insert(0, "# Exemple resolu : Bin Packing avec conflits\n")
    nb["cells"][40]["source"] = old_src2
    nb["cells"][40]["outputs"] = []
    nb["cells"][40]["execution_count"] = None

    # Insert Ex2b: Bin Packing with different conflicts
    ex2b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 2b : Bin Packing avec conflits etendus\n",
            "\n",
            "**Enonce** : Resolvez un Bin Packing avec **12 objets** et des conflits plus nombreux.\n",
            "\n",
            "Donnees :\n",
            "- Tailles : `[5, 3, 7, 2, 8, 4, 6, 1, 9, 3, 5, 2]`\n",
            "- Capacite des bins : 15\n",
            "- Conflits : `[(0, 3), (1, 6), (2, 5), (4, 8), (7, 10), (0, 9)]`\n",
            "\n",
            "**Consignes** :\n",
            "1. Utilisez `solve_bin_packing_conflicts` definie dans l'exemple ci-dessus\n",
            "2. Comparez le nombre de bins avec et sans conflits\n",
            "3. Verifiez qu'aucune paire en conflit ne partage le meme bin\n",
        ],
    }

    ex2b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 2b : Bin Packing avec conflits etendus\n",
            "\n",
            "# TODO: definissez les nouvelles donnees\n",
            "new_items    = [5, 3, 7, 2, 8, 4, 6, 1, 9, 3, 5, 2]\n",
            "new_capacity = 15\n",
            "new_conflicts = [(0, 3), (1, 6), (2, 5), (4, 8), (7, 10), (0, 9)]\n",
            "\n",
            "# TODO: resolvez avec solve_bin_packing_conflicts\n",
            "# TODO: comparez avec solve_bin_packing_cp (sans conflits)\n",
            "# Indice : les conflits forcent souvent un bin supplementaire\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(41, ex2b_md)
    nb["cells"].insert(42, ex2b_code)

    # ================================================================
    # Ex3: Portfolio with risk → Exemple resolu (now cell 44)
    # ================================================================
    old_src3 = nb["cells"][44]["source"]
    if old_src3[0].startswith("# Exercice 3"):
        old_src3[0] = old_src3[0].replace("# Exercice 3", "# Exemple resolu : Portfolio avec risque")
    else:
        old_src3.insert(0, "# Exemple resolu : Portfolio avec contrainte de risque\n")
    nb["cells"][44]["source"] = old_src3
    nb["cells"][44]["outputs"] = []
    nb["cells"][44]["execution_count"] = None

    # Insert Ex3b: Portfolio with tighter risk constraint
    ex3b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 3b : Portefeuille conservative\n",
            "\n",
            "**Enonce** : Construisez un portefeuille **conservatif** avec une contrainte de\n",
            "variance plus stricte (`max_variance_per_euro = 3.0` au lieu de 10.0).\n",
            "\n",
            "Donnees :\n",
            "```python\n",
            "assets = ['AAPL', 'GOOGL', 'MSFT', 'AMZN', 'TSLA', 'NVDA']\n",
            "prices = [\n",
            "    [150, 155, 160, 158, 165],   # AAPL\n",
            "    [2800, 2850, 2900, 2880, 2950],  # GOOGL\n",
            "    [300, 310, 315, 320, 325],   # MSFT\n",
            "    [3200, 3150, 3300, 3400, 3350],  # AMZN\n",
            "    [900, 950, 880, 920, 1000],   # TSLA\n",
            "    [450, 480, 510, 490, 520],    # NVDA\n",
            "]\n",
            "budget = 60000\n",
            "```\n",
            "\n",
            "**Consignes** :\n",
            "1. Utilisez `solve_portfolio_with_risk` definie dans l'exemple ci-dessus\n",
            "2. Selectionnez entre 2 et 4 actifs avec une variance max par euro de 3.0\n",
            "3. Comparez le rendement avec le portefeuille moins contraint de l'exemple\n",
        ],
    }

    ex3b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 3b : Portefeuille conservative\n",
            "\n",
            "# TODO: definissez les 6 actifs avec leurs historiques de prix\n",
            "assets_conservative = ['AAPL', 'GOOGL', 'MSFT', 'AMZN', 'TSLA', 'NVDA']\n",
            "prices_conservative = [\n",
            "    [150, 155, 160, 158, 165],\n",
            "    [2800, 2850, 2900, 2880, 2950],\n",
            "    [300, 310, 315, 320, 325],\n",
            "    [3200, 3150, 3300, 3400, 3350],\n",
            "    [900, 950, 880, 920, 1000],\n",
            "    [450, 480, 510, 490, 520],\n",
            "]\n",
            "\n",
            "# TODO: appelez solve_portfolio_with_risk avec max_variance_per_euro=3.0\n",
            "# Indice : avec 6 actifs au lieu de 5, vous avez plus de choix\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(45, ex3b_md)
    nb["cells"].insert(46, ex3b_code)

    # ================================================================
    # Ex4: Cutting Stock with reuse → Exemple resolu (now cell 48)
    # ================================================================
    old_src4 = nb["cells"][48]["source"]
    if old_src4[0].startswith("# Exercice 4"):
        old_src4[0] = old_src4[0].replace("# Exercice 4", "# Exemple resolu : Cutting Stock avec chutes reutilisables")
    else:
        old_src4.insert(0, "# Exemple resolu : Cutting Stock avec chutes reutilisables\n")
    nb["cells"][48]["source"] = old_src4
    nb["cells"][48]["outputs"] = []
    nb["cells"][48]["execution_count"] = None

    # Insert Ex4b: Cutting Stock with different demands and threshold
    ex4b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 4b : Cutting Stock avec seuil de reutilisation eleve\n",
            "\n",
            "**Enonce** : Resolvez un Cutting Stock avec des demandes plus elevees\n",
            "et un seuil de reutilisation plus strict (30 cm au lieu de 20 cm).\n",
            "\n",
            "Donnees :\n",
            "- Longueurs de pieces : `[15, 22, 35, 40]` cm\n",
            "- Demandes : `[8, 6, 5, 3]`\n",
            "- Longueur des barres : 120 cm\n",
            "- Seuil de reutilisation : 30 cm\n",
            "\n",
            "**Consignes** :\n",
            "1. Utilisez `solve_cutting_stock_reuse` definie dans l'exemple ci-dessus\n",
            "2. Comparez avec `solve_cutting_stock_cp` (sans reutilisation des chutes)\n",
            "3. Affichez le nombre de barres neuves et le nombre de chutes reutilisees\n",
        ],
    }

    ex4b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 4b : Cutting Stock avec seuil de reutilisation eleve\n",
            "\n",
            "# TODO: definissez les nouvelles donnees\n",
            "new_piece_lengths = [15, 22, 35, 40]\n",
            "new_demands       = [8, 6, 5, 3]\n",
            "new_stock_length  = 120\n",
            "new_reuse_thresh  = 30\n",
            "\n",
            "# TODO: resolvez avec solve_cutting_stock_reuse\n",
            "# TODO: comparez avec solve_cutting_stock_cp (sans chutes)\n",
            "# Indice : un seuil plus eleve signifie moins de chutes reutilisables\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(49, ex4b_md)
    nb["cells"].insert(50, ex4b_code)

    # ================================================================
    # Write back
    # ================================================================
    with open(path, "w", encoding="utf-8") as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)

    print(f"CSP-5 updated: {len(nb['cells'])} cells (was 45, +8 new cells)")


if __name__ == "__main__":
    main()
