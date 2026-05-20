"""
Fix App-3-NurseScheduling: Recycle student solutions into Exemple resolu + new stubs.

Issue #463: Recyclage solutions etudiants CSP Applications.
"""

import json


def fix_app3():
    path = "MyIA.AI.Notebooks/Search/Applications/CSP/App-3-NurseScheduling.ipynb"
    with open(path, encoding="utf-8") as f:
        nb = json.load(f)

    # --- Ex1: pas plus de 3 jours consecutifs (cell 46=code) ---
    # Replace with Exemple resolu
    nb["cells"][46] = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exemple resolu : pas plus de 3 jours consecutifs\n",
            "\n",
            "for n in range(num_nurses):\n",
            "    works = {}\n",
            "    for d in range(num_days):\n",
            "        works[d] = model.new_bool_var(f'works_{n}_{d}')\n",
            "        model.add(works[d] == sum(x[(n, d, s)] for s in range(num_shifts)))\n",
            "    for d in range(num_days - 3):\n",
            "        model.add(works[d] + works[d+1] + works[d+2] + works[d+3] <= 3)\n",
        ],
    }

    # Insert new Ex1b: pas plus de 5 jours consecutifs
    new_ex1b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "#### Exercice 1b : Limite de jours consecutifs configurable\n",
            "\n",
            "Generalisez la contrainte ci-dessus : ajoutez une contrainte qui limite\n",
            "a **`max_consecutive` jours consecutifs** de travail (parametre configurable).\n",
            "\n",
            "Testez avec `max_consecutive = 2` (plus strict) et `max_consecutive = 4` (plus permissif).\n",
            "\n",
            "**Consignes** :\n",
            "1. Definissez un parametre `max_consecutive` en debut de cellule\n",
            "2. Utilisez une boucle sur des fenetres glissantes de `max_consecutive + 1` jours\n",
            "3. Affichez le nombre de violations potentiels pour chaque valeur testee\n",
        ],
    }

    new_ex1b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 1b : Limite de jours consecutifs configurable\n",
            "\n",
            "# TODO: definissez max_consecutive et ajoutez la contrainte\n",
            "# Indice : reprenez le pattern de l'exemple mais rendez la taille de fenetre parametrable\n",
            "\n",
            "raise NotImplementedError\n",
        ],
    }

    nb["cells"].insert(47, new_ex1b_md)
    nb["cells"].insert(48, new_ex1b_code)

    # After insertion, indices shifted: Ex2 is now at 50=code
    # --- Ex2: preferences ponderees (now cell 50=code) ---
    nb["cells"][50] = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exemple resolu : preferences ponderees par priorite\n",
            "\n",
            "weighted_prefs = {\n",
            "    (0, 5, MATIN): 5,\n",
            "    (1, 0, NUIT): 10,\n",
            "    (2, 3, MATIN): 1,\n",
            "}\n",
            "\n",
            "penalty = sum(weight * x[(n, d, s)] for (n, d, s), weight in weighted_prefs.items())\n",
            "model.minimize(10 * balance_penalty + penalty)\n",
        ],
    }

    # Insert new Ex2b: preferences avec niveaux obligatoires
    new_ex2b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "#### Exercice 2b : Preferences avec contraintes obligatoires\n",
            "\n",
            "Certaines preferences sont en fait des **contraintes dures** (non-negociables),\n",
            "d'autres restent des preferences souples.\n",
            "\n",
            "**Consignes** :\n",
            "1. Definissez deux dictionnaires : `hard_prefs` (contraintes, poids infini)\n",
            "   et `soft_prefs` (preferences, poids 1-10)\n",
            "2. Les `hard_prefs` doivent etre ajoutees avec `model.add(... == 0)`\n",
            "3. Les `soft_prefs` sont minimisees dans l'objectif\n",
            "4. Exemples : hard = infirmier 0 jamais de NUIT, infirmier 3 jamais le dimanche\n",
        ],
    }

    new_ex2b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 2b : Preferences avec contraintes obligatoires\n",
            "\n",
            "# TODO: definissez hard_prefs et soft_prefs, puis ajoutez les contraintes\n",
            "# Indice : hard_prefs avec model.add(...) et soft_prefs avec model.minimize(...)\n",
            "\n",
            "raise NotImplementedError\n",
        ],
    }

    nb["cells"].insert(51, new_ex2b_md)
    nb["cells"].insert(52, new_ex2b_code)

    # After insertion, indices shifted: Ex3 is now at 54=code
    # --- Ex3: infirmiers a temps partiel (now cell 54=code) ---
    nb["cells"][54] = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exemple resolu : infirmiers a temps partiel\n",
            "\n",
            "max_shifts_per_nurse = {\n",
            "    0: 5,\n",
            "    1: 5,\n",
            "    2: 3,\n",
            "    3: 5,\n",
            "    4: 3,\n",
            "}\n",
            "\n",
            "for n in range(num_nurses):\n",
            "    total = sum(x[(n, d, s)] for d in range(num_days) for s in range(num_shifts))\n",
            "    model.add(total <= max_shifts_per_nurse[n])\n",
        ],
    }

    # Insert new Ex3b: contrats avec min/max shifts
    new_ex3b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "#### Exercice 3b : Contrats avec minimum et maximum de shifts\n",
            "\n",
            "Dans la realite, les infirmiers a temps partiel ont aussi un **minimum** de shifts\n",
            "a effectuer (garantie d'emploi). Generalisez le modele.\n",
            "\n",
            "**Consignes** :\n",
            "1. Definissez `contract_range = {n: (min_shifts, max_shifts) for n in range(num_nurses)}`\n",
            "2. Exemples : temps plein = (4, 5), mi-temps = (2, 3), 3/4 = (3, 4)\n",
            "3. Ajoutez les contraintes `min_shifts <= total <= max_shifts` pour chaque infirmier\n",
            "4. Verifiez que le solveur trouve une solution faisable\n",
        ],
    }

    new_ex3b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 3b : Contrats avec minimum et maximum de shifts\n",
            "\n",
            "# TODO: definissez contract_range et ajoutez les contraintes min/max\n",
            "# Indice : utilisez model.add(total >= min_shifts) et model.add(total <= max_shifts)\n",
            "\n",
            "raise NotImplementedError\n",
        ],
    }

    nb["cells"].insert(55, new_ex3b_md)
    nb["cells"].insert(56, new_ex3b_code)

    with open(path, "w", encoding="utf-8") as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)

    print(f"App-3 updated: {len(nb['cells'])} cells (+6 new cells)")


if __name__ == "__main__":
    fix_app3()
