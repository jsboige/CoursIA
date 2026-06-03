"""
Recycle CSP-6-Hybridization exercises (Issue #463).

Converts 4 student solutions into labeled "Exemple resolu" cells
and creates new exercise stubs with variant data.
"""

import json


def main():
    path = "MyIA.AI.Notebooks/Search/Part2-CSP/CSP-6-Hybridization.ipynb"
    with open(path, encoding="utf-8") as f:
        nb = json.load(f)

    # --- Exercise layout (33 cells) ---
    # [22] md  : "## 6. Exercices" header
    # [23] md  : Ex1 enonce (Generation de modeles)
    # [24] code: Ex1 solution (106L)
    # [25] md  : Ex2 enonce (ML pour branching)
    # [26] code: Ex2 solution (94L)
    # [27] md  : Ex3 enonce (Portfolio dynamique)
    # [28] code: Ex3 solution (103L)
    # [29] md  : Ex4 enonce (Integration LLM)
    # [30] code: Ex4 solution (95L)
    # [31] md  : References
    # [32] md  : Conclusion

    # ================================================================
    # Ex1: Parser JSON → modele CP-SAT → Exemple resolu (cell 24)
    # ================================================================
    nb["cells"][24]["source"][0] = "# Exemple resolu : Parser JSON vers modele CP-SAT\n"
    nb["cells"][24]["outputs"] = []
    nb["cells"][24]["execution_count"] = None

    ex1b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 1b : Parser JSON pour un probleme d'ordonnancement\n",
            "\n",
            "**Enonce** : Ecrivez un parser JSON qui convertit une description d'un probleme\n",
            "d'ordonnancement en modele CP-SAT.\n",
            "\n",
            "Format d'entree JSON :\n",
            "```json\n",
            '{\n'
            '  "tasks": [\n'
            '    {"id": "T1", "duration": 3, "resources": ["R1"]},\n'
            '    {"id": "T2", "duration": 5, "resources": ["R2"]},\n'
            '    {"id": "T3", "duration": 2, "resources": ["R1", "R2"]}\n'
            '  ],\n'
            '  "precedences": [["T1", "T3"], ["T2", "T3"]],\n'
            '  "horizon": 15\n'
            '}\n'
            '```\n',
            "\n",
            "**Consignes** :\n",
            "1. Inspirez-vous du parser JSON de l'exemple ci-dessus\n",
            "2. Ajoutez les contraintes de precedence ET les contraintes de ressources\n",
            "3. Minimisez le makespan (date de fin de la derniere tache)\n",
        ],
    }

    ex1b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 1b : Parser JSON pour ordonnancement\n",
            "\n",
            "scheduling_json = {\n",
            '    "tasks": [\n',
            '        {"id": "T1", "duration": 3, "resources": ["R1"]},\n',
            '        {"id": "T2", "duration": 5, "resources": ["R2"]},\n',
            '        {"id": "T3", "duration": 2, "resources": ["R1", "R2"]},\n',
            '        {"id": "T4", "duration": 4, "resources": ["R1"]},\n',
            "    ],\n",
            '    "precedences": [["T1", "T3"], ["T2", "T3"], ["T3", "T4"]],\n',
            '    "horizon": 15\n',
            "}\n",
            "\n",
            "# TODO: parsez le JSON et construisez le modele CP-SAT\n",
            "# Indice : utilisez des IntVar pour les dates de debut de chaque tache\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(25, ex1b_md)
    nb["cells"].insert(26, ex1b_code)

    # ================================================================
    # Ex2: VSIDS-like branching → Exemple resolu (now cell 28)
    # ================================================================
    nb["cells"][28]["source"][0] = "# Exemple resolu : Heuristique de branching VSIDS-like\n"
    nb["cells"][28]["outputs"] = []
    nb["cells"][28]["execution_count"] = None

    ex2b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 2b : Branching base sur l'activite\n",
            "\n",
            "**Enonce** : Implementez une heuristique de selection de variables basee sur\n",
            "l'**activite** (activity-based branching), ou chaque variable recoit un score\n",
            "proportionnel au nombre de contraintes dans lesquelles elle apparait.\n",
            "\n",
            "Contrairement a VSIDS (historique des conflits), l'activite mesure la\n",
            "**connectivite** de la variable dans le graphe de contraintes.\n",
            "\n",
            "**Consignes** :\n",
            "1. Pour chaque variable, comptez le nombre de contraintes impliquant cette variable\n",
            "2. Selectionnez la variable avec le score d'activite le plus eleve\n",
            "3. Comparez les performances (temps, noeuds) avec VSIDS sur les memes instances\n",
        ],
    }

    ex2b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 2b : Branching base sur l'activite\n",
            "\n",
            "# TODO: definissez une classe ActivityBrancher\n",
            "# Indice : calculez score[var] = nombre de contraintes impliquant var\n",
            "\n",
            "# class ActivityBrancher:\n",
            "#     def __init__(self, constraints):\n",
            "#         self.activity = {}\n",
            "#         # TODO: calculez l'activite de chaque variable\n",
            "#\n",
            "#     def select_variable(self, unassigned_vars):\n",
            "#         # TODO: retournez la variable avec l'activite max\n",
            "#         pass\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(29, ex2b_md)
    nb["cells"].insert(30, ex2b_code)

    # ================================================================
    # Ex3: Dynamic portfolio → Exemple resolu (now cell 32)
    # ================================================================
    nb["cells"][32]["source"][0] = "# Exemple resolu : Portfolio dynamique avec bascule\n"
    nb["cells"][32]["outputs"] = []
    nb["cells"][32]["execution_count"] = None

    ex3b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 3b : Portfolio avec 5 strategies et timeout adaptatif\n",
            "\n",
            "**Enonce** : Etendez le portfolio dynamique pour gerer **5 strategies** au lieu de 3,\n",
            "avec un mecanisme de timeout adaptatif qui double le temps alloue a chaque strategie\n",
            "apres chaque echec.\n",
            "\n",
            "Strategies suggerees :\n",
            "1. Recherche naive (no heuristic)\n",
            "2. Fail-first (smallest domain)\n",
            "3. Dom/Wdeg (weighted degree)\n",
            "4. Random (with restarts)\n",
            "5. Activity-based\n",
            "\n",
            "**Consignes** :\n",
            "1. Inspirez-vous du DynamicPortfolio de l'exemple ci-dessus\n",
            "2. Ajoutez un parametre `base_timeout` qui double apres chaque echec\n",
            "3. Mesurez et affichez le temps passe dans chaque strategie\n",
        ],
    }

    ex3b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 3b : Portfolio avec 5 strategies et timeout adaptatif\n",
            "\n",
            "# TODO: creez une classe ExtendedPortfolio avec 5 strategies\n",
            "# Indice : le timeout adaptatif double a chaque echec\n",
            "# base_timeout * (2 ** num_failures)\n",
            "\n",
            "# class ExtendedPortfolio:\n",
            "#     def __init__(self, strategies, base_timeout=5.0):\n",
            "#         ...\n",
            "#\n",
            "#     def solve(self, problem, max_total_time=60):\n",
            "#         # TODO: boucle avec timeout adaptatif\n",
            "#         pass\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(33, ex3b_md)
    nb["cells"].insert(34, ex3b_code)

    # ================================================================
    # Ex4: LLM pipeline → Exemple resolu (now cell 36)
    # ================================================================
    nb["cells"][36]["source"][0] = "# Exemple resolu : Pipeline LLM vers CSP\n"
    nb["cells"][36]["outputs"] = []
    nb["cells"][36]["execution_count"] = None

    ex4b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 4b : Pipeline LLM pour un probleme de coloration de graphe\n",
            "\n",
            "**Enonce** : Adaptez le pipeline LLM pour un probleme de **coloration de graphe**.\n",
            "Le LLM recoit une description textuelle du graphe et doit produire un JSON\n",
            "avec les variables (noeuds), les domaines (couleurs) et les contraintes (aretes).\n",
            "\n",
            "Description d'entree :\n",
            "```\n",
            "Coloriez les 6 regions suivantes avec 3 couleurs (R, V, B)\n",
            "de sorte que deux regions adjacentes n'aient pas la meme couleur.\n",
            "Adjacences : A-B, A-C, B-C, B-D, C-E, D-E, D-F, E-F\n",
            "```\n",
            "\n",
            "**Consignes** :\n",
            "1. Inspirez-vous du mock LLM de l'exemple ci-dessus\n",
            "2. Simulez la reponse du LLM avec un dictionnaire pre-formatte\n",
            "3. Parsez la reponse et construisez le modele CP-SAT\n",
            "4. Resolvez et affichez la coloration obtenue\n",
        ],
    }

    ex4b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 4b : Pipeline LLM pour coloration de graphe\n",
            "\n",
            "# TODO: simulez la reponse d'un LLM pour un probleme de coloration\n",
            "# Le JSON doit contenir : variables (noeuds), domaines (couleurs),\n",
            "# et contraintes (paires de noeuds adjacents)\n",
            "\n",
            "# mock_llm_response = {\n",
            '#     "variables": ["A", "B", "C", "D", "E", "F"],\n',
            '#     "domains": {"A": ["R","V","B"], ...},\n',
            '#     "constraints": [{"type": "neq", "vars": ["A","B"]}, ...]\n',
            "# }\n",
            "\n",
            "# TODO: parsez et resolvez avec CP-SAT\n",
            "# Indice : utilisez des NewBoolVar ou NewIntVar pour les couleurs\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(37, ex4b_md)
    nb["cells"].insert(38, ex4b_code)

    # ================================================================
    # Write back
    # ================================================================
    with open(path, "w", encoding="utf-8") as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)

    print(f"CSP-6 updated: {len(nb['cells'])} cells (was 33, +8 new cells)")


if __name__ == "__main__":
    main()
