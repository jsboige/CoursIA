"""
Recycle CSP-8-Temporal exercises (Issue #463).

Converts 4 student solutions into labeled "Exemple resolu" cells
and creates new exercise stubs with variant data.
"""

import json


def main():
    path = "MyIA.AI.Notebooks/Search/Part2-CSP/CSP-8-Temporal.ipynb"
    with open(path, encoding="utf-8") as f:
        nb = json.load(f)

    # --- Exercise layout (33 cells) ---
    # [24] md  : Ex1 Allen composition table
    # [25] code: Ex1 table de composition (58L)
    # [26] md  : Ex2 STP avec deadlines
    # [27] code: Ex2 STPWithDeadlines (45L)
    # [28] md  : Ex3 Planning multi-reunions
    # [29] code: Ex3 Multi-reunions CP-SAT (105L)
    # [30] md  : Ex4 STP avec OR-Tools CP-SAT
    # [31] code: Ex4 solve_stp_cp_sat (80L)
    # [32] md  : References

    # ================================================================
    # Ex1: Allen composition table → Exemple resolu (cell 25)
    # ================================================================
    nb["cells"][25]["source"][0] = "# Exemple resolu : Table de composition d'Allen par enumeration\n"
    nb["cells"][25]["outputs"] = []
    nb["cells"][25]["execution_count"] = None

    ex1b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 1b : Inverse et composition partielle d'Allen\n",
            "\n",
            "**Enonce** : Implementez deux fonctions sur les relations d'Allen :\n",
            "\n",
            "1. `inverse_relation(r: AllenRelation) -> AllenRelation` : retourne la relation inverse\n",
            "   (ex : BEFORE <-> AFTER, MEETS <-> MET_BY)\n",
            "2. `compose_pair(r1: AllenRelation, r2: AllenRelation) -> Set[AllenRelation]` : retourne\n",
            "   la composition de deux relations (sans enumeration exhaustive, utilisez les proprietes)\n",
            "\n",
            "**Consignes** :\n",
            "1. Inspirez-vous de la table de composition de l'exemple ci-dessus\n",
            "2. Utilisez les symetries (ex : inverse de BEFORE = AFTER)\n",
            "3. Verifiez : `compose(BEFORE, OVERLAPS) == {BEFORE, OVERLAPS, MEETS, FINISHED_BY}`\n",
        ],
    }

    ex1b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 1b : Inverse et composition partielle d'Allen\n",
            "\n",
            "# TODO: implementez inverse_relation(r)\n",
            "# Indice : 6 paires de relations inverses (BEFORE/AFTER, MEETS/MET_BY, etc.)\n",
            "\n",
            "# TODO: implementez compose_pair(r1, r2)\n",
            "# Indice : decomposez en cas selon les proprietes des intervalles\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(26, ex1b_md)
    nb["cells"].insert(27, ex1b_code)

    # ================================================================
    # Ex2: STP avec deadlines → Exemple resolu (now cell 29)
    # ================================================================
    nb["cells"][29]["source"][0] = "# Exemple resolu : STP avec deadlines\n"
    nb["cells"][29]["outputs"] = []
    nb["cells"][29]["execution_count"] = None

    ex2b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 2b : STP pour planification de projet avec contraintes\n",
            "\n",
            "**Enonce** : Utilisez `SimpleTemporalProblem` (ou `STPWithDeadlines`) pour\n",
            "modeliser un **projet de construction** avec des contraintes temporelles.\n",
            "\n",
            "Taches et durees :\n",
            "- Fondations : 3 jours (demarre au jour 0)\n",
            "- Structure : 5 jours (apres fondations)\n",
            "- Toiture : 2 jours (apres structure)\n",
            "- Electricite : 2 jours (apres structure, avant finition)\n",
            "- Plomberie : 3 jours (apres structure, avant finition)\n",
            "- Finition : 4 jours (apres toiture, electricite et plomberie)\n",
            "- Deadline : tout doit etre termine avant le jour 25\n",
            "\n",
            "**Consignes** :\n",
            "1. Modelisez les contraintes de precedence et les durees dans un STP\n",
            "2. Ajoutez la deadline comme contrainte sur le dernier evenement\n",
            "3. Trouvez l'horaire optimal et affichez-le sous forme de diagramme de Gantt\n",
        ],
    }

    ex2b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 2b : STP pour planification de projet\n",
            "\n",
            "# TODO: definissez les evenements (debut + fin de chaque tache)\n",
            "# TODO: ajoutez les contraintes de precedence et de duree\n",
            "# Indice : pour \"Structure prend 5 jours\", contrainte : fin_struct - debut_struct in [5, 5]\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(30, ex2b_md)
    nb["cells"].insert(31, ex2b_code)

    # ================================================================
    # Ex3: Planning multi-reunions → Exemple resolu (now cell 33)
    # ================================================================
    nb["cells"][33]["source"][0] = "# Exemple resolu : Planification multi-reunions avec precedences\n"
    nb["cells"][33]["outputs"] = []
    nb["cells"][33]["execution_count"] = None

    ex3b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 3b : Planification de cours avec contraintes de salle\n",
            "\n",
            "**Enonce** : Planifiez **6 cours** dans une journee (8h-18h) avec :\n",
            "\n",
            "- Des contraintes de **precedence** (certains cours doivent etre avant d'autres)\n",
            "- Des contraintes de **salle** (2 salles disponibles, un seul cours par salle par creneau)\n",
            "- Des contraintes de **duree** (chaque cours dure 1h ou 2h)\n",
            "\n",
            "Precedences : CoursA avant CoursC, CoursB avant CoursD, CoursC avant CoursE\n",
            "\n",
            "**Consignes** :\n",
            "1. Inspirez-vous du modele CP-SAT de l'exemple multi-reunions\n",
            "2. Ajoutez des variables pour le choix de salle\n",
            "3. Affichez l'emploi du temps optimal\n",
        ],
    }

    ex3b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 3b : Planification de cours avec contraintes de salle\n",
            "\n",
            "# TODO: definissez les cours, durees et precedences\n",
            "# COURSES = {'A': 1, 'B': 2, 'C': 1, 'D': 1, 'E': 2, 'F': 1}  # durees en heures\n",
            "# PRECEDENCES = [('A', 'C'), ('B', 'D'), ('C', 'E')]\n",
            "\n",
            "# TODO: creez le modele CP-SAT avec variables start[i], duration[i], room[i]\n",
            "# Indice : noOverlap pour chaque salle + precedence pour les contraintes d'ordre\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(34, ex3b_md)
    nb["cells"].insert(35, ex3b_code)

    # ================================================================
    # Ex4: STP avec OR-Tools → Exemple resolu (now cell 37)
    # ================================================================
    nb["cells"][37]["source"][0] = "# Exemple resolu : STP resolu avec OR-Tools CP-SAT\n"
    nb["cells"][37]["outputs"] = []
    nb["cells"][37]["execution_count"] = None

    ex4b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 4b : STP disjonctif avec intervals d'Allen\n",
            "\n",
            "**Enonce** : Combinez le STP avec les **relations d'Allen** pour modeliser\n",
            "un probleme ou certaines taches doivent etre dans une relation specifique.\n",
            "\n",
            "Scenario : Planification d'une conference avec 4 presentations :\n",
            "- Keynote doit OVERLAP avec au moins une autre presentation\n",
            "- Talk1 et Talk2 doivent se MEET (fin de l'un = debut de l'autre)\n",
            "- Workshop doit etre AFTER Talk2\n",
            "- Chaque presentation dure entre 30 min et 2h\n",
            "\n",
            "**Consignes** :\n",
            "1. Utilisez CP-SAT avec des variables de debut et fin pour chaque presentation\n",
            "2. Modelisez les relations d'Allen comme des contraintes lineaires\n",
            "   (ex : MEET(A, B) = fin_A == debut_B)\n",
            "3. Trouvez un horaire valide\n",
        ],
    }

    ex4b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 4b : STP disjonctif avec relations d'Allen\n",
            "\n",
            "# TODO: definissez les 4 presentations et leurs contraintes\n",
            "# presentations = ['Keynote', 'Talk1', 'Talk2', 'Workshop']\n",
            "\n",
            "# TODO: modelisez les relations d'Allen comme contraintes CP-SAT\n",
            "# Indice : OVERLAP = debut_A < fin_B ET debut_B < fin_A\n",
            "#          MEET(A, B) = fin_A == debut_B\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(38, ex4b_md)
    nb["cells"].insert(39, ex4b_code)

    # ================================================================
    # Write back
    # ================================================================
    with open(path, "w", encoding="utf-8") as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)

    print(f"CSP-8 updated: {len(nb['cells'])} cells (was 33, +8 new cells)")


if __name__ == "__main__":
    main()
