"""
Recycle CSP-4-Scheduling: split 411-line solution cell into 4 Exemples
and create new exercise stubs with variants.

Pattern: fix_issue_420.py (PR #453, Issue #420)
Reference: Issue #463
"""

import json

path = "MyIA.AI.Notebooks/Search/Part2-CSP/CSP-4-Scheduling.ipynb"

with open(path, encoding="utf-8") as f:
    nb = json.load(f)

src = "".join(nb["cells"][26]["source"])
lines = src.split("\n")

# Section boundaries (0-indexed lines)
sections = [
    (0, 105),    # Ex1: JSSP deadlines
    (105, 213),  # Ex2: RCPSP non-renouvelable
    (213, 326),  # Ex3: Nurse preferences
    (326, 411),  # Ex4: Multi-objectif
]

# Replace markdown cell [25] with per-exercise headers
nb["cells"][25] = {
    "cell_type": "markdown",
    "metadata": {},
    "source": [
        "## 5. Exercices\n",
        "\n",
        "Les exemples resolus ci-dessous illustrent les techniques avancees d'ordonnancement.\n",
        "Chaque exercice demande d'adapter ces techniques a un nouveau probleme.\n",
    ],
}

# Build new cells to replace cell[26]
new_cells = []

# --- Ex1: JSSP with deadlines -> Exemple resolu ---
ex1_lines = lines[0:105]
ex1_source = [line + "\n" for line in ex1_lines[:-1]] + [ex1_lines[-1]]
ex1_source[0] = "# Exemple resolu : JSSP avec deadlines\n"

new_cells.append({
    "cell_type": "code",
    "execution_count": None,
    "metadata": {},
    "outputs": [],
    "source": ex1_source,
})

# New Ex1 stub: different job data
new_cells.append({
    "cell_type": "markdown",
    "metadata": {},
    "source": [
        "### Exercice 1 : JSSP avec deadlines serrees\n",
        "\n",
        "**Enonce** : Resolvez un JSSP avec 4 jobs et 3 machines, en ajoutant des deadlines\n",
        "plus strictes. Utilisez les donnees suivantes :\n",
        "\n",
        "```python\n",
        "jobs_data = [\n",
        "    [(0, 3), (1, 2), (2, 2)],  # Job 0\n",
        "    [(1, 4), (2, 3)],           # Job 1\n",
        "    [(0, 2), (2, 3), (1, 3)],  # Job 2\n",
        "    [(2, 2), (0, 4), (1, 1)],  # Job 3\n",
        "]\n",
        "deadlines = [8, 10, 9, 11]\n",
        "```\n",
        "\n",
        "**Consignes** :\n",
        "1. Inspirez-vous de l'exemple ci-dessus pour modeliser le probleme\n",
        "2. Utilisez `AddMaxEquality` pour calculer le retard maximum\n",
        "3. Minimisez le retard maximum et affichez le schedule\n",
    ],
})

new_cells.append({
    "cell_type": "code",
    "execution_count": None,
    "metadata": {},
    "outputs": [],
    "source": [
        "# Exercice 1 : JSSP avec deadlines serrees\n",
        "\n",
        "# TODO: definissez les donnees jobs_data et deadlines ci-dessus\n",
        "# Indice : reutilisez le schema de l'exemple (variables d'intervalle, NoOverlap, lateness)\n",
        "\n",
        "# Votre code ici\n",
    ],
})

# --- Ex2: RCPSP non-renouvelable -> Exemple resolu ---
ex2_lines = lines[105:213]
ex2_source = [line + "\n" for line in ex2_lines[:-1]] + [ex2_lines[-1]]
ex2_source[0] = "# Exemple resolu : RCPSP avec ressources non-renouvelables\n"

new_cells.append({
    "cell_type": "code",
    "execution_count": None,
    "metadata": {},
    "outputs": [],
    "source": ex2_source,
})

# New Ex2 stub: different resources
new_cells.append({
    "cell_type": "markdown",
    "metadata": {},
    "source": [
        "### Exercice 2 : RCPSP avec budget limite\n",
        "\n",
        "**Enonce** : Etendez le modele RCPSP pour gerer un budget global. Chaque tache\n",
        "a un cout, et le budget total ne doit pas etre depasse.\n",
        "\n",
        "**Consignes** :\n",
        "1. Ajoutez une variable de cout par tache\n",
        "2. Posez la contrainte : somme des couts des taches selectionnees <= budget\n",
        "3. Minimisez le makespan tout en respectant le budget\n",
    ],
})

new_cells.append({
    "cell_type": "code",
    "execution_count": None,
    "metadata": {},
    "outputs": [],
    "source": [
        "# Exercice 2 : RCPSP avec budget limite\n",
        "\n",
        "# TODO: definissez les taches avec couts et contraintes de precedence\n",
        "# Indice : utilisez model.NewIntVar pour les couts et model.Add pour la contrainte budget\n",
        "\n",
        "# Votre code ici\n",
    ],
})

# --- Ex3: Nurse preferences -> Exemple resolu ---
ex3_lines = lines[213:326]
ex3_source = [line + "\n" for line in ex3_lines[:-1]] + [ex3_lines[-1]]
ex3_source[0] = "# Exemple resolu : Nurse Scheduling avec preferences\n"

new_cells.append({
    "cell_type": "code",
    "execution_count": None,
    "metadata": {},
    "outputs": [],
    "source": ex3_source,
})

# New Ex3 stub: different constraints
new_cells.append({
    "cell_type": "markdown",
    "metadata": {},
    "source": [
        "### Exercice 3 : Nurse Scheduling avec equilibrage de charge\n",
        "\n",
        "**Enonce** : Ajoutez une contrainte d'equilibrage : chaque infirmier doit travailler\n",
        "entre `min_shifts` et `max_shifts` tours sur la semaine.\n",
        "\n",
        "**Consignes** :\n",
        "1. Parametres : 5 infirmiers, 7 jours, 3 tours/jour\n",
        "2. Contraintes : pas de doubles tours, max 5 jours consecutifs\n",
        "3. Equilibrage : chaque infirmier fait entre 3 et 5 tours\n",
        "4. Maximisez la satisfaction (preferences)\n",
    ],
})

new_cells.append({
    "cell_type": "code",
    "execution_count": None,
    "metadata": {},
    "outputs": [],
    "source": [
        "# Exercice 3 : Nurse Scheduling avec equilibrage\n",
        "\n",
        "# TODO: definissez les variables de decision et les contraintes\n",
        "# Indice : utilisez model.Add(sum(...) >= min_shifts) pour l'equilibrage\n",
        "\n",
        "# Votre code ici\n",
    ],
})

# --- Ex4: Multi-objectif -> Exemple resolu ---
ex4_lines = lines[326:411]
ex4_source = [line + "\n" for line in ex4_lines[:-1]] + [ex4_lines[-1]]
ex4_source[0] = "# Exemple resolu : JSSP multi-objectif\n"

new_cells.append({
    "cell_type": "code",
    "execution_count": None,
    "metadata": {},
    "outputs": [],
    "source": ex4_source,
})

# New Ex4 stub: Pareto exploration
new_cells.append({
    "cell_type": "markdown",
    "metadata": {},
    "source": [
        "### Exercice 4 : Exploration du front de Pareto\n",
        "\n",
        "**Enonce** : Au lieu d'utiliser une ponderation fixe, trouvez plusieurs solutions\n",
        "Pareto-optimales en variant les poids `weight_makespan` et `weight_tardiness`.\n",
        "\n",
        "**Consignes** :\n",
        "1. Testez au moins 5 combinaisons de poids (ex: (10,1), (5,5), (1,10), (1,1), (20,1))\n",
        "2. Pour chaque combinaison, affichez makespan, tardiness totale et objectif pondere\n",
        "3. Tracez le front de Pareto (makespan vs tardiness) avec matplotlib\n",
    ],
})

new_cells.append({
    "cell_type": "code",
    "execution_count": None,
    "metadata": {},
    "outputs": [],
    "source": [
        "# Exercice 4 : Exploration du front de Pareto\n",
        "\n",
        "# TODO: bouclez sur differentes ponderations et collectez les resultats\n",
        "# Indice : stockez (makespan, tardiness) dans une liste et tracez avec plt.scatter\n",
        "\n",
        "# Votre code ici\n",
    ],
})

# Replace cell[26] with new cells
nb["cells"][26:27] = new_cells

with open(path, "w", encoding="utf-8") as f:
    json.dump(nb, f, ensure_ascii=False, indent=1)

print(f"CSP-4 updated: {len(nb['cells'])} cells (was 29, +{len(new_cells) - 1} new cells)")
print("Split 411-line cell into 4 Exemples + 4 stubs TODO")
