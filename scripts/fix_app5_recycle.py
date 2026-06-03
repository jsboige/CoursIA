"""
Fix App-5-Timetabling: recycle Ex1 solution into Exemple cell + new stub.

Part of Issue #463: recyclage App-1..App-11.
Only Ex1 needs recycling; Ex2 and Ex3 are already stubs.
"""

import json


def fix_app5():
    path = "MyIA.AI.Notebooks/Search/Applications/CSP/App-5-Timetabling.ipynb"
    with open(path, encoding="utf-8") as f:
        nb = json.load(f)

    # --- Ex1: solve_timetable_cpsat (cell 37, 177L) ---
    # Keep the same source content, just relabel and clear outputs
    old_source = nb["cells"][37]["source"]
    old_source[0] = "# Exemple resolu : pas de 3 heures consecutives pour un enseignant\n"

    nb["cells"][37] = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": old_source,
    }

    # Insert new Ex1b: minimize teacher idle time
    new_ex1b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 1b : minimiser le temps d'attente entre cours\n",
            "\n",
            "**Enonce** : un enseignant qui donne plusieurs cours dans la journee\n",
            "prefere qu'ils soient regroupes plutot qu'eparpilles. Ajoutez un\n",
            "**objectif d'optimisation** pour minimiser le temps d'attente total\n",
            "des enseignants entre leurs cours.\n",
            "\n",
            "**Consignes** :\n",
            "1. Appelez `solve_timetable_cpsat` definie ci-dessus pour obtenir\n",
            "   une solution de base\n",
            "2. Copiez et modifiez la fonction pour ajouter une variable\n",
            "   `idle_time` par enseignant et minimisez la somme\n",
            "3. Comparez les emplois du temps avec et sans l'objectif\n",
        ],
    }

    new_ex1b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 1b : minimiser le temps d'attente\n",
            "\n",
            "# TODO: copiez solve_timetable_cpsat et ajoutez un objectif\n",
            "# pour minimiser l'ecart entre les creneaux de chaque enseignant\n",
            "# Indice : pour chaque enseignant, calculez max_slot - min_slot\n",
            "# et minimisez la somme\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(38, new_ex1b_md)
    nb["cells"].insert(39, new_ex1b_code)

    with open(path, "w", encoding="utf-8") as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)

    print(f"App-5 updated: {len(nb['cells'])} cells (was 44, +2 new cells)")


if __name__ == "__main__":
    fix_app5()
    print("Done.")
