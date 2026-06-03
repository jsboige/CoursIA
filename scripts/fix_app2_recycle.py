"""
Fix App-2-GraphColoring: Recycle student solutions into Exemple resolu + new stubs.

Issue #463: Recyclage solutions etudiants CSP Applications.
"""

import json


def fix_app2():
    path = "MyIA.AI.Notebooks/Search/Applications/CSP/App-2-GraphColoring.ipynb"
    with open(path, encoding="utf-8") as f:
        nb = json.load(f)

    # --- Ex1: US states coloring (cell 43=code) ---
    nb["cells"][43] = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exemple resolu : colorier les etats americains\n",
            "\n",
            "us_adjacency = {\n",
            '    "Ohio":          ["Indiana", "Kentucky", "West Virginia", "Michigan", "Pennsylvania"],\n',
            '    "Indiana":       ["Ohio", "Illinois", "Kentucky", "Michigan"],\n',
            '    "Illinois":      ["Indiana", "Iowa", "Missouri", "Kentucky", "Wisconsin"],\n',
            '    "Michigan":      ["Ohio", "Indiana", "Wisconsin"],\n',
            '    "Wisconsin":     ["Michigan", "Illinois", "Iowa", "Minnesota"],\n',
            '    "Minnesota":     ["Wisconsin", "Iowa"],\n',
            '    "Iowa":          ["Minnesota", "Wisconsin", "Illinois", "Missouri"],\n',
            '    "Missouri":      ["Iowa", "Illinois", "Kentucky"],\n',
            '    "Kentucky":      ["Ohio", "Indiana", "Illinois", "Missouri", "West Virginia"],\n',
            '    "West Virginia": ["Ohio", "Kentucky", "Pennsylvania"],\n',
            '    "Pennsylvania":  ["Ohio", "West Virginia"],\n',
            "}\n",
            "\n",
            "us_graph = nx.Graph()\n",
            "for state, neighbors in us_adjacency.items():\n",
            "    for n in neighbors:\n",
            "        us_graph.add_edge(state, n)\n",
            "\n",
            'for r in run_all_algorithms(us_graph, "US States"):\n',
            '    print(f"{r[\'algorithm\']:<25} {r[\'colors\']} couleurs  ({r[\'optimal\']})")\n',
        ],
    }

    # Insert new Ex1b: Europe countries
    new_ex1b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "#### Exercice 1b : Colorier les pays d'Europe de l'Ouest\n",
            "\n",
            "Construisez un graphe de 8-10 pays d'Europe de l'Ouest avec leurs frontieres\n",
            "et comparez les trois algorithmes.\n",
            "\n",
            "**Consignes** :\n",
            "1. Definissez un dictionnaire d'adjacence pour les pays : France, Espagne,\n",
            "   Portugal, Belgique, Allemagne, Suisse, Italie, Autriche, Pays-Bas, Luxembourg\n",
            "2. Construisez le graphe NetworkX\n",
            "3. Appelez `run_all_algorithms` et comparez les resultats\n",
        ],
    }

    new_ex1b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 1b : Colorier les pays d'Europe de l'Ouest\n",
            "\n",
            "# TODO: definissez le dictionnaire d'adjacence europe_adjacency\n",
            "# TODO: construisez le graphe et appelez run_all_algorithms\n",
            "# Indice : commencez par France -> Espagne, Belgique, Suisse, Allemagne, Italie, Luxembourg\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(44, new_ex1b_md)
    nb["cells"].insert(45, new_ex1b_code)

    # After insertion, Ex2 shifted: now at 47=code
    # --- Ex2: icosahedron greedy (now cell 47=code) ---
    nb["cells"][47] = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exemple resolu : borne superieure du greedy sur l'icosahedre\n",
            "\n",
            "icosahedron = nx.icosahedral_graph()\n",
            "_, n_opt, _ = cpsat_coloring(icosahedron)\n",
            "\n",
            "worst = 0\n",
            "for seed in range(30):\n",
            "    _, n = greedy_coloring(icosahedron, order_random(icosahedron, seed=seed))\n",
            "    worst = max(worst, n)\n",
            "\n",
            'print(f"optimum = {n_opt}, pire greedy = {worst}")\n',
        ],
    }

    # Insert new Ex2b: dodecahedron
    new_ex2b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "#### Exercice 2b : Comparaison greedy vs optimal sur le dodecahedre\n",
            "\n",
            "Reproduisez l'analyse ci-dessus sur le **dodecahedre** (`nx.dodecahedral_graph()`).\n",
            "\n",
            "**Consignes** :\n",
            "1. Calculez le nombre chromatique optimal avec `cpsat_coloring`\n",
            "2. Executez `greedy_coloring` avec 50 ordres aleatoires\n",
            "3. Comparez le meilleur/worst greedy avec l'optimal\n",
            "4. Expliquez pourquoi l'ecart est plus ou moins grand que sur l'icosahedre\n",
        ],
    }

    new_ex2b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 2b : Comparaison greedy vs optimal sur le dodecahedre\n",
            "\n",
            "# TODO: reproduisez l'analyse sur nx.dodecahedral_graph()\n",
            "# Indice : meme pattern que l'exemple, changez juste le graphe\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(48, new_ex2b_md)
    nb["cells"].insert(49, new_ex2b_code)

    # After insertion, Ex3 shifted: now at 51=code
    # --- Ex3: Welsh-Powell (now cell 51=code) ---
    nb["cells"][51] = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exemple resolu : Welsh-Powell et comparaison avec DSATUR\n",
            "\n",
            "def welsh_powell_coloring(G):\n",
            "    coloring = {}\n",
            "    sorted_vertices = sorted(G.nodes(), key=lambda v: G.degree(v), reverse=True)\n",
            "    uncolored = set(sorted_vertices)\n",
            "    color = 0\n",
            "    while uncolored:\n",
            "        layer = []\n",
            "        for v in sorted_vertices:\n",
            "            if v not in uncolored:\n",
            "                continue\n",
            "            if all(not G.has_edge(u, v) for u in layer):\n",
            "                layer.append(v)\n",
            "                coloring[v] = color\n",
            "                uncolored.remove(v)\n",
            "        color += 1\n",
            "    return coloring, max(coloring.values()) + 1\n",
            "\n",
            "\n",
            "for i in range(5):\n",
            "    G = nx.erdos_renyi_graph(50, 0.3, seed=i)\n",
            "    _, n_wp = welsh_powell_coloring(G)\n",
            "    _, n_ds = dsatur_coloring(G)\n",
            "    _, n_cp, _ = cpsat_coloring(G, time_limit=10)\n",
            '    print(f"G{i}: WP={n_wp}, DSATUR={n_ds}, optimal={n_cp}")\n',
        ],
    }

    # Insert new Ex3b: DSATUR variant
    new_ex3b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "#### Exercice 3b : Implementez un algorithme de coloration par saturation\n",
            "\n",
            "L'algorithme DSATUR (Degree of SATURation) choisit le sommet non colore\n",
            "avec le plus grand nombre de couleurs differentes dans son voisinage.\n",
            "\n",
            "**Consignes** :\n",
            "1. Implementez `dsatur_manual(G)` sans utiliser la fonction `dsatur_coloring` fournie\n",
            "2. A chaque etape, choisissez le sommet non colore avec la saturation maximale\n",
            "3. En cas d'egalite, choisissez le sommet de degre maximal\n",
            "4. Comparez vos resultats avec `dsatur_coloring` sur 10 graphes aleatoires\n",
        ],
    }

    new_ex3b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 3b : Implementez DSATUR manuellement\n",
            "\n",
            "# TODO: implementez dsatur_manual(G)\n",
            "# Indice : utilisez un dictionnaire saturation[v] = nombre de couleurs distinctes dans le voisinage\n",
            "# A chaque iteration : trouver le sommet non colore avec max(saturation), puis max(degree)\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(52, new_ex3b_md)
    nb["cells"].insert(53, new_ex3b_code)

    with open(path, "w", encoding="utf-8") as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)

    print(f"App-2 updated: {len(nb['cells'])} cells (+6 new cells)")


if __name__ == "__main__":
    fix_app2()
