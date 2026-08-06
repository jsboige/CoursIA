"""
Recycle CSP-9-Distributed exercises (Issue #463).

Converts 4 student solutions into labeled "Exemple resolu" cells
and creates new exercise stubs with variant data.
"""

import json


def main():
    path = "MyIA.AI.Notebooks/Search/Part2-CSP/CSP-9-Distributed.ipynb"
    with open(path, encoding="utf-8") as f:
        nb = json.load(f)

    # --- Exercise layout (38 cells) ---
    # [27] md  : Section header "7. Exercices"
    # [28] code: Ex1 N-reines distribuees avec ABT (59L)
    # [29] md  : Ex2 Comparaison ABT vs AWC
    # [30] code: Ex2 Comparaison ABT vs AWC (70L)
    # [31] md  : Ex3 Negociation multi-agent
    # [32] code: Ex3 Negociation multi-agent (90L)
    # [33] md  : Ex4 Analyse fuite d'information
    # [34] code: Ex4 Fuite d'information (77L)
    # [35] md  : References
    # [36] code: Resume notebook
    # [37] md  : Synthese

    # ================================================================
    # Ex1: N-reines distribuees → Exemple resolu (cell 28)
    # ================================================================
    nb["cells"][28]["source"][0] = "# Exemple resolu : N-reines distribuees avec ABT\n"
    nb["cells"][28]["outputs"] = []
    nb["cells"][28]["execution_count"] = None

    ex1b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 1b : Coloration de graphe distribuee avec 5 couleurs\n",
            "\n",
            "**Enonce** : Utilisez `ABTSystem` pour resoudre un probleme de coloration\n",
            "de graphe avec **5 noeuds** et **5 couleurs**.\n",
            "\n",
            "Graphe (topologie differente de l'exemple) :\n",
            "- Aretes : 0-1, 0-2, 1-3, 2-3, 3-4\n",
            "- Domaine : {R, G, B, Y, P} (Rouge, Vert, Bleu, Jaune, Violet)\n",
            "\n",
            "**Consignes** :\n",
            "1. Inspirez-vous de l'exemple de coloration 4-noeuds de l'exemple ci-dessus\n",
            "2. Verifiez que la solution est valide (pas de conflit sur les aretes)\n",
            "3. Affichez le nombre total de messages echanges\n",
        ],
    }

    ex1b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 1b : Coloration de graphe distribuee avec 5 couleurs\n",
            "\n",
            "# TODO: definissez le graphe et le domaine\n",
            "# graph_edges_5 = [(0, 1), (0, 2), (1, 3), (2, 3), (3, 4)]\n",
            "# domain_5 = ['R', 'G', 'B', 'Y', 'P']\n",
            "\n",
            "# TODO: creez les agents ABT et le systeme\n",
            "# Indice : utilisez ABTAgent et ABTSystem comme dans l'exemple\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(29, ex1b_md)
    nb["cells"].insert(30, ex1b_code)

    # ================================================================
    # Ex2: Comparaison ABT vs AWC → Exemple resolu (now cell 32)
    # ================================================================
    nb["cells"][32]["source"][0] = "# Exemple resolu : Comparaison ABT vs AWC sur coloration aleatoire\n"
    nb["cells"][32]["outputs"] = []
    nb["cells"][32]["execution_count"] = None

    ex2b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 2b : Impact de la densite de contraintes sur ABT\n",
            "\n",
            "**Enonce** : Etudiez l'impact de la **densite de contraintes** sur les performances\n",
            "d'ABT. Faites varier la densite et mesurez le nombre de messages.\n",
            "\n",
            "Parametres :\n",
            "- N agents fixe a 6, domaine fixe a 3 couleurs\n",
            "- Densites a tester : 0.2, 0.4, 0.6, 0.8\n",
            "- 10 instances par densite (moyenne)\n",
            "\n",
            "**Consignes** :\n",
            "1. Utilisez la fonction `_random_coloring_problem` de l'exemple\n",
            "2. Tracez un graphique : densite (x) vs nombre de messages (y)\n",
            "3. Analysez : a quelle densite ABT commence-t-il a peiner ?\n",
        ],
    }

    ex2b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 2b : Impact de la densite de contraintes sur ABT\n",
            "\n",
            "# TODO: bouclez sur les densites [0.2, 0.4, 0.6, 0.8]\n",
            "# TODO: pour chaque densite, genereez 10 instances et mesurez les messages\n",
            "# Indice : reutilisez _random_coloring_problem et ABTSystem\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(33, ex2b_md)
    nb["cells"].insert(34, ex2b_code)

    # ================================================================
    # Ex3: Negociation multi-agent → Exemple resolu (now cell 36)
    # ================================================================
    nb["cells"][36]["source"][0] = "# Exemple resolu : Negociation multi-agent avec preferences secretes\n"
    nb["cells"][36]["outputs"] = []
    nb["cells"][36]["execution_count"] = None

    ex3b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 3b : Allocation de taches avec preferences privees\n",
            "\n",
            "**Enonce** : 5 agents doivent se repartir 8 taches. Chaque agent a des\n",
            "**preferences secretes** (score de preference pour chaque tache).\n",
            "\n",
            "Contraintes :\n",
            "- Chaque tache est assignee a exactement un agent\n",
            "- Chaque agent a au maximum 2 taches\n",
            "- Les preferences ne sont jamais revelees en clair\n",
            "\n",
            "**Consignes** :\n",
            "1. Inspirez-vous de `NegotiationAgent` de l'exemple\n",
            "2. Utilisez `PrivacyPreservingAgent` comme classe de base\n",
            "3. Affichez l'allocation finale et le score de satisfaction total\n",
        ],
    }

    ex3b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 3b : Allocation de taches avec preferences privees\n",
            "\n",
            "# TODO: definissez 5 agents et 8 taches\n",
            "# TASKS = ['T1', 'T2', 'T3', 'T4', 'T5', 'T6', 'T7', 'T8']\n",
            "# Chaque agent a un score secret pour chaque tache\n",
            "\n",
            "# TODO: implementez le protocole de negociation\n",
            "# Indice : proposez, evaluez avec preference secrete, acceptez/refusez\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(37, ex3b_md)
    nb["cells"].insert(38, ex3b_code)

    # ================================================================
    # Ex4: Fuite d'information → Exemple resolu (now cell 40)
    # ================================================================
    nb["cells"][40]["source"][0] = "# Exemple resolu : Mesure de la fuite d'information (ABT vs MinimalDisclosure)\n"
    nb["cells"][40]["outputs"] = []
    nb["cells"][40]["execution_count"] = None

    ex4b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 4b : Etude comparative de la vie privee dans DisCSP\n",
            "\n",
            "**Enonce** : Comparez 3 niveaux de protection de la vie privee sur un\n",
            "probleme de planification distribuee :\n",
            "\n",
            "1. **ABT standard** : aucune protection (baseline)\n",
            "2. **Partial Disclosure** : les agents ne revelent que les conflits\n",
            "3. **Minimal Disclosure** : les agents ne revelent que si une contrainte est violee\n",
            "\n",
            "Mesurez pour chaque approche :\n",
            "- Nombre de messages echanges\n",
            "- Quantite d'information revelee (nombre de valeurs exposees)\n",
            "- Temps de convergence\n",
            "\n",
            "**Consignes** :\n",
            "1. Utilisez `MinimalDisclosureAgent` de l'exemple comme reference\n",
            "2. Creez une variante `PartialDisclosureAgent` (entre ABT et MinimalDisclosure)\n",
            "3. Tracez un graphique comparatif des 3 approches\n",
        ],
    }

    ex4b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 4b : Etude comparative de la vie privee dans DisCSP\n",
            "\n",
            "# TODO: creez la classe PartialDisclosureAgent\n",
            "# Indice : entre ABTAgent (tout revele) et MinimalDisclosureAgent (rien ne revele)\n",
            "\n",
            "# TODO: executez les 3 approches sur le meme probleme\n",
            "# TODO: mesurez et comparez messages, informations revelees, convergence\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(41, ex4b_md)
    nb["cells"].insert(42, ex4b_code)

    # ================================================================
    # Write back
    # ================================================================
    with open(path, "w", encoding="utf-8") as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)

    print(f"CSP-9 updated: {len(nb['cells'])} cells (was 38, +8 new cells)")


if __name__ == "__main__":
    main()
