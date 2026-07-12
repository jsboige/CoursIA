"""
Recycle CSP-7-Soft exercises (Issue #463).

Converts 4 student solutions into labeled "Exemple resolu" cells
and creates new exercise stubs with variant data.
"""

import json


def main():
    path = "MyIA.AI.Notebooks/Search/Part2-CSP/CSP-7-Soft.ipynb"
    with open(path, encoding="utf-8") as f:
        nb = json.load(f)

    # --- Exercise layout (35 cells) ---
    # [26] md  : "## 7. Exercices" header with all enonces
    # [27] code: Ex1 Menu Planning Fuzzy (56L)
    # [28] code: Ex2 Weighted CSP Planification de voyage (87L)
    # [29] md  : Ex3 Nurse Scheduling equitable enonce
    # [30] code: Ex3 Nurse Scheduling equitable solution (89L)
    # [31] code: Ex3 Comparison baseline vs fairness (51L)
    # [32] code: Ex3 Visualization (26L)
    # [33] code: Ex4 Hierarchical CSP Configuration PC (163L)
    # [34] md  : References

    # ================================================================
    # Ex1: Menu Planning Fuzzy → Exemple resolu (cell 27)
    # ================================================================
    nb["cells"][27]["source"][0] = "# Exemple resolu : Menu Planning Fuzzy\n"
    nb["cells"][27]["outputs"] = []
    nb["cells"][27]["execution_count"] = None

    ex1b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 1b : Planification de repas avec preferences cuisine\n",
            "\n",
            "**Enonce** : Creez un Fuzzy CSP pour planifier les repas de la semaine\n",
            "en privilegiant un **equilibre nutritionnel** et des **preferences de cuisine**.\n",
            "\n",
            "Categories : 'Francais', 'Asiatique', 'Vegetarien', 'Fast-food', 'Mediterraneen'\n",
            "\n",
            "Preferences floues :\n",
            "- Budget : economique > milieu de semaine, cuisine chic le week-end\n",
            "- Nutrition : equilibre nutritionnel eleve (score fuzzy 0.8-1.0)\n",
            "- Diversite : penaliser la repetition d'une meme cuisine sur 2 jours consecutifs\n",
            "\n",
            "**Consignes** :\n",
            "1. Inspirez-vous du Menu Planning Fuzzy de l'exemple ci-dessus\n",
            "2. Utilisez la classe `SoftCSP` avec le `FuzzySemiring`\n",
            "3. Affichez le planning optimal avec les scores de satisfaction\n",
        ],
    }

    ex1b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 1b : Planification de repas avec preferences cuisine\n",
            "\n",
            "# TODO: definissez les jours, types de cuisine et preferences floues\n",
            "# JOURS = ['Lundi', 'Mardi', 'Mercredi', 'Jeudi', 'Vendredi', 'Samedi', 'Dimanche']\n",
            "# CUISINES = ['Francais', 'Asiatique', 'Vegetarien', 'Fast-food', 'Mediterraneen']\n",
            "\n",
            "# TODO: creez le SoftCSP avec FuzzySemiring\n",
            "# TODO: ajoutez les contraintes de budget, nutrition et diversite\n",
            "# Indice : la diversite peut etre modelisee comme neq sur 2 jours consecutifs\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(28, ex1b_md)
    nb["cells"].insert(29, ex1b_code)

    # ================================================================
    # Ex2: Weighted CSP → Exemple resolu (now cell 30)
    # ================================================================
    nb["cells"][30]["source"][0] = "# Exemple resolu : Weighted CSP - Planification de voyage\n"
    nb["cells"][30]["outputs"] = []
    nb["cells"][30]["execution_count"] = None

    ex2b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 2b : Planification de voyage avec budget contraint\n",
            "\n",
            "**Enonce** : Creez un Weighted CSP pour planifier un voyage de 5 jours\n",
            "avec un **budget total contraint** (le cout ne doit pas depasser un plafond).\n",
            "\n",
            "Donnees :\n",
            "- Destinations : 'Lyon', 'Marseille', 'Bordeaux', 'Toulouse', 'Nantes'\n",
            "- Budget max : 800 euros\n",
            "- Couts par destination : 150, 250, 180, 200, 120 euros/jour\n",
            "- Preferences : proximite geographique, interet touristique (score 0-10)\n",
            "\n",
            "**Consignes** :\n",
            "1. Inspirez-vous de la planification de voyage de l'exemple\n",
            "2. Utilisez le `WeightedSemiring` et ajoutez une contrainte dure de budget\n",
            "3. Affichez l'itineraire optimal avec le cout total et les scores de preference\n",
        ],
    }

    ex2b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 2b : Planification de voyage avec budget contraint\n",
            "\n",
            "# TODO: definissez les destinations, couts et preferences\n",
            "# DESTINATIONS = ['Lyon', 'Marseille', 'Bordeaux', 'Toulouse', 'Nantes']\n",
            "# COUTS = {'Lyon': 150, 'Marseille': 250, ...}\n",
            "\n",
            "# TODO: creez le WeightedCSP avec contrainte de budget\n",
            "# Indice : le budget est une contrainte DURE (pas souple)\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(31, ex2b_md)
    nb["cells"].insert(32, ex2b_code)

    # ================================================================
    # Ex3: Nurse Scheduling equitable → Exemple resolu (now cell 34)
    # Also cells [35] comparison, [36] visualization
    # ================================================================
    nb["cells"][34]["source"][0] = "# Exemple resolu : Nurse Scheduling equitable via min-max\n"
    nb["cells"][34]["outputs"] = []
    nb["cells"][34]["execution_count"] = None

    ex3b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 3b : Nurse Scheduling avec preferences personnelles\n",
            "\n",
            "**Enonce** : Adaptez le nurse scheduling pour integrer des **preferences\n",
            "personnelles** de chaque infirmier (jours de repos preferes, postes preferes).\n",
            "\n",
            "Preferences :\n",
            "- Infirmier 0 : prefere les matins, veut le week-end libre\n",
            "- Infirmier 1 : prefere les soirs, disponible tous les jours\n",
            "- Infirmier 2 : pas de preference de poste, veut le mercredi libre\n",
            "- Infirmier 3 : alterne matin/soir, veut le vendredi libre\n",
            "\n",
            "**Consignes** :\n",
            "1. Inspirez-vous de `solve_nurse_scheduling_fair` de l'exemple\n",
            "2. Ajoutez un poids `preference_penalty` pour chaque assignation non-prefered\n",
            "3. Minimisez le cout total = penalite d'equite + penalite de preferences\n",
        ],
    }

    ex3b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 3b : Nurse Scheduling avec preferences personnelles\n",
            "\n",
            "# TODO: definissez les preferences de chaque infirmier\n",
            "# preferences = {\n",
            "#     0: {'shift_pref': 'morning', 'days_off': [5, 6]},\n",
            "#     1: {'shift_pref': 'evening', 'days_off': []},\n",
            "#     ...\n",
            "# }\n",
            "\n",
            "# TODO: ajoutez les penalites de preference au modele CP-SAT\n",
            "# Indice : penalite = poids si assignation != preference\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(37, ex3b_md)
    nb["cells"].insert(38, ex3b_code)

    # ================================================================
    # Ex4: Hierarchical CSP → Exemple resolu (now cell 39)
    # ================================================================
    nb["cells"][39]["source"][0] = "# Exemple resolu : Hierarchical CSP - Configuration PC\n"
    nb["cells"][39]["outputs"] = []
    nb["cells"][39]["execution_count"] = None

    ex4b_md = {
        "cell_type": "markdown",
        "metadata": {},
        "source": [
            "### Exercice 4b : Configuration de station de travail avec budget\n",
            "\n",
            "**Enonce** : Adaptez le Hierarchical CSP pour configurer une **station de travail**\n",
            "(pas un PC gamer) avec un budget plus contraint de 1200 euros.\n",
            "\n",
            "Hierarchie des contraintes :\n",
            "- **Requis** : compatibilite CPU/motherboard, alimentation suffisante\n",
            "- **Important** : 16 Go RAM minimum, SSD de 500 Go minimum\n",
            "- **Souhaite** : carte graphique dediee, boitier silencieux\n",
            "\n",
            "**Consignes** :\n",
            "1. Inspirez-vous du Configuration PC de l'exemple ci-dessus\n",
            "2. Adaptez le catalogue de composants pour une station de travail\n",
            "3. Verifiez que la solution respecte le budget de 1200 euros\n",
        ],
    }

    ex4b_code = {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": [
            "# Exercice 4b : Configuration de station de travail avec budget\n",
            "\n",
            "# TODO: definissez un catalogue adapte (CPU pro, RAM ECC, etc.)\n",
            "# CATALOGUE = {\n",
            "#     'CPU': [...],\n",
            "#     'RAM': [...],\n",
            "#     'SSD': [...],\n",
            "#     'GPU': [...],\n",
            "#     'PSU': [...],\n",
            "#     'Case': [...],\n",
            "# }\n",
            "\n",
            "# TODO: modelisez les contraintes hierarchiques\n",
            "# Indice : les contraintes Requis doivent etre satisfaites obligatoirement\n",
            "\n",
            "# Votre code ici\n",
        ],
    }

    nb["cells"].insert(40, ex4b_md)
    nb["cells"].insert(41, ex4b_code)

    # ================================================================
    # Write back
    # ================================================================
    with open(path, "w", encoding="utf-8") as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)

    print(f"CSP-7 updated: {len(nb['cells'])} cells (was 35, +8 new cells)")


if __name__ == "__main__":
    main()
