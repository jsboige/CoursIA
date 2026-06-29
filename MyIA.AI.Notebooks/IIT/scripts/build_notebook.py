"""Build IIT-2-AdvancedTopics.ipynb programmatically."""
import json

cells = []

# Cell 0: Title + Navigation
cells.append({
    "cell_type": "markdown",
    "metadata": {},
    "source": [
        "# IIT - Sujets Avances : Partitionnement, Repertoires Cause-Effet et Reseaux Elargis\n",
        "\n",
        "## Navigation\n",
        "\n",
        "Ce notebook est le **deuxieme volet** de la serie IIT. Il approfondit les concepts introduits dans [IIT-1-IntroToPyPhi](IIT-1-IntroToPyPhi.ipynb).\n",
        "\n",
        "| Notebook | Contenu | Duree |\n",
        "|----------|---------|-------|\n",
        "| [1. IIT-1-IntroToPyPhi](IIT-1-IntroToPyPhi.ipynb) | Reseaux, Phi, CES, macro-subsystemes | 60-90 min |\n",
        "| **2. AdvancedTopics** (ce notebook) | Partitions MIP, repertoires, MICE, reseaux elargis | 60-90 min |\n",
        "\n",
        "**Prerequis** : avoir complete le notebook 1 (IIT-1-IntroToPyPhi).\n",
        "\n",
        "---\n",
        "\n",
        "## Plan de ce notebook\n",
        "\n",
        "1. **Rappels et configuration** - Reprise des concepts cles du notebook 1\n",
        "2. **Partitionnement et MIP** - Comment PyPhi cherche la coupe minimale d'information\n",
        "3. **Repertoires cause-effet** - Distributions de probabilites sur les causes et effets possibles\n",
        "4. **MICE et concepts** - Mechanismes maximalement irreductibles\n",
        "5. **Big Phi vs Small Phi** - Difference entre integration systeme et integration mecanisme\n",
        "6. **Reseaux elargis** - Systemes a 4+ noeuds et interpretation\n",
        "7. **Performance et coarse-graining** - Strategies pour traiter de grands systemes\n",
        "8. **Vers IIT 4.0** - Apercu des evolutions recentes de la theorie"
    ]
})

# Cell 1: Rappels
cells.append({
    "cell_type": "markdown", "metadata": {},
    "source": [
        "<a id=\"sec1\"></a>\n",
        "## 1. Rappels et configuration\n",
        "\n",
        "Dans le notebook precedent, nous avons vu :\n",
        "\n",
        "- **Reseau (Network)** : un ensemble de noeuds binaires connectes, decrit par une TPM\n",
        "- **Sous-systeme (Subsystem)** : un sous-ensemble de noeuds dans un etat donne\n",
        "- **Phi (big Phi, $\\Phi$)** : mesure de l'integration irreductible du systeme\n",
        "- **CES (Cause-Effect Structure)** : l'ensemble des concepts du systeme\n",
        "- **Concept** : un mecanisme avec son cause et son effet maximalement irreductibles\n",
        "\n",
        "Reprenons avec notre reseau XOR et configurons PyPhi."
    ]
})

# Cell 2: Imports
cells.append({
    "cell_type": "code", "execution_count": None, "metadata": {}, "outputs": [],
    "source": [
        "import os\n",
        "os.environ['PYPHI_WELCOME_OFF'] = 'yes'\n",
        "\n",
        "import pyphi\n",
        "import numpy as np\n",
        "\n",
        "pyphi.config.VALIDATE_SUBSYSTEM_STATES = False\n",
        "\n",
        "print(\"PyPhi version:\", pyphi.__version__)\n",
        "print(\"Configuration prete.\")"
    ]
})

# Cell 3: XOR setup
cells.append({
    "cell_type": "code", "execution_count": None, "metadata": {}, "outputs": [],
    "source": [
        "# Creation du reseau XOR (3 noeuds) - identique au notebook 1\n",
        "network = pyphi.examples.xor_network()\n",
        "state = (0, 0, 0)\n",
        "subsystem = pyphi.Subsystem(network, state)\n",
        "\n",
        "print(\"Reseau XOR : 3 noeuds (A, B, C)\")\n",
        "print(\"Etat initial :\", state)\n",
        "print(\"Noeuds du sous-systeme :\", subsystem.node_indices)\n",
        "print(\"Connectivite (CM) :\")\n",
        "print(network.cm)"
    ]
})

# Cell 4: Section 2 header
cells.append({
    "cell_type": "markdown", "metadata": {},
    "source": [
        "<a id=\"sec2\"></a>\n",
        "## 2. Partitionnement et MIP (Minimum Information Partition)\n",
        "\n",
        "Le coeur du calcul de $\\Phi$ repose sur la recherche de la **partition minimale d'information (MIP)**. La MIP est la facon de couper le systeme en deux qui **detruit le moins d'information**. Si cette coupe minimale detruit beaucoup d'information, c'est que le systeme est fortement integre.\n",
        "\n",
        "### 2.1. Types de partitions\n",
        "\n",
        "PyPhi supporte plusieurs types de partitions :\n",
        "- **Bipartition** : couper le systeme en 2 parties\n",
        "- **Tripartition** : couper en 3 parties\n",
        "- **K-partition** : couper en K parties\n",
        "\n",
        "Pour chaque partition, on mesure l'information detruite par la coupe. La MIP est celle qui minimise cette perte."
    ]
})

# Cell 5: SIA computation
cells.append({
    "cell_type": "code", "execution_count": None, "metadata": {}, "outputs": [],
    "source": [
        "# Calculer l'analyse d'irreductibilite du systeme (SIA)\n",
        "sia = pyphi.compute.sia(subsystem)\n",
        "\n",
        "print(\"=== System Irreducibility Analysis (SIA) ===\")\n",
        "print(f\"Big Phi: {sia.phi}\")\n",
        "print(f\"Coupe (MIP): {sia.cut}\")\n",
        "print(f\"Partie from: {sia.cut.from_nodes}\")\n",
        "print(f\"Partie to: {sia.cut.to_nodes}\")"
    ]
})

# Cell 6: MIP interpretation
cells.append({
    "cell_type": "markdown", "metadata": {},
    "source": [
        "### 2.2. Interpretation de la MIP\n",
        "\n",
        "La MIP nous dit **ou le systeme est le plus faiblement integre**. Dans notre reseau XOR :\n",
        "\n",
        "- Si la coupe separe les noeuds {A, B} de {C}, cela signifie que le lien A,B -> C est le plus faible\n",
        "- Plus $\\Phi$ est eleve, plus le systeme est irreductiblement integre\n",
        "- Un $\\Phi = 0$ signifie que le systeme est completement decomposable (pas d'integration)\n",
        "\n",
        "### 2.3. Complexite du partitionnement\n",
        "\n",
        "Le nombre de partitions possibles croit exponentiellement avec la taille du systeme (nombre de Bell). C'est pourquoi le calcul exact de $\\Phi$ est **intractable** pour de grands reseaux."
    ]
})

# Cell 7: Bipartitions
cells.append({
    "cell_type": "code", "execution_count": None, "metadata": {}, "outputs": [],
    "source": [
        "# Enumerer toutes les bipartitions possibles du sous-systeme\n",
        "from pyphi.partition import bipartition\n",
        "\n",
        "nodes = subsystem.node_indices\n",
        "all_biparts = list(bipartition(nodes))\n",
        "print(f\"Nombre de bipartitions pour {len(nodes)} noeuds : {len(all_biparts)}\")\n",
        "print(\"\\nBipartitions possibles :\")\n",
        "for i, bp in enumerate(all_biparts):\n",
        "    print(f\"  {i+1}. {bp[0]} | {bp[1]}\")\n",
        "\n",
        "# Nombre de Bell pour les 6 premiers entiers\n",
        "bell = [1, 1, 2, 5, 15, 52, 203]\n",
        "print(f\"\\nNombres de Bell (nombre total de partitions):\")\n",
        "for n in range(len(bell)):\n",
        "    print(f\"  {n} noeuds -> {bell[n]} partitions\")"
    ]
})

# Cell 8: Section 3 header
cells.append({
    "cell_type": "markdown", "metadata": {},
    "source": [
        "<a id=\"sec3\"></a>\n",
        "## 3. Repertoires cause-effet\n",
        "\n",
        "Les **repertoires cause et effet** sont les distributions de probabilite qui decrivent comment un mecanisme contraint les etats passes (cause) et futurs (effet) d'un purview.\n",
        "\n",
        "### 3.1. Repertoire cause\n",
        "\n",
        "Le repertoire cause repond a la question : etant donne le mecanisme dans son etat actuel, quelles sont les probabilites des etats anterieurs possibles du purview ?"
    ]
})

# Cell 9: Cause repertoire
cells.append({
    "cell_type": "code", "execution_count": None, "metadata": {}, "outputs": [],
    "source": [
        "# Calculer le repertoire cause pour le mecanisme {A, B} et le purview {A}\n",
        "mechanism = (0, 1)\n",
        "purview = (0,)\n",
        "\n",
        "cause_rep = subsystem.cause_repertoire(mechanism, purview)\n",
        "print(f\"Repertoire cause pour mecanisme {mechanism} -> purview {purview}:\")\n",
        "print(f\"  Shape: {cause_rep.shape}\")\n",
        "print(f\"  Valeurs: {cause_rep.flatten()}\")\n",
        "print(f\"  Somme: {cause_rep.sum():.4f} (doit etre 1.0)\")"
    ]
})

# Cell 10: Effect repertoire
cells.append({
    "cell_type": "code", "execution_count": None, "metadata": {}, "outputs": [],
    "source": [
        "# Calculer le repertoire effet pour le meme mecanisme\n",
        "effect_rep = subsystem.effect_repertoire(mechanism, purview)\n",
        "print(f\"Repertoire effet pour mecanisme {mechanism} -> purview {purview}:\")\n",
        "print(f\"  Shape: {effect_rep.shape}\")\n",
        "print(f\"  Valeurs: {effect_rep.flatten()}\")\n",
        "print(f\"  Somme: {effect_rep.sum():.4f} (doit etre 1.0)\")\n",
        "\n",
        "print(\"\\nComparaison cause vs effet:\")\n",
        "for i, label in enumerate(['A=0', 'A=1']):\n",
        "    c_val = cause_rep.flatten()[i]\n",
        "    e_val = effect_rep.flatten()[i]\n",
        "    print(f\"  {label}: cause={c_val:.3f}, effet={e_val:.3f}\")"
    ]
})

# Cell 11: Unconstrained header
cells.append({
    "cell_type": "markdown", "metadata": {},
    "source": [
        "### 3.2. Repertoire non-perturbe (unconstrained)\n",
        "\n",
        "Le repertoire **non-perturbe** est la distribution uniforme - ce qu'on attendrait sans aucune contrainte. La difference entre le repertoire contraint et le repertoire non-perturbe mesure **l'information specifiee** par le mecanisme."
    ]
})

# Cell 12: Unconstrained + EMD
cells.append({
    "cell_type": "code", "execution_count": None, "metadata": {}, "outputs": [],
    "source": [
        "# Repertoire non-perturbe (uniforme)\n",
        "unconstrained = subsystem.unconstrained_cause_repertoire(purview)\n",
        "print(f\"Repertoire non-perturbe pour purview {purview}:\")\n",
        "print(f\"  Valeurs: {unconstrained.flatten()}\")\n",
        "\n",
        "from pyphi.distance import hamming_emd\n",
        "distance = hamming_emd(cause_rep, unconstrained)\n",
        "print(f\"\\nDistance EMD (cause contrainte vs non-perturbe): {distance:.4f}\")\n",
        "print(\"Cette valeur mesure l'information cause specifiee par le mecanisme.\")"
    ]
})

# Cell 13: Exercise 1 header
cells.append({
    "cell_type": "markdown", "metadata": {},
    "source": [
        "### Exercice 1 : Explorer les repertoires d'un mecanisme different\n",
        "\n",
        "Calculez les repertoires cause et effet pour le mecanisme `{A, C}` (noeuds 0 et 2) avec le purview `{B, C}` (noeuds 1 et 2).\n",
        "\n",
        "**Objectifs** :\n",
        "1. Calculer le repertoire cause et le repertoire effet\n",
        "2. Verifier que chaque repertoire somme a 1.0\n",
        "3. Identifier quel etat du purview est le plus probable en cause et en effet\n",
        "\n",
        "**Indices** :\n",
        "- Utilisez `subsystem.cause_repertoire(mechanism, purview)` et `subsystem.effect_repertoire(mechanism, purview)`\n",
        "- Les noeuds sont indices par des tuples d'entiers : `(0, 2)` pour {A, C}\n",
        "- Pour identifier l'etat le plus probable, utilisez `np.argmax(rep.flatten())`"
    ]
})

# Cell 14: Exercise 1 code
cells.append({
    "cell_type": "code", "execution_count": None, "metadata": {}, "outputs": [],
    "source": [
        "# Exercice 1 : Repertoires cause-effet pour le mecanisme {A, C} et purview {B, C}\n",
        "# TODO etudiant : remplacez les valeurs None par votre code\n",
        "\n",
        "mechanism_ex1 = None  # TODO : definir le mecanisme {A, C}\n",
        "purview_ex1 = None    # TODO : definir le purview {B, C}\n",
        "\n",
        "if mechanism_ex1 is not None and purview_ex1 is not None:\n",
        "    cause_rep_ex1 = subsystem.cause_repertoire(mechanism_ex1, purview_ex1)\n",
        "    effect_rep_ex1 = subsystem.effect_repertoire(mechanism_ex1, purview_ex1)\n",
        "    \n",
        "    print(f\"Repertoire cause: {cause_rep_ex1.flatten()}\")\n",
        "    print(f\"Somme cause: {cause_rep_ex1.sum():.4f}\")\n",
        "    print(f\"Etat le plus probable (cause): {np.argmax(cause_rep_ex1.flatten())}\")\n",
        "    print(f\"\\nRepertoire effet: {effect_rep_ex1.flatten()}\")\n",
        "    print(f\"Somme effet: {effect_rep_ex1.sum():.4f}\")\n",
        "    print(f\"Etat le plus probable (effet): {np.argmax(effect_rep_ex1.flatten())}\")\n",
        "else:\n",
        "    print(\"Exercice a completer : definissez mechanism_ex1 et purview_ex1\")"
    ]
})

# Cell 15: Section 4 header
cells.append({
    "cell_type": "markdown", "metadata": {},
    "source": [
        "<a id=\"sec4\"></a>\n",
        "## 4. MICE et Concepts\n",
        "\n",
        "Un **MICE** (Maximally Irreducible Cause or Effect) est un couple (mecanisme, purview) qui maximise l'information irreductible. Un **concept** est forme d'un MICE cause et d'un MICE effet pour le meme mecanisme.\n",
        "\n",
        "### 4.1. Trouver le MICE pour un mecanisme"
    ]
})

# Cell 16: MICE computation
cells.append({
    "cell_type": "code", "execution_count": None, "metadata": {}, "outputs": [],
    "source": [
        "# Trouver le MICE (cause et effet) pour le mecanisme {A, B}\n",
        "mechanism = (0, 1)\n",
        "\n",
        "mice_cause = subsystem.find_mice(pyphi.Direction.CAUSE, mechanism)\n",
        "mice_effect = subsystem.find_mice(pyphi.Direction.EFFECT, mechanism)\n",
        "\n",
        "print(\"=== MICE pour le mecanisme {A, B} ===\")\n",
        "print(\"\\nMICE Cause:\")\n",
        "print(f\"  Purview: {mice_cause.purview}\")\n",
        "print(f\"  Phi (small): {mice_cause.phi}\")\n",
        "print(f\"  Direction: {mice_cause.direction}\")\n",
        "print(\"\\nMICE Effet:\")\n",
        "print(f\"  Purview: {mice_effect.purview}\")\n",
        "print(f\"  Phi (small): {mice_effect.phi}\")\n",
        "print(f\"  Direction: {mice_effect.direction}\")"
    ]
})

# Cell 17: CES details
cells.append({
    "cell_type": "code", "execution_count": None, "metadata": {}, "outputs": [],
    "source": [
        "# Construire les concepts a partir de la CES\n",
        "ces = pyphi.compute.ces(subsystem)\n",
        "print(f\"Nombre total de concepts dans la CES: {len(ces)}\")\n",
        "print(\"\\nDetails de chaque concept :\")\n",
        "for i, concept in enumerate(ces):\n",
        "    print(f\"\\n  Concept {i+1}:\")\n",
        "    print(f\"    Mecanisme: {concept.mechanism}\")\n",
        "    if concept.cause:\n",
        "        print(f\"    Cause purview: {concept.cause.purview}, phi={concept.cause.phi:.4f}\")\n",
        "    if concept.effect:\n",
        "        print(f\"    Effet purview: {concept.effect.purview}, phi={concept.effect.phi:.4f}\")\n",
        "    print(f\"    Phi du concept: {concept.phi:.4f}\")"
    ]
})

# Cell 18: MICE interpretation
cells.append({
    "cell_type": "markdown", "metadata": {},
    "source": [
        "### 4.2. Interpretation des MICE\n",
        "\n",
        "Chaque concept decrit une **unite d'information cause-effet** :\n",
        "- Le **mecanisme** est l'ensemble de noeuds qui specifie de l'information\n",
        "- Le **purview cause** est l'ensemble de noeuds dont le mecanisme contraint les etats passes\n",
        "- Le **purview effet** est l'ensemble de noeuds dont le mecanisme contraint les etats futurs\n",
        "- Le **small phi** ($\\varphi$) mesure la quantite d'information irreductible du concept\n",
        "\n",
        "Un concept avec $\\varphi > 0$ existe dans la CES du systeme. La somme de tous les $\\varphi$ des concepts ne donne PAS le big $\\Phi$."
    ]
})

# Cell 19: Section 5 header
cells.append({
    "cell_type": "markdown", "metadata": {},
    "source": [
        "<a id=\"sec5\"></a>\n",
        "## 5. Big Phi vs Small Phi\n",
        "\n",
        "La distinction entre **big Phi** ($\\Phi$) et **small phi** ($\\varphi$) est fondamentale :\n",
        "\n",
        "| | Big Phi ($\\Phi$) | Small phi ($\\varphi$) |\n",
        "|---|---|---|\n",
        "| **Niveau** | Systeme entier | Mecanisme individuel |\n",
        "| **Mesure** | Integration irreductible du systeme | Information irreductible d'un concept |\n",
        "| **Question** | Le systeme est-il integre ? | Ce mecanisme specifie-t-il de l'information ? |\n",
        "| **Calcul** | SIA sur toutes les partitions | EMD entre repertoire contraint et partitionne |"
    ]
})

# Cell 20: Big vs Small Phi code
cells.append({
    "cell_type": "code", "execution_count": None, "metadata": {}, "outputs": [],
    "source": [
        "# Comparaison Big Phi vs Small Phi\n",
        "print(\"=== Big Phi (niveau systeme) ===\")\n",
        "print(f\"  Phi du systeme (SIA): {sia.phi:.4f}\")\n",
        "print(f\"  Coupe minimale: {sia.cut}\")\n",
        "\n",
        "print(\"\\n=== Small Phi (niveau concept) ===\")\n",
        "total_small_phi = sum(c.phi for c in ces)\n",
        "print(f\"  Nombre de concepts: {len(ces)}\")\n",
        "print(f\"  Somme des small phi: {total_small_phi:.4f}\")\n",
        "for i, c in enumerate(ces):\n",
        "    print(f\"    Concept {i+1}: mecanisme={c.mechanism}, phi={c.phi:.4f}\")\n",
        "\n",
        "print(f\"\\nBig Phi ({sia.phi:.4f}) != somme des small phi ({total_small_phi:.4f})\")\n",
        "print(\"Ce sont deux mesures differentes a des niveaux differents.\")"
    ]
})

# Cell 21: Exercise 2 header
cells.append({
    "cell_type": "markdown", "metadata": {},
    "source": [
        "### Exercice 2 : Comparer Phi pour deux etats du reseau\n",
        "\n",
        "Calculez le big Phi et la CES pour le reseau XOR dans l'etat `(1, 1, 1)` et comparez avec l'etat `(0, 0, 0)`.\n",
        "\n",
        "**Objectifs** :\n",
        "1. Creer un nouveau sous-systeme pour l'etat `(1, 1, 1)`\n",
        "2. Calculer le SIA (big Phi) et la CES (concepts)\n",
        "3. Comparer les resultats avec l'etat `(0, 0, 0)`\n",
        "\n",
        "**Indices** :\n",
        "- `pyphi.Subsystem(network, state)` pour creer le sous-systeme\n",
        "- `pyphi.compute.sia(subsystem)` pour le big Phi\n",
        "- `pyphi.compute.ces(subsystem)` pour les concepts"
    ]
})

# Cell 22: Exercise 2 code
cells.append({
    "cell_type": "code", "execution_count": None, "metadata": {}, "outputs": [],
    "source": [
        "# Exercice 2 : Comparer Phi pour deux etats\n",
        "# TODO etudiant : remplacez les valeurs None par votre code\n",
        "\n",
        "state_2 = None  # TODO : definir l'etat (1, 1, 1)\n",
        "\n",
        "if state_2 is not None:\n",
        "    subsystem_2 = pyphi.Subsystem(network, state_2)\n",
        "    sia_2 = pyphi.compute.sia(subsystem_2)\n",
        "    ces_2 = pyphi.compute.ces(subsystem_2)\n",
        "    \n",
        "    print(f\"Etat {state}: Big Phi = {sia.phi:.4f}, Concepts = {len(ces)}\")\n",
        "    print(f\"Etat {state_2}: Big Phi = {sia_2.phi:.4f}, Concepts = {len(ces_2)}\")\n",
        "    print(f\"\\nDifference Big Phi: {abs(sia.phi - sia_2.phi):.4f}\")\n",
        "else:\n",
        "    print(\"Exercice a completer : definissez state_2 = (1, 1, 1)\")"
    ]
})

# Cell 23: Section 6 header
cells.append({
    "cell_type": "markdown", "metadata": {},
    "source": [
        "<a id=\"sec6\"></a>\n",
        "## 6. Reseaux elargis : systemes a 4+ noeuds\n",
        "\n",
        "Explorons un systeme plus grand pour observer comment la complexite de la CES evolue.\n",
        "\n",
        "### 6.1. Reseau XOR cyclique (4 noeuds)\n",
        "\n",
        "Nous construisons un reseau a 4 noeuds en anneau ou chaque noeud depend de lui-meme et de son voisin de gauche via XOR."
    ]
})

# Cell 24: 4-node network
cells.append({
    "cell_type": "code", "execution_count": None, "metadata": {}, "outputs": [],
    "source": [
        "# Reseau 4 noeuds en anneau - chaque noeud depend de lui-meme et de son voisin\n",
        "tpm_4 = np.zeros((16, 4))\n",
        "for i in range(16):\n",
        "    bits = [(i >> j) & 1 for j in range(3, -1, -1)]\n",
        "    a_next = bits[3] ^ bits[0]  # D XOR A\n",
        "    b_next = bits[0] ^ bits[1]  # A XOR B\n",
        "    c_next = bits[1] ^ bits[2]  # B XOR C\n",
        "    d_next = bits[2] ^ bits[3]  # C XOR D\n",
        "    tpm_4[i] = [a_next, b_next, c_next, d_next]\n",
        "\n",
        "cm_4 = np.array([\n",
        "    [1, 1, 0, 1],\n",
        "    [1, 1, 1, 0],\n",
        "    [0, 1, 1, 1],\n",
        "    [1, 0, 1, 1],\n",
        "])\n",
        "\n",
        "labels_4 = ('A', 'B', 'C', 'D')\n",
        "net_4 = pyphi.Network(tpm_4, cm_4, node_labels=labels_4)\n",
        "\n",
        "print(\"Reseau 4 noeuds en anneau (XOR cyclique)\")\n",
        "print(\"Labels:\", labels_4)\n",
        "print(\"Connectivite:\")\n",
        "print(cm_4)"
    ]
})

# Cell 25: 4-node analysis
cells.append({
    "cell_type": "code", "execution_count": None, "metadata": {}, "outputs": [],
    "source": [
        "# Analyser le reseau 4 noeuds\n",
        "state_4 = (0, 0, 0, 0)\n",
        "sub_4 = pyphi.Subsystem(net_4, state_4)\n",
        "\n",
        "print(f\"Sous-systeme 4 noeuds, etat {state_4}\")\n",
        "print(f\"Noeuds: {sub_4.node_indices}\")\n",
        "\n",
        "ces_4 = pyphi.compute.ces(sub_4)\n",
        "print(f\"\\nNombre de concepts: {len(ces_4)}\")\n",
        "for i, c in enumerate(ces_4):\n",
        "    cause_p = c.cause.purview if c.cause else None\n",
        "    effect_p = c.effect.purview if c.effect else None\n",
        "    print(f\"  Concept {i+1}: mech={c.mechanism}, cause_p={cause_p}, \"\n",
        "          f\"effect_p={effect_p}, phi={c.phi:.4f}\")"
    ]
})

# Cell 26: 4-node big Phi
cells.append({
    "cell_type": "code", "execution_count": None, "metadata": {}, "outputs": [],
    "source": [
        "# Big Phi pour le reseau 4 noeuds\n",
        "sia_4 = pyphi.compute.sia(sub_4)\n",
        "print(f\"Big Phi (4 noeuds): {sia_4.phi:.4f}\")\n",
        "print(f\"Coupe MIP: {sia_4.cut}\")\n",
        "print(f\"\\nComparaison:\")\n",
        "print(f\"  3 noeuds (XOR): Big Phi = {sia.phi:.4f}\")\n",
        "print(f\"  4 noeuds (anneau): Big Phi = {sia_4.phi:.4f}\")"
    ]
})

# Cell 27: Interpretation
cells.append({
    "cell_type": "markdown", "metadata": {},
    "source": [
        "### 6.2. Interpreter les resultats\n",
        "\n",
        "Quelques observations importantes :\n",
        "\n",
        "1. **Plus de noeuds ne signifie pas plus de Phi** : la valeur de $\\Phi$ depend de la structure causale, pas de la taille\n",
        "2. **Les reseaux feed-forward ont Phi = 0** : pas de boucle causale = pas d'integration\n",
        "3. **Les reseaux recurrents** (comme notre anneau) peuvent avoir Phi > 0\n",
        "4. **La symetrie** de la connectivite influence la distribution des concepts"
    ]
})

# Cell 28: Section 7 header
cells.append({
    "cell_type": "markdown", "metadata": {},
    "source": [
        "<a id=\"sec7\"></a>\n",
        "## 7. Performance et coarse-graining\n",
        "\n",
        "Le calcul exact de $\\Phi$ croit de maniere **super-exponentielle** avec la taille du reseau. Pour des reseaux de plus de ~6-8 noeuds, le calcul devient intractable.\n",
        "\n",
        "### 7.1. Strategies de gestion de la complexite\n",
        "\n",
        "| Strategie | Principe | Utilite |\n",
        "|-----------|----------|----------|\n",
        "| **Coarse-graining** | Grouper les noeuds en macro-noeuds | Reduire la dimensionnalite |\n",
        "| **Blackboxing** | Ignorer certains noeuds | Se concentrer sur les noeuds pertinents |\n",
        "| **Parallelisation** | Repartir les calculs | Accelerer sur multi-coeur |\n",
        "| **Caching** | Stocker les resultats intermediaires | Eviter les recalculs |"
    ]
})

# Cell 29: Macro module
cells.append({
    "cell_type": "code", "execution_count": None, "metadata": {}, "outputs": [],
    "source": [
        "# Demonstration du module macro\n",
        "print(\"=== Module pyphi.macro ===\")\n",
        "print(\"Le module macro offre des outils pour le coarse-graining et blackboxing.\")\n",
        "print(\"\\nFonctions disponibles:\")\n",
        "macro_funcs = [f for f in dir(pyphi.macro) if not f.startswith('_')]\n",
        "for f in macro_funcs[:12]:\n",
        "    print(f\"  - {f}\")"
    ]
})

# Cell 30: Timing
cells.append({
    "cell_type": "code", "execution_count": None, "metadata": {}, "outputs": [],
    "source": [
        "# Mesurer le temps de calcul pour differentes tailles\n",
        "import time\n",
        "\n",
        "def time_phi_calc(network, state, label=\"\"):\n",
        "    \"\"\"Mesure le temps de calcul de la CES pour un sous-systeme.\"\"\"\n",
        "    sub = pyphi.Subsystem(network, state)\n",
        "    t0 = time.time()\n",
        "    ces_result = pyphi.compute.ces(sub)\n",
        "    elapsed = time.time() - t0\n",
        "    print(f\"  {label}: {len(ces_result)} concepts, {elapsed:.2f}s\")\n",
        "    return elapsed\n",
        "\n",
        "print(\"Temps de calcul CES par taille de reseau:\")\n",
        "t3 = time_phi_calc(network, (0,0,0), \"3 noeuds (XOR)\")\n",
        "t4 = time_phi_calc(net_4, (0,0,0,0), \"4 noeuds (anneau)\")\n",
        "\n",
        "if t3 > 0:\n",
        "    print(f\"\\nRatio 4noeuds/3noeuds: {t4/t3:.1f}x\")\n",
        "    print(\"La croissance est super-lineaire.\")"
    ]
})

# Cell 31: Neuroscience implications
cells.append({
    "cell_type": "markdown", "metadata": {},
    "source": [
        "### 7.2. Implications pour la recherche en neuroscience\n",
        "\n",
        "Cette complexite computationnelle a des implications directes :\n",
        "\n",
        "- Le **cerveau humain** (~86 milliards de neurones) ne peut pas etre analyse avec le calcul exact\n",
        "- Les **approximations** (coarse-graining, echantillonnage) sont necessaires\n",
        "- Le **Perturbational Complexity Index (PCI)** est une approximation clinique inspiree de $\\Phi$\n",
        "- Le debat entre **exactitude mathematique** et **applicabilite pratique** est central"
    ]
})

# Cell 32: Section 8 header
cells.append({
    "cell_type": "markdown", "metadata": {},
    "source": [
        "<a id=\"sec8\"></a>\n",
        "## 8. Vers IIT 4.0\n",
        "\n",
        "### 8.1. D'IIT 3.0 a IIT 4.0\n",
        "\n",
        "| Aspect | IIT 3.0 (PyPhi) | IIT 4.0 (2024+) |\n",
        "|--------|-----------------|------------------|\n",
        "| **Identite** | Le complexe maximise $\\Phi$ | Le systeme EST sa structure cause-effet |\n",
        "| **Existence intrinseque** | Via les concepts | Axiome fondamental |\n",
        "| **Coupes** | Bipartitions | Coupes directionnelles |\n",
        "| **Extension** | Potentiel a Phi maximal | Ensemble des systemes qui existent |"
    ]
})

# Cell 33: Concept-style
cells.append({
    "cell_type": "code", "execution_count": None, "metadata": {}, "outputs": [],
    "source": [
        "# Apercu : le concept-style (vers IIT 4.0)\n",
        "try:\n",
        "    cs_sia = pyphi.compute.sia_concept_style(subsystem)\n",
        "    print(\"=== Concept-Style SIA (vers IIT 4.0) ===\")\n",
        "    print(f\"Phi (concept-style): {cs_sia.phi:.4f}\")\n",
        "    print(f\"Phi (classique 3.0): {sia.phi:.4f}\")\n",
        "    diff = abs(cs_sia.phi - sia.phi)\n",
        "    print(f\"Difference: {diff:.4f}\")\n",
        "    print(\"Le concept-style utilise un schema de partition different.\")\n",
        "except Exception as e:\n",
        "    print(f\"Concept-style non disponible: {e}\")"
    ]
})

# Cell 34: Exercise 3 header
cells.append({
    "cell_type": "markdown", "metadata": {},
    "source": [
        "### Exercice 3 : Explorer un reseau feed-forward\n",
        "\n",
        "Construisez un reseau feed-forward a 3 noeuds (A -> B -> C) et verifiez que son big Phi est egal a 0.\n",
        "\n",
        "**Objectifs** :\n",
        "1. Creer la TPM d'un reseau ou A influence B et B influence C (pas de boucle)\n",
        "2. Creer le reseau PyPhi avec la connectivite appropriee\n",
        "3. Calculer le big Phi et verifier qu'il vaut 0\n",
        "\n",
        "**Indices** :\n",
        "- La matrice de connectivite est triangulaire : `[[0,1,0], [0,0,1], [0,0,0]]`\n",
        "- Pour la TPM : B_next = A, C_next = B, A_next = A (ou une constante)\n",
        "- Utilisez `pyphi.compute.sia(subsystem)` pour calculer big Phi"
    ]
})

# Cell 35: Exercise 3 code
cells.append({
    "cell_type": "code", "execution_count": None, "metadata": {}, "outputs": [],
    "source": [
        "# Exercice 3 : Reseau feed-forward (Phi attendu = 0)\n",
        "# TODO etudiant : construisez le reseau et verifiez Phi = 0\n",
        "\n",
        "# Etape 1 : Definir la TPM (8 etats -> 3 noeuds)\n",
        "tpm_ff = None  # TODO : construire la TPM du reseau feed-forward\n",
        "\n",
        "# Etape 2 : Matrice de connectivite\n",
        "cm_ff = None   # TODO : A->B, B->C (pas de connexion C->A)\n",
        "\n",
        "if tpm_ff is not None and cm_ff is not None:\n",
        "    net_ff = pyphi.Network(tpm_ff, cm_ff)\n",
        "    sub_ff = pyphi.Subsystem(net_ff, (0, 0, 0))\n",
        "    sia_ff = pyphi.compute.sia(sub_ff)\n",
        "    print(f\"Big Phi du reseau feed-forward: {sia_ff.phi:.4f}\")\n",
        "    print(f\"Phi = 0 confirme: {sia_ff.phi == 0.0}\")\n",
        "    print(\"Un reseau sans boucle causale n'a pas d'integration.\")\n",
        "else:\n",
        "    print(\"Exercice a completer : definissez tpm_ff et cm_ff\")"
    ]
})

# Cell 36: Debates
cells.append({
    "cell_type": "markdown", "metadata": {},
    "source": [
        "### 8.2. Limites et debats\n",
        "\n",
        "L'IIT est une theorie active et debattue :\n",
        "\n",
        "- **Lettre ouverte de 2023** : ~120 signataires qualifiant l'IIT de pseudoscience\n",
        "- **Reponse des partisans** : l'IIT fait des predictions falsifiables (PCI, activations)\n",
        "- **Programme Templeton** : tests adversariaux IIT vs Global Workspace Theory\n",
        "- **Enjeu IA** : l'IIT predit que les reseaux feed-forward (comme les LLMs) ont $\\Phi = 0$\n",
        "\n",
        "Ces debats illustrent la tension entre **rigueur mathematique** et **applicabilite empirique**."
    ]
})

# Cell 37: Conclusion
cells.append({
    "cell_type": "markdown", "metadata": {},
    "source": [
        "---\n",
        "\n",
        "## Bilan et perspectives\n",
        "\n",
        "Dans ce deuxieme notebook, nous avons approfondi :\n",
        "\n",
        "1. **Le partitionnement MIP** - la recherche de la coupe minimale d'information\n",
        "2. **Les repertoires cause-effet** - les distributions de probabilite au coeur de l'analyse IIT\n",
        "3. **Les MICE et concepts** - les unites d'information irreductible dans la CES\n",
        "4. **Big Phi vs Small Phi** - deux niveaux de mesure complementaires\n",
        "5. **Les reseaux elargis** - comment la complexite croit avec la taille du systeme\n",
        "6. **Le coarse-graining** - strategies pour gerer l'intractabilite du calcul\n",
        "7. **IIT 4.0** - les evolutions recentes de la theorie\n",
        "\n",
        "### Pour aller plus loin\n",
        "\n",
        "- **Documentation PyPhi** : [pyphi.readthedocs.io](https://pyphi.readthedocs.io/en/stable/)\n",
        "- **Article fondateur** : Oizumi, Albantakis, Tononi (2014). *From the Phenomenology to the Mechanisms of Consciousness*\n",
        "- **IIT 4.0** : Albantakis et al. (2023). *Integrated information theory (IIT) 4.0*\n",
        "- **Series connexes** : [Probas](../Probas/README.md), [GameTheory](../GameTheory/README.md)"
    ]
})

# Build notebook
nb = {
    "cells": cells,
    "metadata": {
        "kernelspec": {
            "display_name": "Python 3 (PyPhi/IIT)",
            "language": "python",
            "name": "pyphi"
        },
        "language_info": {
            "codemirror_mode": {"name": "ipython", "version": 3},
            "file_extension": ".py",
            "mimetype": "text/x-python",
            "name": "python",
            "nbformat_minor": 4,
            "version": "3.9.25"
        }
    },
    "nbformat": 4,
    "nbformat_minor": 4
}

outpath = "MyIA.AI.Notebooks/IIT/IIT-2-AdvancedTopics.ipynb"
with open(outpath, "w", encoding="utf-8") as f:
    json.dump(nb, f, indent=1, ensure_ascii=False)

# Verify
json.load(open(outpath, "r", encoding="utf-8"))
code_cells = sum(1 for c in cells if c["cell_type"] == "code")
md_cells = sum(1 for c in cells if c["cell_type"] == "markdown")
print(f"Notebook OK: {len(cells)} cells ({code_cells} code, {md_cells} markdown)")
