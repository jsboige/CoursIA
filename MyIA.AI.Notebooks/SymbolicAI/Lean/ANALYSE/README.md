# ANALYSE — formalisations d'analyse, digérées

Sous-série de la série [Lean](../README.md) (décision de gradation #17545, 24/09) : les formalisations de recherche en analyse — Sendov, *Analysis I* de Tao, PFR, KLS — descendent ici avec un arc interne **Licence → Recherche** : chaque carnet part d'un énoncé lisible et finit sur le lac réel cité par ses déclarations.

La série principale garde son tutoriel (numéros 1 à 14) ; le présent dossier porte l'arc d'analyse. Les numéros de la table ci-dessous renvoient à l'ancien identifiant de série (`Lean-18` → `ANALYSE-01`, etc. — table de correspondance dans `docs/reference/rename-ledger.tsv`).

**Escalier depuis la série principale** : [Lean-20 — Capstone](../Lean-20-Capstone-Digestions-Tao-Python.ipynb) présente la sous-série, en fait monter une première marche (règle de chaîne et distance de Ruzsa sur F₂³) et en mesure la surface.

| Carnet | Contenu | Durée |
|---|---|---|
| [ANALYSE-01-Sendov-Lean-Python](ANALYSE-01-Sendov-Lean-Python.ipynb) | La conjecture de Sendov (preuve L. Mazur 2026, digestion et formalisation T. Tao) : pour un polynôme dont tous les zéros sont dans le disque unité, chaque zéro a un point critique à distance ≤ 1 — énoncé, illustrations numériques des cas, contexte de la preuve | 45 min |
| [ANALYSE-02-Tao-Lean-Python](ANALYSE-02-Tao-Lean-Python.ipynb) | Le manuel *Analysis I* de T. Tao en lac Lean 4 (`teorth/analysis`) : architecture du lac, philosophie d'auto-contenance vs Mathlib, cinq lemmes emblématiques parmi 44k LOC, méta-récit single-agent vs cluster distribué | 40 min |
| [ANALYSE-03-PFR-Lean](ANALYSE-03-PFR-Lean.ipynb) | La conjecture PFR (polynomial Freiman–Ruzsa, ZMod 2) : méthode entropique de la preuve `teorth/pfr` — énoncé combinatoire, illustrations cosets dans F₂³, `#check` réels et axiomes du lac compilé | 45 min |
| [ANALYSE-04-PFR-Primitives-Python](ANALYSE-04-PFR-Primitives-Python.ipynb) | Trois primitives de PFR, et l'endroit exact où elles cessent de valoir — companion de digestion de ANALYSE-03 : ce qui se transporte hors du cadre d'origine (#12214) | 30 min |
| [ANALYSE-05-KLS-Lean-Python](ANALYSE-05-KLS-Lean-Python.ipynb) | La conjecture KLS démontrée (Bizeul–Klartag–Lehec, arXiv:2610.05474) : énoncé (Théorème 1.1), chaîne de la preuve en cinq maillons (thin-shell, germe quadratique, localisation stochastique, suspension, critère de Song–Zhang), lac local `kls_lean` — audit Mathlib au pin, six définitions, deux théorèmes prouvés (0 sorry, `#print axioms` propre) — thin-shell en Monte-Carlo avec saturation exacte à 8n par l'exponentielle produit, banc 1-lipschitzien minorant `poincareConstant` | 45 min |

**Prérequis d'entrée** : le tutoriel de la série principale (numéros 1 à 6, tactiques et Mathlib). Le point d'entrée réel documenté du carnet 01 est [Search-03e-AStar-Optimality](../../../Search/Part1-Foundations/Search-03e-AStar-Optimality.ipynb) (heuristique A*, companion `search_lean`) — voir sa cellule d'ouverture.

**Marches nommées, à écrire** (règle 5 de la gradation) : entropie de Shannon avant ANALYSE-03, inégalités de concentration avant le converse MIMO ([Lean-21b](../Lean-21b-MIMO-Converse-Native.ipynb)). Elles vivront dans ce dossier ou la série principale selon la décision de renumérotation.

**Marches franchissables** : depuis la série principale, le tutoriel (1-14) suffit pour ANALYSE-01. ANALYSE-02 suppose la lecture d'un lac externe ; ANALYSE-03/04 supposent l'entropie de Shannon (marche nommée ci-dessus) ; ANALYSE-05 ne suppose rien au-delà du tutoriel : son lac est local, posé à côté du carnet.
