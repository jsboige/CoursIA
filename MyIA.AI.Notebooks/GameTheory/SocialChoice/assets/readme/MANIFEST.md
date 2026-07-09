# Manifeste des figures — GameTheory / SocialChoice

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`.

| Figure | Fichier | Dimensions | Poids | Source (notebook · cellule · output) | Sujet |
|--------|---------|------------|-------|--------------------------------------|-------|
| Synthèse des axiomes d'Arrow | `sc-arrow.png` | 1489×515 | 20 Ko | `01-Arrow-Impossibility-Theorem.ipynb` · cellule 29 · output 0 | 3 panneaux (Borda / Pluralité / Dictature) × 3 barres (Pareto, IIA, Non-dictature), vert « SATISFAIT » / rouge « VIOLÉ » |
| Cycle de Condorcet | `sc-condorcet.png` | 690×490 | 25 Ko | `03-Voting-Methods.ipynb` · cellule 10 · output 1 | Graphe orienté A→B→C→A (layout circulaire) : le majority pairwise crée un cycle, aucun vainqueur n'émerge |
| Paradoxe de Sen | `sc-sen.png` | 765×590 | 24 Ko | `03-Voting-Methods.ipynb` · cellule 21 · output 0 | 3 noeuds (a, b, c) : flèches vertes « Liberté » (Prude c>a, Lewd b>c), flèche rouge « Pareto » (a>b), flèche orange pointillée « Transitivité » (b>a) |
| Théorème de l'électeur médian | `sc-median.png` | 1389×490 | 62 Ko | `03-Voting-Methods.ipynb` · cellule 29 · output 0 | 2 panneaux : histogramme des pics de préférence (ligne pointillée rouge = médiane) + courbes d'utilité unimodales de 3 électeurs (utilité = −distance au pic) |
| Modèle de Downs | `sc-downs.png` | 1389×490 | 50 Ko | `03-Voting-Methods.ipynb` · cellule 32 · output 0 | 2 panneaux : histogramme des électeurs (positions initiales/finales des partis) + trajectoires des 2 partis (bleu gauche / rouge droite) convergeant vers l'électeur médian (vert pointillé) sur 20 rounds |
| Illustration de l'agrégation computationnelle | `sc-z3-sat.png` | 1312×590 | 67 Ko | `04-Computational-Aggregation-SAT-Z3.ipynb` · cellule 31 · output 0 | 2 panneaux : diagramme conceptuel des cercles de contraintes Pareto/IIA/Non-dictature à intersection vide + courbe semi-log du nombre de profils (m!)^k explosant avec le nombre d'alternatives (illustration conceptuelle, non une sortie du solveur Z3) |

**Total** : 6 figures, 254 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Courbes matplotlib (line-art + étiquettes de texte) → **PNG lossless natif** (netteté du texte privilégiée ; plots 20–76 Ko natifs, sous le seuil sans downscale). Arc narratif : du théorème d'impossibilité d'Arrow (limite axiomatique) aux méthodes de vote (Condorcet, Sen, électeur médian, Downs) puis à l'agrégation computationnelle par SAT/Z3.
