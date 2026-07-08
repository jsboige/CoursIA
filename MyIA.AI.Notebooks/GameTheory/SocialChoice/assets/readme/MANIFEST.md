# Manifeste des figures — GameTheory / SocialChoice

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`.

| Figure | Fichier | Dimensions | Poids | Source (notebook · cellule · output) | Sujet |
|--------|---------|------------|-------|--------------------------------------|-------|
| Synthèse des axiomes d'Arrow | `sc-arrow.png` | 1489×515 | 20 Ko | `01-Arrow-Impossibility-Theorem.ipynb` · cellule 29 · output 0 | Théorème d'impossibilité : visualisation des axiomes |
| Vainqueur de Condorcet | `sc-condorcet.png` | 690×490 | 25 Ko | `03-Voting-Methods.ipynb` · cellule 10 · output 1 | Détermination du vainqueur de Condorcet |
| Paradoxe de Sen | `sc-sen.png` | 765×590 | 24 Ko | `03-Voting-Methods.ipynb` · cellule 21 · output 0 | Paradoxe du libéral parétien |
| Théorème de l'électeur médian | `sc-median.png` | 1389×490 | 62 Ko | `03-Voting-Methods.ipynb` · cellule 29 · output 0 | Convergence vers l'électeur médian |
| Modèle de Downs | `sc-downs.png` | 1389×490 | 50 Ko | `03-Voting-Methods.ipynb` · cellule 32 · output 0 | Simulation de convergence vers le centre |
| Agrégation SAT (Z3) | `sc-z3-sat.png` | 1312×590 | 67 Ko | `04-Computational-Aggregation-SAT-Z3.ipynb` · cellule 31 · output 0 | Agrégation computationnelle via solveur SAT/Z3 |

**Total** : 6 figures, 254 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Courbes matplotlib (line-art + étiquettes de texte) → **PNG lossless natif** (netteté du texte privilégiée ; plots 20–76 Ko natifs, sous le seuil sans downscale). Arc narratif : du théorème d'impossibilité d'Arrow (limite axiomatique) aux méthodes de vote (Condorcet, Sen, électeur médian, Downs) puis à l'agrégation computationnelle par SAT/Z3.
