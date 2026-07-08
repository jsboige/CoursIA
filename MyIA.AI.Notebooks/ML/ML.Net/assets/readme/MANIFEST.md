# Manifeste des figures — ML / ML.Net

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`. Les figures sont extraites des notebooks **Python** (parité marathon #4956 — les mêmes concepts ML illustrés côté C# ML.NET et côté Python scikit-learn).

| Figure | Fichier | Dimensions | Poids | Source (notebook · cellule · output) | Sujet |
|--------|---------|------------|-------|--------------------------------------|-------|
| Régression (scatter) | `ml-regression.png` | 690×440 | 36 Ko | `ML-1-Introduction-Python.ipynb` · cellule 17 · output 0 | Nuage de points et droite de régression |
| Série temporelle | `ml-ts-series.png` | 1198×429 | 116 Ko | `ML-5-TimeSeries-Python.ipynb` · cellule 7 · output 0 | Série de ventes brute |
| Décomposition STL | `ml-ts-stl.png` | 1198×868 | 179 Ko | `ML-5-TimeSeries-Python.ipynb` · cellule 11 · output 0 | Décomposition tendance/saisonnalité/résidu |
| Prévision | `ml-ts-forecast.png` | 1195×429 | 126 Ko | `ML-5-TimeSeries-Python.ipynb` · cellule 20 · output 0 | Prévision sur le jeu de test |
| Clustering K-means | `ml-clustering.png` | 1418×483 | 55 Ko | `ML-8-Clustering-Python.ipynb` · cellule 12 · output 0 | Partition en clusters |
| Méthode du coude | `ml-coude.png` | 758×447 | 55 Ko | `ML-8-Clustering-Python.ipynb` · cellule 16 · output 1 | Choix du nombre K de clusters |

**Total** : 6 figures, 580 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Courbes matplotlib (line-art + étiquettes) → **PNG lossless natif** (netteté du texte privilégiée). Arc : régression (ML-1) → séries temporelles + décomposition STL + prévision (ML-5) → clustering K-means + méthode du coude (ML-8).
