# Manifeste des figures — GenAI Texte

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`.

| Figure | Fichier | Dimensions | Poids | Source (notebook · cellule · output) | Sujet |
|--------|---------|------------|-------|--------------------------------------|-------|
| Scaling pass@k | `texte-scaling-passk.png` | 715×462 | 33 Ko | `16_Scaling_Test_Time_Compute.ipynb` · cellule 8 · output 0 | Courbes de scaling pass@k par bucket (Snell 2024) |
| BoN vs Réflexion | `texte-bon-vs-reflex.png` | 715×462 | 24 Ko | `16_Scaling_Test_Time_Compute.ipynb` · cellule 11 · output 0 | Best-of-N parallèle vs Réflexion séquentielle — frontière compute-optimal |
| Raisonnement vs Scaling | `texte-reason-vs-scale.png` | 770×505 | 50 Ko | `17_Native_Reasoning_vs_Scaling.ipynb` · cellule 11 · output 0 | Raisonnement natif vs scaling de calcul |

**Total** : 3 figures, 105 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Ces sorties sont des **courbes matplotlib** (line-art + étiquettes de texte) : **PNG lossless natif** préféré à WebP pour préserver la netteté du texte (plots déjà petits, 23–50 Ko natifs). 3 figures = toutes les sorties PNG du module (pas de padding).
