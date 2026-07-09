# Manifeste des figures — Image examples

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`.

| Figure | Fichier | Dimensions | Poids | Source (notebook · cellule · output) | Source native |
|--------|---------|------------|-------|--------------------------------------|---------------|
| Empire romain (117 ap. J.-C.) — carte d'expansion | `imgex-hist1.webp` | 1200×846 | 89 Ko | `history-geography.ipynb` · cellule 8 · output 3 | 1260×889, 1882 Ko |
| Colisée de Rome (Iᵉʳ siècle) — reconstruction photoréaliste | `imgex-hist2.webp` | 1200×846 | 122 Ko | `history-geography.ipynb` · cellule 12 · output 3 | 1260×889, 1911 Ko |
| Révolution française (1789-1799) — frise chronologique illustrée | `imgex-hist3.webp` | 1200×848 | 64 Ko | `history-geography.ipynb` · cellule 18 · output 3 | 1259×890, 1560 Ko |
| Les Misérables — la barricade (scène XIXᵉ) | `imgex-lit1.webp` | 769×1200 | 65 Ko | `literature-visual.ipynb` · cellule 8 · output 2 | 891×1390, 1957 Ko |
| Jean Valjean (Les Misérables) — character sheet (portrait + âges) | `imgex-lit2.webp` | 769×1200 | 62 Ko | `literature-visual.ipynb` · cellule 10 · output 3 | 891×1390, 2116 Ko |
| Cellule animale en coupe — schéma des organites | `imgex-sci.webp` | 1200×846 | 86 Ko | `science-diagrams.ipynb` · cellule 12 · output 3 | 1260×889, 1420 Ko |

**Total** : 6 figures, 501 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Ces sorties sont des images GenAI photographiques denses (sources 1,4–2,1 Mo) : WebP q82 à 1200 px comprime d'un facteur 15–30 sans perte visuelle pédagogique (recommandation WebP P2 « gain net »). Chaque figure couvre un domaine éducatif distinct (histoire-géographie, littérature, sciences).
