# ML-HeadShoulders-CNN (HandsOn Ex17)

**Classe d'actifs :** Forex (USDCAD)
**Cloud project ID :** None (local only)

## Description

CNN Keras pour la détection de figure tête-épaules sur USDCAD. `main.py` charge le modèle pré-entraîné depuis l'Object Store, sous la clé `head-and-shoulders-model.keras`. S'il n'y est pas, l'algorithme entraîne au démarrage un petit CNN sur des figures synthétiques, moins riche que celui de research.ipynb.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-HeadShoulders-CNN"`
**QC Cloud :** Pas encore déployé. Copier les fichiers dans un nouveau projet QC Cloud pour exécuter.

## Métriques de backtest

| Métrique | Valeur |
|----------|--------|
| Modèle | Keras CNN (détection de figure) |
| Univers | USDCAD |
| Rebalance | Event-driven (figure) |

## Fichiers

- main.py - Stratégie (v1.0, CNN de figures)
- research.ipynb - Labellisation des figures et entraînement du CNN
- head-and-shoulders-model.keras - Modèle CNN entraîné par research.ipynb, à déposer dans l'Object Store pour que main.py l'utilise

## Références

- Hands-On AI Trading, Section 06, Exemple 17
