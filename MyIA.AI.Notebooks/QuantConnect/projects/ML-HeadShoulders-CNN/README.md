# ML-HeadShoulders-CNN (HandsOn Ex17)

**Classe d'actifs :** Forex (USDCAD)
**Cloud project ID :** None (local only)

## Description

CNN Keras pour la détection de figure tête-épaules sur USDCAD. Requiert le modèle pré-entraîné issu de research.ipynb.

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

## Références

- Hands-On AI Trading, Section 06, Exemple 17
