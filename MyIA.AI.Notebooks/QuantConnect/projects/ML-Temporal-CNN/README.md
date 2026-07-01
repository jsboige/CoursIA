# ML-Temporal-CNN (HandsOn Ex14)

**Classe d'actifs :** Actions US (QQQ top-3)
**Cloud project ID :** None (local only)

## Description

CNN Conv1D temporel pour la prédiction de rendements. Utilise une fenêtre glissante des 20 derniers jours de rendements comme entrée d'un réseau de convolution 1D.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-Temporal-CNN"`
**QC Cloud :** Pas encore déployé. Copier les fichiers dans un nouveau projet QC Cloud pour exécuter.

## Métriques de backtest

| Métrique | Valeur |
|----------|--------|
| Modèle | Conv1D CNN (Keras) |
| Univers | QQQ top-3 |
| Rebalance | Daily |

## Fichiers

- main.py - Stratégie (v1.0, CNN temporel)
- research.ipynb - Architecture CNN et entraînement

## Références

- Hands-On AI Trading, Section 06, Exemple 14
