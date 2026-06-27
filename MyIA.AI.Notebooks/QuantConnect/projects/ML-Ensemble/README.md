# ML-Ensemble

**Classe d'actifs :** Actions US (30 grandes capitalisations)
**ID projet Cloud :** Aucun (local uniquement)

## Description

Stratégie ML d'ensemble combinant la régression Ridge, le Random Forest et le Gradient Boosting sur un univers de 30 actions. Rebalancement hebdomadaire avec ré-entraînement mensuel. Utilise les rendements décalés comme variables explicatives pour la prédiction de direction.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-Ensemble"`
**QC Cloud :** Pas encore déployé. Copier les fichiers dans un nouveau projet QC Cloud pour l'exécuter.

## Métriques de backtest

| Métrique | Valeur |
|----------|--------|
| Modèles | Ensemble Ridge + Random Forest + Gradient Boosting |
| Univers | 30 grandes capitalisations |
| Rebalancement | Hebdomadaire |

## Fichiers

- `main.py` — Stratégie (269 lignes, `MLEnsembleAlgorithm`)
