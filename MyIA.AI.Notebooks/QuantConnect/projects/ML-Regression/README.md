# ML-Regression

**Classe d'actifs :** Actions US (20 grandes capitalisations)
**ID projet Cloud :** Aucun (local uniquement)

## Description

Stratégie de régression Ridge prédisant les rendements du jour suivant sur un univers de 20 actions. Utilise les rendements open-close décalés comme variables explicatives. Rebalancement bi-hebdomadaire avec ré-entraînement mensuel. Sélectionne les meilleures actions (`top-N`) selon le rendement prédit.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-Regression"`
**QC Cloud :** Pas encore déployé. Copier les fichiers dans un nouveau projet QC Cloud pour l'exécuter.

## Métriques de backtest

| Métrique | Valeur |
|----------|--------|
| Modèle | Régression Ridge |
| Univers | 20 grandes capitalisations |
| Rebalancement | Bi-hebdomadaire |

## Fichiers

- `main.py` — Stratégie (227 lignes, `MLRegressionAlgorithm`)
