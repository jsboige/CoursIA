# ML-Regression

**Classe d'actifs :** Actions US (20 grandes capitalisations)
**ID projet Cloud :** Aucun (local uniquement)

## Description

Stratégie de régression Ridge prédisant les rendements du jour suivant sur un univers de 20 actions. Utilise des features techniques — RSI, ratio EMA20/EMA50, volatilité glissante (5/20 j), rendements décalés (1/5 j), momentum (5/10 j) et distance aux moyennes mobiles — comme variables explicatives. Rebalancement quotidien avec ré-entraînement hebdomadaire (chaque lundi). Sélectionne les meilleures actions (`top-N`) selon le rendement prédit.

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

- `main.py` — Stratégie (`MLRegressionAlgorithm`)
- `quantbook.ipynb` - QuantBook de recherche : régression appliquée à la prévision des rendements
