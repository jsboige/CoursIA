# ML-Ensemble

**Classe d'actifs :** Actions US (30 grandes capitalisations)
**ID projet Cloud :** Aucun (local uniquement)

## Description

Stratégie ML d'ensemble combinant la régression Ridge, le Random Forest et le Gradient Boosting sur un univers de 30 actions. Rebalancement hebdomadaire avec ré-entraînement hebdomadaire (chaque lundi). Utilise les rendements décalés comme variables explicatives pour la prédiction de direction.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-Ensemble"`
**QC Cloud :** Pas encore déployé. Copier les fichiers dans un nouveau projet QC Cloud pour l'exécuter. **Verdict de recherche** (notebook) : **NO BEATS** — sur 29 titres et 2020-2025, l'ensemble obtient un Sharpe de 0,928 (taux sans risque nul) contre 0,975 pour SPY buy-and-hold. Il ne choisit pas mieux qu'un tirage au hasard des titres dans le même univers (médiane de 20 tirages : 0,950), et un portefeuille équipondéré des 29 titres fait aussi bien (0,943).

## Métriques de backtest

| Métrique | Valeur |
|----------|--------|
| Modèles | Ensemble Ridge + Random Forest + Gradient Boosting |
| Univers | 30 grandes capitalisations |
| Rebalancement | Hebdomadaire |

## Fichiers

- `main.py` — Stratégie (`MLEnsembleAlgorithm`)
- `quantbook.ipynb` - QuantBook de recherche : analyse de la stratégie d'ensemble ML
