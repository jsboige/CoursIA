# Markov-Regime-Detection

**Classe d'actifs :** Actions/ETF américains (SPY, TLT, GLD)
**ID projet Cloud :** Aucun (local uniquement)

## Description

Détection de régime markovien avec `MarkovRegression` de statsmodels. Identifie 2 régimes (haussier/baissier) sur les rendements de SPY.

**Consolidé depuis ML-HMM-Regime** (copie quasi-identique avec même nom de classe, même `k_regimes=2`, même logique d'allocation).

## Comment lancer

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Markov-Regime-Detection"`
**QC Cloud :** Pas encore déployé. Copier les fichiers dans un nouveau projet QC Cloud pour lancer.

## Métriques de backtest

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | 0.408 |
| Modèle | MarkovRegression |
| Régimes | 2 (haussier/baissier) |

## Fichiers

- `main.py` - Stratégie (v1.1, régime markovien, consolidé depuis ML-HMM-Regime)
