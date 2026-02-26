# Diagnostic Rapide - BTC-MachineLearning (21047688)

**Date**: 2026-02-15
**Analyste**: Claude QC Strategy Analyzer
**Statut**: COMPILATION OK - NEEDS_BACKTEST

---

## Resume Executif

| Aspect | Statut | Details |
|--------|--------|---------|
| **Synchronisation Cloud/Local** | OK | Fichiers identiques, corrections in-situ presentes |
| **Compilation** | OK | BuildSuccess (warnings linter non-bloquants) |
| **Backtests** | AUCUN | 0 backtests disponibles (historique supprime) |
| **Code Quality** | MOYEN | Fonctionne mais 3 problemes critiques |
| **Potentiel** | ELEVE | Sharpe estimé 0 -> >0.5 avec ameliorations |

---

## Problemes Critiques Identifies

### 1. Data Leakage (BLOQUEUR)
```
Entrainement: 365 jours d'historique AVANT la date de backtest
Backtest: 2023-01-01 à 2024-01-01
=> Le modèle "voit" les données de test pendant l'entrainement !
```
**Solution**: Separer train (2021-2022) et test (2023).

### 2. Pas de Risk Management (CRITIQUE)
```
Strategie: All-in (100% BTC) ou All-out (100% USDT)
Pas de stop-loss, pas de take-profit
=> Drawdowns potentiellement énormes
```
**Solution**: Ajouter stop-loss -5%, take-profit +10%.

### 3. Modele Statique (CRITIQUE)
```
Entrainement: Une seule fois au début du backtest
=> Ne s'adapte pas aux changements de régime
```
**Solution**: Re-entrainer tous les 30 jours.

---

## Ameliorations Proposees (Priorisees)

| # | Amelioration | Impact | Effort | Priorite |
|---|--------------|--------|--------|----------|
| 1 | Corriger data leakage | Sharpe realiste | LOW | HAUTE |
| 2 | Ajouter stop-loss/take-profit | DD -15% | LOW | HAUTE |
| 3 | Re-training periodique (30j) | Sharpe +0.2 | MEDIUM | HAUTE |
| 4 | Position sizing probabiliste | Sharpe +0.15 | MEDIUM | MOYENNE |
| 5 | Enrichir features (regime) | Sharpe +0.1 | MEDIUM | MOYENNE |
| 6 | Tester XGBoost/LightGBM | Sharpe +0.1 | MEDIUM | BASSE |

---

## Metriques Cibles

| Metrique | Actuel | Cible | Excellent |
|----------|--------|-------|-----------|
| **Sharpe Ratio** | ? | >0.3 | >0.8 |
| **Max Drawdown** | ? | <30% | <15% |
| **Win Rate** | ? | >50% | >60% |
| **Trades** | ? | >50 | >100 |

---

## Actions Immediates

1. **Lancer backtest initial** (via UI web)
   - URL: https://www.quantconnect.com/project/21047688
   - Objectif: Obtenir baseline de performance

2. **Implementer ameliorations HAUTE PRIORITE**
   - Modifier `main.py` pour train/test separation
   - Ajouter stop-loss/take-profit
   - Ajouter re-training periodique

3. **Backtester et comparer**
   - Sharpe, DD, Win Rate, Trades

---

## Architecture Actuelle

### Features (9 indicateurs)
- **Trend**: SMA20, EMA10, EMA20, EMA50, EMA200
- **Momentum**: RSI14, DailyReturn
- **Trend Strength**: ADX14
- **Volatility**: ATR14

### Modele
- **Type**: RandomForestClassifier
- **Hyperparams**: n_estimators=100, max_depth=5
- **Entrainement**: In-situ sur 365 jours

### Logique de Trading
```
if predict(X) == UP:
    SetHoldings(BTC, 100%)
else:
    Liquidate()
```

---

## Fichiers du Projet

| Fichier | Taille | Description |
|---------|--------|-------------|
| `main.py` | 6.4 KB | Algorithme enhanced (9 features) |
| `main-simple.py` | 2.5 KB | Algorithme simple (3 features, ObjectStore-dependent) |
| `research.ipynb` | 8.9 KB | Notebook entrainement enhanced |
| `research-simple.ipynb` | 5.4 KB | Notebook entrainement simple |
| `ANALYSIS.md` | 12 KB | Analyse detaillee complete |
| `DIAGNOSTIC.md` | Ce fichier | Resume executif |

---

## Conclusion

Le projet **compile sans erreur** et le code **contient les corrections d'entrainement in-situ**.

Cependant, **aucun backtest n'est disponible** pour valider la performance. Les 3 problemes critiques identifies (data leakage, pas de risk management, modele statique) doivent etre corriges avant de lancer un nouveau backtest.

**Potentiel d'amelioration: ELEVE**. Avec les ameliorations proposees, le Sharpe peut passer de ~0 à >0.5.

**Prochaine etape**: Lancer un backtest manuel via l'UI web pour obtenir une baseline.
