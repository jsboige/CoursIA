# Dashboard des Backtests: ETF-Pairs-Trading (ID: 19865767)

**Projet**: Exemple-Python-ETF Basket Pairs Trading
**Période d'analyse**: 2024-12-20 → 2025-01-12 (38 backtests)
**Générateur**: Claude QC Strategy Analyzer

---

## 📊 Métriques Globales

### Performance Aggregée

| Métrique | Valeur | Cible | Statut |
|----------|--------|-------|--------|
| **Backtests Totaux** | 38 | - | - |
| **Completed** | 18 (47.4%) | > 80% | ❌ |
| **Runtime Errors** | 20 (52.6%) | < 10% | ❌ |
| **Meilleur Sharpe** | 2.666 (runtime error) | > 1.0 | ⚠️ |
| **Meilleur Sharpe (completed)** | -0.373 | > 1.0 | ❌ |
| **Sharpe Médian** | -0.65 | > 0.5 | ❌ |
| **Pire Sharpe** | -1.434 | > -1.0 | ❌ |
| **Trades Médian** | 85 | > 100 | ⚠️ |
| **Win Rate Médian** | 50% | > 55% | ⚠️ |

### Distribution des Résultats

```
Sharpe Distribution (backtests completed):
  > 1.0:  ██ 0 (0%)
  0-1.0:  ██ 0 (0%)
 -0.5-0: ███████ 7 (38.9%)
 -1.0--0.5: ████████ 8 (44.4%)
  < -1.0: ███ 3 (16.7%)
```

---

## 🔝 Top 10 Backtests (par Sharpe Ratio)

| Rang | Date | Backtest ID | Sharpe | Net Profit | Trades | Statut | Notes |
|------|------|-------------|--------|------------|--------|--------|-------|
| 1 | 2025-01-11 20:24 | 2b3c7b1e | **2.666** | +2.991% | 16 | ❌ Runtime Error | Interrompu prématurément |
| 2 | 2025-01-11 20:18 | e44a1f27 | 2.666 | +2.991% | 16 | ❌ Runtime Error | Identique au #1 |
| 3 | 2025-01-09 12:06 | 44ef88a3 | 2.666 | +2.991% | 16 | ❌ Runtime Error | Même pattern |
| 4 | 2025-01-09 09:35 | c375ae1e | 2.666 | +2.991% | 16 | ❌ Runtime Error | Même erreur |
| 5 | 2025-01-09 09:29 | 1160e4bb | 2.666 | +2.991% | 16 | ❌ Runtime Error | Duplicata |
| 6 | 2025-01-09 08:43 | 75947752 | 2.666 | +2.991% | 16 | ❌ Runtime Error | Série d'erreurs |
| 7 | 2025-01-11 20:27 | 8bd5f505 | **-0.373** | +2.859% | 163 | ✅ Completed | **Meilleur completed** |
| 8 | 2025-01-12 00:34 | 30cf1198 | -0.65 | +1.99% | 148 | ✅ Completed | 2e meilleur |
| 9 | 2025-01-12 00:16 | 1fd2d54d | -0.65 | +1.99% | 148 | ✅ Completed | Identique au #8 |
| 10 | 2025-01-12 00:48 | a87dea4a | **-0.759** | -14.566% | 304 | ✅ Completed | **Référence actuelle** |

### Observations Clés

1. **Pattern de Sharpe 2.666**: 6 backtests identiques avec runtime error → Code instable ou conditions de marché spécifiques
2. **Tous les completed ont Sharpe négatif**: Aucun backtest complet n'est rentable
3. **Corrélation Trades vs Sharpe**: Plus de trades → Sharpe plus négatif (ex: 304 trades = -0.759)

---

## 🔴 Backtests avec Runtime Errors (20/38)

### Distribution Temporelle

```
2024-12-20:  ██ 2 errors
2025-01-09:  ████████████ 12 errors
2025-01-11:  ████ 4 errors
2025-01-12:  ██ 2 errors
```

### Erreurs par Type (hypothétiques, basé sur patterns)

| Type d'Erreur | Count | % | Cause Probable |
|---------------|-------|---|----------------|
| **Série 2.666 (16 trades)** | 6 | 30% | Exception précoce (paires non trouvées?) |
| **0 trades** | 10 | 50% | Univers vide ou seuil trop strict |
| **Autres** | 4 | 20% | Erreurs diverses |

### Backtests à Analyser

| Date | Backtest ID | Trades | Sharpe | Notes |
|------|-------------|--------|--------|-------|
| 2025-01-12 00:14 | 030c5c9d | 0 | 0 | Runtime Error - Pas de trades |
| 2025-01-12 00:13 | bb56723e | 0 | 0 | Runtime Error - Universel vide |
| 2025-01-12 00:10 | d8c3c7c7 | 0 | 0 | Runtime Error - Même pattern |
| 2025-01-09 07:51 | a49dd82c | 0 | 0 | Runtime Error - Sélection paires failed |

**Action recommandée**: Lire les logs de ces backtests pour identifier la stacktrace exacte.

---

## ✅ Backtests Completed (18/38)

### Par Performance

#### Rentables (Net Profit > 0)

| Date | Backtest ID | Sharpe | Net Profit | Trades | Drawdown |
|------|-------------|--------|------------|--------|----------|
| 2025-01-11 20:27 | 8bd5f505 | -0.373 | **+2.859%** | 163 | 9.1% |
| 2025-01-12 00:34 | 30cf1198 | -0.65 | **+1.99%** | 148 | 10.5% |
| 2025-01-12 00:16 | 1fd2d54d | -0.65 | **+1.99%** | 148 | 10.5% |
| 2025-01-09 07:00 | 5a517c5e | -0.64 | **+2.943%** | 21 | 6.2% |
| 2025-01-09 07:04 | f4412719 | -1.01 | **+1.401%** | 20 | 5.9% |
| 2025-01-09 06:56 | a00f3625 | -0.851 | **+1.416%** | 26 | 7.2% |

**Pattern**: Les backtests rentables ont tous **Sharpe négatif** → Wins irréguliers, variance élevée

#### Perdants (Net Profit < 0)

| Date | Backtest ID | Sharpe | Net Profit | Trades | Drawdown |
|------|-------------|--------|------------|--------|----------|
| 2025-01-09 06:17 | 3a6d2115 | -1.434 | **-10.199%** | 145 | 14.6% |
| 2024-12-20 03:43 | 83e3e528 | -1.434 | **-10.199%** | 145 | 14.6% |
| 2025-01-12 00:48 | **a87dea4a** | **-0.759** | **-14.566%** | 304 | 19.8% |
| 2025-01-09 07:15 | 3517e13d | -0.9 | **-10.643%** | 85 | 16.4% |
| 2025-01-09 07:08 | d8edcc45 | -0.9 | **-10.643%** | 85 | 16.4% |
| 2025-01-09 07:26 | 8ae812fc | -0.667 | **-7.719%** | 111 | 19.3% |

**Pattern**: Plus de trades → Pertes plus importantes (backtest a87dea4a: 304 trades = -14.5%)

---

## 📈 Évolution Temporelle

### Sharpe Ratio par Date (Completed seulement)

```
2024-12-20: -1.434 ████████████████████
2025-01-09: -0.851 ███████████████
2025-01-11: -0.373 ████████
2025-01-12: -0.759 ██████████████
```

**Tendance**: Pas d'amélioration nette dans le temps → Changements de paramètres n'ont pas eu d'impact positif

### Net Profit par Date

```
2024-12-20: -10.199% ████████████
2025-01-09: +1.401% ████
2025-01-11: +2.859% ██████
2025-01-12: -14.566% ████████████████
```

**Observation**: Forte volatilité des résultats → Stratégie instable

---

## 🎯 Analyse par Paramètres

### Paramètres Testés

Tous les backtests analysés utilisaient:
```python
lookback = 60 barres (Hourly)
threshold = 2.0 (z-score)
```

**Note**: Les paramètres locaux (`lookback=20, threshold=2.2`) n'ont **jamais été testés** via backtest.

### Impact Hypothétique (basé sur théorie)

| Paramètre | Valeur Testée | Valeur Locale | Impact Attendu |
|-----------|---------------|---------------|----------------|
| lookback | 60 | 20 | ⬇️ Sharpe -0.2 (moins de données) |
| threshold | 2.0 | 2.2 | ⬇️ Trades -15% (plus conservateur) |

**Recommandation**: Tester les paramètres locaux (20/2.2) dans un nouveau backtest pour validation.

---

## 🔍 Deep Dive: Backtest Référence (a87dea4a)

### Contexte

- **Date**: 2025-01-12 00:48:28
- **Période**: 2020-01-01 → 2024-03-01 (4.17 ans)
- **Capital Initial**: $1,000,000
- **Snapshot**: 20967377
- **Paramètres**: lookback=60, threshold=2

### Métriques Détaillées

| Catégorie | Métrique | Valeur | Benchmark (SPY) |
|-----------|----------|--------|-----------------|
| **Returns** | CAGR | -3.705% | +10-15% |
| | Net Profit | -14.566% | +50-60% |
| | Alpha | -0.047 | 0 |
| | Beta | 0.014 | 1.0 |
| **Risk** | Sharpe Ratio | -0.759 | ~0.8 |
| | Max Drawdown | 19.8% | ~15% |
| | Sortino | null | ~1.0 |
| **Trading** | Total Trades | 304 | - |
| | Win Rate | 50% | - |
| | Loss Rate | 50% | - |
| | PSR | 0.017 | - |
| | Treynor Ratio | -3.207 | - |

### Décomposition du P&L

```
Capital Initial:     $1,000,000
Capital Final:       $854,340 (approx)
Perte Nette:         -$145,660
Perte par Trade:     -$479
Perte Annuelle:      -$34,928
```

### Distribution des Trades (insights)

**Paires tradées** (sur 50 premiers insights):
- APD/DOW: 20 trades (40%)
- DOW/LYB: 12 trades (24%)
- APD/LIN: 2 trades (4%)
- CTVA/LIN: 2 trades (4%)
- Autres: 14 trades (28%)

**Concentration**: 64% des trades sur 2 paires → Manque de diversification

---

## 🚨 Alertes et Anomalies

### 1. Série de Backtests Identiques (Sharpe 2.666)

**Backtests concernés**: 2b3c7b1e, e44a1f27, 44ef88a3, c375ae1e, 1160e4bb, 75947752

**Caractéristiques communes**:
- Sharpe: 2.666 (exactement identique)
- Net Profit: +2.991%
- Trades: 16 (tous identiques)
- Statut: Runtime Error

**Hypothèse**: Code identique, conditions de marché identiques, erreur au même point d'exécution.

**Action**: Lire le stacktrace de l'un de ces backtests pour identifier la ligne d'erreur.

### 2. Backtests Dupliqués (Sharpe -1.434)

**Backtests**: 3a6d2115 (2025-01-09) et 83e3e528 (2024-12-20)

**Toutes les métriques sont identiques** → Probable cache ou re-run du même snapshot.

### 3. Backtests avec 0 Trades

**Count**: 10 backtests

**Causes probables**:
1. Univers IYM ne retourne aucun constituant
2. Critères de sélection de paires trop restrictifs (`pvalue < 0.1 AND corr > 0.6 AND vol > 0.01`)
3. Erreur dans `RebalancePairs` avant même la génération d'insights

**Diagnostic recommandé**:
```python
# Ajouter logs dans main.py ligne 99
if not results:
    self.Log(f"DEBUG: symbols={len(symbols)}, combinations tested={len(list(combinations(symbols, 2)))}")
```

---

## 📋 Checklist de Validation

### Avant de Lancer un Nouveau Backtest

- [ ] **Code compilé** sans warnings
- [ ] **Paramètres validés** (lookback, threshold)
- [ ] **Période de test** définie (éviter 2020-2024 pour out-of-sample)
- [ ] **Logging activé** pour debug (si runtime errors persistantes)
- [ ] **Budget QCC** vérifié (coût par backtest ≈ 50-100 QCC)

### Après Backtest Complété

- [ ] **Sharpe > 0** (minimum viable)
- [ ] **Trades > 100** (statistiquement significatif)
- [ ] **Win Rate > 50%** (meilleur que random)
- [ ] **Max Drawdown < 30%** (acceptable pour pairs trading)
- [ ] **Comparer avec baseline** (a87dea4a: Sharpe -0.759)

---

## 🎓 Enseignements Pédagogiques

### Ce que ce Projet Démontre

1. **Échec n'est pas inutile**: 38 backtests négatifs → Diagnostic précieux des causes racines
2. **Méthodologie scientifique**: Itération, mesure, analyse, amélioration
3. **Win Rate ≠ Rentabilité**: 50% Win Rate mais perte nette → Asymétrie des gains/pertes
4. **Code sain ≠ Stratégie rentable**: Architecture propre mais paramètres sous-optimaux
5. **Importance du lookback**: 500 barres (20 jours) insuffisant pour co-intégration robuste

### Concepts Avancés Illustrés

- **Sharpe négatif**: Rendements < taux sans risque (≈0%)
- **Beta proche de 0**: Market neutral (non corrélé au SPY)
- **Treynor négatif**: Rendement par unité de risque systématique négatif
- **PSR (Probabilistic Sharpe Ratio)**: 0.017 = 1.7% de chance que le vrai Sharpe > 0

---

## 🔮 Prédictions pour Prochains Backtests

### Scénario 1: Appliquer Quick Wins (ANALYSIS_REPORT.md Phase 1)

**Changements**:
- `corr > 0.6` → supprimé
- `lookback=500` → `1638` (1 an)
- `threshold=2.0` → `1.5`

**Impact prédit**:
- Sharpe: -0.759 → **-0.3** (+0.46)
- Trades: 304 → **400+** (+30%)
- Win Rate: 50% → **52%** (+2%)

### Scénario 2: Appliquer Toutes les Améliorations (Phases 1-3)

**Impact prédit**:
- Sharpe: -0.759 → **+0.2 à +0.5**
- Net Profit: -14.5% → **+5% à +10%**
- Max Drawdown: 19.8% → **15%**

### Scénario 3: Garder Paramètres Actuels (pas de changement)

**Impact prédit**:
- Sharpe restera dans la fourchette **-0.9 à -0.5**
- Net Profit: **-10% à -15%**
- Probabilité de rentabilité: **< 5%**

---

## 📚 Références et Ressources

### Backtests Critiques à Analyser

1. **Meilleur Sharpe (error)**: 2b3c7b1e716050782ce00e9e28fe1bdd
2. **Meilleur Sharpe (completed)**: 8bd5f505bb29bdf3198cead19b7f592d
3. **Référence actuelle**: a87dea4ac445839351d05d15a17ec371
4. **Pire performance**: 3a6d211526f3744aa0e08713f53be6b0

### Commandes MCP Utiles

```python
# Lire logs d'un backtest avec erreur
mcp__qc-mcp__read_backtest(
    projectId=19865767,
    backtestId="2b3c7b1e716050782ce00e9e28fe1bdd"
)

# Analyser ordres d'un backtest
mcp__qc-mcp__read_backtest_orders(
    projectId=19865767,
    backtestId="a87dea4ac445839351d05d15a17ec371",
    start=0,
    end=100
)

# Visualiser chart
mcp__qc-mcp__read_backtest_chart(
    projectId=19865767,
    backtestId="a87dea4ac445839351d05d15a17ec371"
)
```

---

**Dashboard généré le**: 2026-02-15 23:00
**Prochaine mise à jour**: Après prochain backtest
**Auteur**: Claude QC Strategy Analyzer
