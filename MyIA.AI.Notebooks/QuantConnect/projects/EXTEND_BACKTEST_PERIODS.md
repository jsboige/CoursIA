# Extension des Périodes de Backtest - Plan d'Action

**Issue**: #37 - QC iteration strategies - Maximiser periodes backtest
**Date**: 2026-03-23
**Objectif**: Étendre les périodes de backtest pour valider la robustesse sur différentes régimes de marché

---

## Analyse Actuelle

### Périodes de Backtest par Catégorie

| Catégorie | Période la plus courte | Période la plus longue | Moyenne |
|-----------|----------------------|----------------------|---------|
| **Equities** | 2015-2026 (11 ans) | 2008-2026 (18 ans) | 13 ans |
| **Crypto** | 2020-2026 (6 ans) | 2017-2026 (9 ans) | 7 ans |
| **Options** | 2018-2026 (8 ans) | 2019-2026 (7 ans) | 8 ans |
| **Multi-asset** | 2010-2026 (16 ans) | 2015-2026 (11 ans) | 14 ans |

### Opportunités d'Extension Prioritaires

| Priorité | Projet | Période actuelle | Extension proposée | Gain | Raison |
|----------|--------|-----------------|-------------------|------|--------|
| **HIGH** | EMA-Cross-Crypto | 2020-2026 (6 ans) | → 2017-2026 (9 ans) | +3 ans | BTC data disponible depuis 2017 |
| **HIGH** | Crypto-MultiCanal | 2020-2026 (6 ans) | → 2017-2026 (9 ans) | +3 ans | BTC data disponible depuis 2017 |
| **MEDIUM** | OptionsIncome | 2018-2026 (8 ans) | → 2015-2026 (11 ans) | +3 ans | SPY options disponibles depuis 2010 |
| **MEDIUM** | FuturesTrend | 2018-2026 (8 ans) | → 2015-2026 (11 ans) | +3 ans | ETF futures disponibles |
| **LOW** | Trend-Following | 2019-2026 (7 ans) | → 2015-2026 (11 ans) | +4 ans | Equity data disponible |

---

## Plan d'Implémentation

### Phase 1: Crypto Strategies (HIGH Priority) ✅ COMPLETE

#### 1.1 EMA-Cross-Crypto ✅

**Fichier**: `EMA-Cross-Crypto/main.py`

**Changement effectué** (2026-03-23):
```python
# Avant
self.set_start_date(2020, 1, 1)

# Après
self.set_start_date(2017, 1, 1)  # Extended from 2020: +3 years for robustness validation (includes 2017 bull & 2018 crash)
```

**Justification**:
- BTC/USDT data disponible sur Binance Cash depuis 2017
- Permet de valider la stratégie hors du bull market exceptionnel 2020-2021
- Inclut le crash crypto 2018 (stress test)

**Attendu**:
- Sharpe ratio pourrait diminuer (moins de bull bias)
- Max Drawdown pourrait augmenter (crash 2018 inclus)
- Win rate pourrait diminuer

**Backtest requis**: ⏳ En attente lancement manuel sur QC Cloud

#### 1.2 Crypto-MultiCanal ✅

**Fichier**: `Crypto-MultiCanal/main.py`

**Changement effectué** (2026-03-23):
```python
# Avant
self.set_start_date(2020, 1, 1)

# Après
self.set_start_date(2017, 1, 1)  # Extended from 2020: +3 years for robustness validation (includes 2017 bull & 2018 crash)
```

**Justification**:
- Même logique que EMA-Cross-Crypto
- 18 versions déjà testées, extension période finale pour validation

**Backtest requis**: ⏳ En attente lancement manuel sur QC Cloud

---

### Phase 2: Options Strategies (MEDIUM Priority)

#### 2.1 OptionsIncome

**Fichier**: `OptionsIncome/main.py`

**Changement requis**:
```python
# Avant
self.set_start_date(2018, 1, 1)

# Après
self.set_start_date(2015, 1, 1)  # +3 ans, inclut bull 2017-2019 pré-COVID
```

**Justification**:
- SPY options data disponible depuis 2010
- Permet d'inclure période bull 2017-2019 (sans crise COVID)
- Stress test sur régime différent de 2018-2026

**Risque potentiel**:
- VIX filter pourrait nécessiter ajustement (VIX était très bas 2017)
- Covered calls performance pourrait différer en bull market pur

#### 2.2 Option-Wheel

**Fichier**: `Option-Wheel/main.py`

**Changement requis**:
```python
# Avant
self.set_start_date(2019, 1, 1)

# Après
self.set_start_date(2015, 1, 1)  # +4 ans
```

---

### Phase 3: Trend Following Strategies (MEDIUM Priority)

#### 3.1 FuturesTrend

**Fichier**: `FuturesTrend/main.py`

**Changement requis**:
```python
# Avant
self.set_start_date(2018, 1, 1)

# Après
self.set_start_date(2015, 1, 1)  # +3 ans
```

#### 3.2 Trend-Following

**Fichier**: `Trend-Following/main.py`

**Changement requis**:
```python
# Vérifier date actuelle dans main.py
# Extension proposée: 2015-2026
```

---

## Métriques de Validation

Après extension, vérifier:

1. **Sharpe Ratio**: Doit rester > 0.5 pour stratégies robustes
2. **Max Drawdown**: Ne doit pas augmenter de > 50%
3. **Win Rate**: Variation acceptable (< 10% points)
4. **Stabilité**: Pas de changement de régime (robuste → historique)

### Critères de Succès

| Métrique | Threshold | Action |
|----------|-----------|--------|
| Sharpe post-extension | > 0.5 × Sharpe original | Valider |
| MaxDD post-extension | < 1.5 × MaxDD original | Valider |
| CAGR variation | ± 5% acceptable | Valider |
| Régime change | Robuste → Historique | Documenter |

---

## Implémentation Technique

### Méthode 1: Modification directe des fichiers

```python
# Pour chaque projet
# 1. Backup du fichier original
# 2. Modification set_start_date()
# 3. Backtest QC Cloud
# 4. Comparaison métriques
# 5. Update README.md si validation réussie
```

### Méthode 2: Paramétrage (recommandé)

```python
# Dans main.py, ajouter variable configurable
BACKTEST_START_YEAR = 2017  # Configurable par période

def initialize(self):
    self.set_start_date(BACKTEST_START_YEAR, 1, 1)
```

### Méthode 3: Multi-périodes (recherche)

```python
# Tester plusieurs périodes et comparer
periods_to_test = [
    (2017, 2026),  # Actuel étendu
    (2018, 2026),  # Original
    (2015, 2026),  # Extension max
]

for start, end in periods_to_test:
    # Run backtest
    # Compare metrics
```

---

## Checklist d'Exécution

### Phase 1: Crypto ✅
- [x] EMA-Cross-Crypto: Modifier main.py (2020→2017)
- [ ] EMA-Cross-Crypto: Backtest QC Cloud ⏳
- [ ] EMA-Cross-Crypto: Valider métriques
- [ ] EMA-Cross-Crypto: Update README.md
- [x] Crypto-MultiCanal: Modifier main.py (2020→2017)
- [ ] Crypto-MultiCanal: Backtest QC Cloud ⏳
- [ ] Crypto-MultiCanal: Valider métriques
- [ ] Crypto-MultiCanal: Update README.md

### Phase 2: Options
- [ ] OptionsIncome: Modifier main.py (2018→2015)
- [ ] OptionsIncome: Backtest QC Cloud
- [ ] OptionsIncome: Valider métriques
- [ ] OptionsIncome: Update README.md
- [ ] Option-Wheel: Modifier main.py (2019→2015)
- [ ] Option-Wheel: Backtest QC Cloud
- [ ] Option-Wheel: Valider métriques
- [ ] Option-Wheel: Update README.md

### Phase 3: Trend
- [ ] FuturesTrend: Modifier main.py (2018→2015)
- [ ] FuturesTrend: Backtest QC Cloud
- [ ] FuturesTrend: Valider métriques
- [ ] FuturesTrend: Update README.md

---

## Résultats Attendus

### Scénario Optimiste
- Sharpe ratio stable ou amélioré
- Stratégie validée sur période plus longue
- Classification: Historique → Robuste

### Scénario Réaliste
- Sharpe ratio diminue légèrement
- MaxDD augmente (période plus longue)
- Stratégie reste valide mais avec notes ajustées

### Scénario Pessimiste
- Sharpe chute significativement
- Stratégie reclassée: Historique → Exploratoire
- Nécessite ré-optimisation des paramètres

---

## Documentation

Mettre à jour `README.md` après chaque extension validée:

```markdown
| EMA-Cross-Crypto | EMA 20/50 + SMA200 + trailing stop BTCUSDT | **1.272** | 38.2% | 33.1% | 2017-2026 | Py | Debutant | yfinance |
```

Avec note si applicable:
> Note: Période étendue de 2020→2017. Sharpe stable sur 9 ans vs 6 ans originaux.
