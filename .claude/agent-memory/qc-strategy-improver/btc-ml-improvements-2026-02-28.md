# BTC-ML-Researcher - Ameliorations Iteratives

## Etat Initial (Contexte)
- Projet ID: 28433750
- Sharpe: 0.254
- Win Rate: 78%
- CAGR: 8%
- Max DD: 13.8%
- Objectif: Sharpe > 0.5

## Historique des Ameliorations

### Passe 1-3: Ameliorations de base (deja appliquees avant ce session)
- Filtre volatilite 60% (Sharpe +47% dans la recherche)
- Stop-loss 8% (au lieu de 5%)
- Take-profit 15% (au lieu de 10%)
- Data leakage fix (EMA[:i] au lieu de EMA[:i+1])
- Training 2019-2022, test 2023-2026

### Passe 4: Enhanced Trend Filter (2026-02-28)

**Date**: 2026-02-28
**Compile ID**: 3d532b86d4e25646b48954411c1af8c7-baae88b5b447ae35b292ea4ab0ce1981
**Backtest ID**: 7747767fe389efa25facdbf1f74c09c9

#### Changements implements

| Parametre | Avant | Apres | Impact attendu |
|-----------|-------|-------|----------------|
| **CONFIDENCE_LONG_THRESHOLD** | 0.58 | 0.56 | +5% trades |
| **CONFIDENCE_EXIT_THRESHOLD** | 0.42 | 0.40 | +5% trades |
| **n_estimators** | 100 | 50 | -50% overfitting |
| **max_depth** | 5 | 4 | -20% overfitting |
| **min_samples_leaf** | None | 10 | Regularization |
| **Trend Filter** | EMA200 | EMA200 + RSI>40 + ADX>20 | Multi-confirmation |

#### Rationale

1. **Confidence thresholds relaches**: 0.58/0.42 -> 0.56/0.40
   - Permet plus de trades avec bonne confiance
   - Zone d'incertitude reduite de 16% a 16%

2. **Model regularization**:
   - n_estimators: 100 -> 50 (moins d'overfitting)
   - max_depth: 5 -> 4 (moins de complexite)
   - min_samples_leaf: 10 (evite leafs trop specifiques)

3. **Enhanced Trend Filter** (multi-confirmation):
   - Prix > EMA200 (trend long terme haussier)
   - RSI > 40 (pas de survente)
   - ADX > 20 (trend present, pas sideways)
   - Evite faux signaux en range/consolidation

#### Filtres actifs

1. **Volatility Filter**: Skip si vol annualisee > 60%
2. **Trend Filter**: Skip si price < EMA200
3. **RSI Filter**: Skip si RSI < 40 (oversold)
4. **ADX Filter**: Skip si ADX < 20 (no trend)

#### Resultats attendus

| Metrique | Avant | Attendu | Delta |
|----------|-------|---------|-------|
| Sharpe | 0.254 | 0.40-0.60 | +0.15 to +0.35 |
| CAGR | 8% | 12-18% | +4% to +10% |
| Max DD | 13.8% | 10-15% | -1% to -4% |
| Win Rate | 78% | 75-80% | -3% to +2% |

#### Logique des filtres

```python
# Volatility filter (existant)
if current_vol > 0.60:
    return  # Skip high vol periods

# Enhanced trend filter (nouveau)
if current_price < ema_200:
    return  # Skip bear markets
if rsi_val < 40:
    return  # Skip oversold conditions
if adx_val < 20:
    return  # Skip sideways markets

# Position sizing avec seuils relaxes
if confidence_up > 0.56:  # (etait 0.58)
    # Long avec confirmation multi-filtres
elif confidence_up < 0.40:  # (etait 0.42)
    # Exit
```

#### Statut compilation

- **Compile ID**: 3d532b86d4e25646b48954411c1af8c7-baae88b5b447ae35b292ea4ab0ce1981
- **State**: BuildSuccess
- **Warnings**: Normaux (linter QC avec mixins)
- **Backtest ID**: 7747767fe389efa25facdbf1f74c09c9
- **Statut**: En attente de resultats

---

## Prochaines Etapes (si Sharpe < 0.5)

### Option 1: Feature Engineering
- Ajouter MACD comme feature
- Ajouter Bollinger Bands position
- Ajouter volume profile

### Option 2: Regime Detection
- Detecter regimes (BULL/BEAR/SIDEWAYS)
- Adapter les seuils par regime
- Reduire exposition en BEAR

### Option 3: Ensemble Methods
- Tester XGBoost au lieu de RandomForest
- Gradient boosting pour meilleure generalisation

### Option 4: Ajustement Stop-Loss Dynamique
- ATR-based stop (2x ATR au lieu de 8% fixe)
- Trailing stop pendant les trends forts

### Option 5: Position Sizing Ameliore
- Kelly Criterion pour position size
- Reduction size en haute volatilite

---

## References

- Research BTC-ML: Filtre vol 60% -> Sharpe 1.249
- Analyse failing strategies: https://github.com/.../failing-strategies-analysis-2026-02-26.md
- QuantConnect docs: https://www.quantconnect.com/docs
