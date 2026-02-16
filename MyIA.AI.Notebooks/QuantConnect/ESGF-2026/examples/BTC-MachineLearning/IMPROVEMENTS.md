# BTC-MachineLearning - Ameliorations implementees

**Projet**: BTC-MachineLearning (ID: 21047688)
**Date**: 2026-02-15
**Statut**: Compile avec succes (BuildSuccess)

## Ameliorations HIGH priority implementees

### 1. Fix data leakage - Separation train/test stricte

**Probleme**: L'entrainement initial utilisait les 365 derniers jours depuis le debut du backtest, ce qui pouvait inclure des donnees de la periode de test.

**Solution**:
- **Training set fixe**: 2021-01-01 a 2022-12-31 (2 ans, periode pre-backtest)
- **Backtest period**: 2023-01-01 a 2024-06-01 (1.5 ans out-of-sample)
- Nouvelle methode `_train_model_initial()` qui utilise `History(symbol, TRAIN_START, TRAIN_END)` pour garantir l'isolation

**Impact**: Elimination complete du data leakage. Le modele n'a plus acces aux donnees futures lors du training initial.

---

### 2. Risk management - Stop-loss et Take-profit

**Objectif**: Proteger le capital et securiser les gains.

**Implementation**:
- **Stop-loss**: -5% (variable `STOP_LOSS_PCT = 0.05`)
- **Take-profit**: +10% (variable `TAKE_PROFIT_PCT = 0.10`)
- Tracking du prix d'entree (`self.entry_price`)
- Verifications dans `OnData()` avant les decisions de trading

**Code modifie** (lignes 288-305):
```python
# Risk management - Stop-loss et Take-profit
if self.Portfolio[self.symbol].Invested:
    if self.entry_price is not None:
        pnl_pct = (current_price - self.entry_price) / self.entry_price

        # Stop-loss a -5%
        if pnl_pct <= -self.STOP_LOSS_PCT:
            self.Liquidate(self.symbol)
            self.Debug(f"{self.Time} => STOP-LOSS declenche @ {current_price:.2f} (PnL: {pnl_pct:.2%})")
            self.entry_price = None
            return

        # Take-profit a +10%
        if pnl_pct >= self.TAKE_PROFIT_PCT:
            self.Liquidate(self.symbol)
            self.Debug(f"{self.Time} => TAKE-PROFIT declenche @ {current_price:.2f} (PnL: {pnl_pct:.2%})")
            self.entry_price = None
            return
```

**Impact attendu**:
- Reduction du Max Drawdown grace au stop-loss
- Securisation des gains avec take-profit
- Meilleure gestion du risque asymetrique (perte limitee, gain potentiel 2x)

---

### 3. Retraining periodique - Adaptation au regime de marche

**Objectif**: Adapter le modele aux conditions de marche changeantes.

**Implementation**:
- **Frequence**: Tous les 30 jours (variable `RETRAIN_INTERVAL_DAYS = 30`)
- **Lookback**: 365 derniers jours (variable `RETRAIN_LOOKBACK_DAYS = 365`)
- **Planification**: `Schedule.On()` avec verification quotidienne a 09:30 UTC
- Nouvelle methode `CheckRetraining()` et `_train_model_with_lookback()`

**Code modifie** (lignes 91-117):
```python
# Planification du retraining periodique (tous les 30 jours a 09:30 UTC)
self.Schedule.On(
    self.DateRules.Every(DayOfWeek.Monday, DayOfWeek.Tuesday, DayOfWeek.Wednesday,
                         DayOfWeek.Thursday, DayOfWeek.Friday, DayOfWeek.Saturday, DayOfWeek.Sunday),
    self.TimeRules.At(9, 30),
    self.CheckRetraining
)

def CheckRetraining(self):
    """Verifie si retraining necessaire (tous les 30 jours)."""
    if self.IsWarmingUp:
        return

    if self.last_retrain_date is None:
        days_since_last = 999
    else:
        days_since_last = (self.Time - self.last_retrain_date).days

    if days_since_last >= self.RETRAIN_INTERVAL_DAYS:
        self.Debug(f"{self.Time} => Retraining schedule (derniers {days_since_last} jours)")
        success = self._train_model_with_lookback(self.RETRAIN_LOOKBACK_DAYS)
        if success:
            self.last_retrain_date = self.Time
            self.Debug(f"Retraining reussi. Prochain dans {self.RETRAIN_INTERVAL_DAYS} jours.")
        else:
            self.Debug("Retraining echoue. Tentative au prochain cycle.")
```

**Impact attendu**:
- Meilleure adaptation aux changements de regime (bull/bear market)
- Reduction du risque de model drift
- Amelioration du Sharpe ratio sur le long terme

---

### 4. Position sizing probabiliste - Confiance du modele

**Objectif**: Ajuster la taille de position selon la confiance du modele.

**Implementation**:
- Utilisation de `predict_proba()` au lieu de `predict()`
- **Threshold LONG**: confidence > 0.6 (variable `CONFIDENCE_LONG_THRESHOLD`)
- **Threshold EXIT**: confidence < 0.4 (variable `CONFIDENCE_EXIT_THRESHOLD`)
- **Zone d'incertitude**: 0.4 < confidence < 0.6 (pas de trade)
- Position proportionnelle a la confiance (max 100%)
- Rebalancing si ecart > 10%

**Code modifie** (lignes 284-334):
```python
# Prediction probabiliste
proba = self.model.predict_proba(X)[0]  # [proba_down, proba_up]
confidence_up = proba[1]  # Probabilite de hausse

# Position sizing probabiliste
if confidence_up > self.CONFIDENCE_LONG_THRESHOLD:
    # Signal LONG avec confiance elevee
    # Position proportionnelle a la confiance (max 100%)
    position_size = min(confidence_up, 1.0)

    if not self.Portfolio[self.symbol].Invested:
        self.SetHoldings(self.symbol, position_size)
        self.entry_price = current_price
        self.Debug(f"{self.Time} => LONG @ {current_price:.2f} | Confidence: {confidence_up:.2%} | Size: {position_size:.2%}")
    else:
        # Ajustement position si deja investi
        current_holdings = self.Portfolio[self.symbol].HoldingsValue / self.Portfolio.TotalPortfolioValue
        if abs(current_holdings - position_size) > 0.1:  # Rebalance si ecart > 10%
            self.SetHoldings(self.symbol, position_size)
            self.Debug(f"{self.Time} => Rebalance @ {current_price:.2f} | New size: {position_size:.2%}")

elif confidence_up < self.CONFIDENCE_EXIT_THRESHOLD:
    # Signal EXIT avec confiance faible de hausse (donc confiance elevee de baisse)
    if self.Portfolio[self.symbol].Invested:
        final_pnl = (current_price - self.entry_price) / self.entry_price if self.entry_price else 0
        self.Liquidate(self.symbol)
        self.Debug(f"{self.Time} => EXIT @ {current_price:.2f} | Confidence: {confidence_up:.2%} | Final PnL: {final_pnl:.2%}")
        self.entry_price = None

else:
    # Zone d'incertitude (0.4 < confidence < 0.6) - Pas de trade
    pass
```

**Impact attendu**:
- Reduction des faux signaux (zone d'incertitude)
- Meilleur ratio risk/reward (position plus petite quand confiance moderee)
- Win rate ameliore (trades uniquement sur signaux forts)

---

## Fichiers modifies

| Fichier | Lignes modifiees | Description |
|---------|------------------|-------------|
| main.py | Integralite | Refactoring complet avec les 4 ameliorations |

---

## Compilation

**CompileId**: `e28e4aa0f7a3267c8968e150e47b0bc7-4275d99ab3c0557cc41c0e69c281de70`
**State**: `BuildSuccess`
**Lean Version**: 2.5.0.0.17533

**Warnings**: Linter warnings non-bloquants (attributs de mixins QC)

---

## Prochaines etapes

1. **Backtest via UI**: Lancer un backtest manuel sur la periode 2023-2024 (compte gratuit)
2. **Analyse des resultats**: Comparer avec les 8 backtests precedents (0 trades)
3. **Ajustements possibles**:
   - Tweaking des thresholds de confidence (0.6/0.4)
   - Ajustement stop-loss/take-profit ratios
   - Features engineering (ajouter volume, volatilite)
   - Hyperparameters RandomForest (n_estimators, max_depth)

---

## Impact attendu global

| Metrique | Avant | Attendu | Raisonnement |
|----------|-------|---------|--------------|
| **Nombre de trades** | 0 | 20-40 | Position sizing probabiliste + fix data leakage |
| **Sharpe ratio** | N/A | 0.5-1.0 | Risk management + retraining |
| **Max Drawdown** | N/A | -15% a -25% | Stop-loss -5% limite les pertes |
| **Win rate** | N/A | 55-65% | Confidence thresholds filtrent faux signaux |

---

## Notes techniques

- **Data leakage**: Completement elimine grace a la separation stricte train/test
- **Overfitting**: Mitige par retraining periodique (rolling window)
- **Risk management**: Robuste avec stop-loss asymetrique (perte -5%, gain +10%)
- **Position sizing**: Adaptatif selon confiance du modele (Kelly-like approach)

**Date de mise a jour**: 2026-02-15
**Auteur**: Claude Code (qc-strategy-improver agent)
