# Analyse Projet BTC-MachineLearning (ID: 21047688)

**Date**: 2026-02-15
**Statut**: COMPILATION OK - NEEDS_BACKTEST
**Compilation**: BuildSuccess (warnings linter non-bloquants)
**Backtests**: 0 (historique supprime ou inexistant)

---

## 1. Synchronisation Cloud vs Local

### Fichiers Cloud (via MCP)
| Fichier | Taille | Dernière modification | Statut |
|---------|--------|----------------------|---------|
| `main.py` | ~6.4 KB | 2026-02-13 15:32:37 | Entrainement in-situ present |
| `main-simple.py` | ~2.5 KB | 2025-04-22 00:45:54 | Version simple ObjectStore-dependent |
| `research.ipynb` | ~8.9 KB | 2025-04-22 00:45:54 | Notebook d'entrainement enhanced |
| `research-simple.ipynb` | ~5.4 KB | 2025-04-22 00:45:54 | Notebook d'entrainement simple |

### Fichiers Locaux
| Fichier | Lignes | Description |
|---------|--------|-------------|
| `main.py` | 158 | Version identique au cloud (entrainement in-situ) |
| `main-simple.py` | 49 | Version simple dependante ObjectStore |
| `README.md` | 19 | Documentation architecture |

### Verdict: SYNCHRONISE
Le fichier `main.py` cloud contient bien les corrections d'entrainement in-situ ajoutées le 2026-02-13. Les fichiers locaux sont à jour.

---

## 2. Compilation

### Résultat: BuildSuccess
```
CompileID: 31be4cd5996ad99c05fea09708412632-1e7a85597ab7b40023b38c598067a842
State: BuildSuccess
Lean Version: 2.5.0.0.17533
```

### Warnings (non-bloquants)
Les warnings de type `"MyEnhancedCryptoMlAlgorithm" has no attribute "SetStartDate"` sont des faux positifs du linter Python - QCAlgorithm herite ces methodes de la classe parente (AlgorithmImports).

### Signature
```
signatureOrder: ["project/main.py", "project/main-simple.py"]
```
Les deux fichiers sont compiles. La classe active est `MyEnhancedCryptoMlAlgorithm` (main.py).

---

## 3. Architecture de la Strategie ML

### 3.1 Version Enhanced (main.py)

#### Configuration
- **Periode**: 2023-01-01 à 2024-01-01 (1 an)
- **Capital**: 100,000 USDT
- **Actif**: BTCUSDT (Binance, Daily)
- **Modele**: RandomForestClassifier (100 trees, max_depth=5)

#### Features (9 indicateurs)
| Indicateur | Période | Type | Description |
|------------|---------|------|-------------|
| SMA | 20 | Trend | Simple Moving Average |
| RSI | 14 | Momentum | Relative Strength Index |
| DailyReturn | 1 | Return | (Close_t - Close_t-1) / Close_t-1 |
| EMA_10 | 10 | Trend | Exponential Moving Average |
| EMA_20 | 20 | Trend | Exponential Moving Average |
| EMA_50 | 50 | Trend | Exponential Moving Average |
| EMA_200 | 200 | Trend | Exponential Moving Average |
| ADX | 14 | Trend Strength | Average Directional Index |
| ATR | 14 | Volatility | Average True Range |

#### Entrainement In-Situ
```python
def _train_model_insitu(self):
    training_days = 365
    history = self.History(self.symbol, training_days, Resolution.Daily)
    # Construction X_train, y_train sur 365 jours historiques
    self.model = RandomForestClassifier(n_estimators=100, max_depth=5, random_state=42)
    self.model.fit(X_train, y_train)
```

**Avantages**:
- Pas de dépendance ObjectStore (evite l'erreur "model key not found")
- S'adapte automatiquement aux donnees disponibles
- Entrainement sur 365 jours d'historique

**Inconvenients**:
- Consomme du temps de warm-up (warmup = 200 + 14 = 214 jours)
- Entrainement sur donnees in-sample (risque d'overfitting)

#### Logique de Trading
```python
pred = self.model.predict(X)[0]
if pred == 1:  # Prévision hausse
    if not self.Portfolio[self.symbol].Invested:
        self.SetHoldings(self.symbol, 1.0)  # 100% BTC
else:  # Prévision baisse
    if self.Portfolio[self.symbol].Invested:
        self.Liquidate(self.symbol)  # 100% USDT
```

**Stratégie**: Long-only, all-in ou all-out. Pas de position short, pas de sizing.

---

### 3.2 Version Simple (main-simple.py)

#### Configuration
- **Periode**: 2022-01-01 à 2023-01-01
- **Features**: 3 (SMA20, RSI14, DailyReturn)
- **Modele**: Chargé depuis ObjectStore (`myCryptoMlModel.pkl`)

**Critique**: Cette version echoue si le modele n'a pas été pré-entrainé via le notebook `research-simple.ipynb`.

---

## 4. Problèmes Identifies

### 4.1 Aucun Backtest Existant
L'API retourne `"backtests": [], "count": 0`. Les 8 backtests mentionnés dans la mémoire ont été supprimés ou n'ont jamais existé.

**Action requise**: Lancer un nouveau backtest via l'UI web (l'API `create_backtest` requiert un compte payant).

### 4.2 Risque d'Overfitting (Entrainement In-Situ)
Le modèle s'entraine sur 365 jours d'historique, puis trade sur la même période (2023). Cela crée une **fuite de données** (data leakage).

**Solution**:
- Entrainer sur 2021-2022 (hors-sample)
- Backtester sur 2023-2024
- Utiliser une fenêtre glissante (rolling window) pour re-entrainer périodiquement

### 4.3 Features Calculées Manuellement
Les fonctions `_ema()`, `_compute_rsi()`, `_compute_adx()` réimplémentent des indicateurs existants dans QC. Cela introduit des divergences potentielles avec les indicateurs natifs utilisés dans `OnData()`.

**Solution**: Utiliser l'historique des indicateurs QC plutôt que de recalculer manuellement.

### 4.4 Stratégie All-In / All-Out
Le sizing est binaire (100% BTC ou 100% USDT). Cela amplifie la volatilité et le drawdown.

**Solution**: Ajouter du position sizing basé sur la confiance du modèle (`predict_proba()`).

---

## 5. Propositions d'Amelioration

### 5.1 Corriger le Data Leakage (HAUTE PRIORITE)

#### Problème
```python
# Entrainement sur 365 jours AVANT la date de début du backtest
training_days = 365
history = self.History(self.symbol, training_days, Resolution.Daily)
# Mais si START_DATE = 2023-01-01, l'historique va de 2022-01-01 à 2023-01-01
# Puis le backtest trade sur 2023-2024 => le modèle "voit" des données futures !
```

#### Solution
```python
# Dans Initialize():
TRAIN_START = datetime(2021, 1, 1)
TRAIN_END   = datetime(2022, 12, 31)  # 2 ans d'entrainement
BACKTEST_START = datetime(2023, 1, 1)
BACKTEST_END   = datetime(2024, 1, 1)  # 1 an de test hors-sample

def _train_model_insitu(self):
    history = self.History(self.symbol, TRAIN_START, TRAIN_END, Resolution.Daily)
    # Construire X_train, y_train sur 2021-2022
```

**Impact attendu**: Sharpe plus réaliste (probablement plus bas, mais moins biaisé).

---

### 5.2 Ajouter Position Sizing Probabiliste (MOYENNE PRIORITE)

#### Problème
Le modèle prédit seulement UP/DOWN (classification binaire), mais ne donne pas de confiance.

#### Solution
```python
# Utiliser predict_proba() au lieu de predict()
proba = self.model.predict_proba(X)[0]
confidence_up = proba[1]  # Probabilité de hausse

if confidence_up > 0.6:  # Haute confiance hausse
    target_weight = min(1.0, (confidence_up - 0.5) * 2)  # 0.6 -> 0.2, 0.75 -> 0.5, 1.0 -> 1.0
    self.SetHoldings(self.symbol, target_weight)
elif confidence_up < 0.4:  # Haute confiance baisse
    self.Liquidate(self.symbol)
# Sinon (0.4 < proba < 0.6), ne rien faire (flat)
```

**Impact attendu**: Sharpe +0.1 à +0.3, drawdown -5% à -10%.

---

### 5.3 Enrichir les Features avec des Signaux de Regime (MOYENNE PRIORITE)

#### Problème
Les features actuelles sont toutes des indicateurs de prix. Le modèle manque de contexte de marché (bull/bear/sideways).

#### Solution
Ajouter des features de regime:
```python
# 1. Volatility regime
vol_20 = np.std(closes[-20:]) / np.mean(closes[-20:])  # Coefficient de variation

# 2. Trend strength
ema_slope = (ema_50 - closes[-50]) / 50  # Pente de l'EMA 50

# 3. Cross-EMAs
ema_cross = 1 if ema_10 > ema_20 else 0  # Golden cross / death cross

# 4. Volume anomaly (si disponible)
vol_ratio = volume / volume_ma_20

features = [sma_20, rsi_14, daily_ret, ema_10, ema_20, ema_50, ema_200, adx_val, atr_val,
            vol_20, ema_slope, ema_cross]  # +3 features
```

**Impact attendu**: Accuracy +2% à +5%, Sharpe +0.05 à +0.15.

---

### 5.4 Tester d'Autres Modeles (BASSE PRIORITE)

#### Problème
RandomForest (max_depth=5) est un modèle linéaire peu profond. Il peut sous-apprendre (underfitting).

#### Solution
Tester dans le notebook `research.ipynb`:
```python
# 1. RandomForest plus profond
RandomForestClassifier(n_estimators=200, max_depth=10, min_samples_split=10)

# 2. XGBoost (gradient boosting)
import xgboost as xgb
model = xgb.XGBClassifier(n_estimators=100, max_depth=5, learning_rate=0.1)

# 3. LightGBM (plus rapide que XGBoost)
import lightgbm as lgb
model = lgb.LGBMClassifier(n_estimators=100, max_depth=5, learning_rate=0.1)

# 4. Neural Network (si beaucoup de données)
from sklearn.neural_network import MLPClassifier
model = MLPClassifier(hidden_layer_sizes=(64, 32), max_iter=500)
```

**Impact attendu**: Variable selon le modèle. XGBoost souvent meilleur que RF (+0.1 à +0.2 Sharpe).

---

### 5.5 Ajouter du Re-Training Periodique (HAUTE PRIORITE)

#### Problème
Le modèle est entrainé une seule fois au début du backtest. Il ne s'adapte pas aux changements de régime.

#### Solution
```python
def Initialize(self):
    self.retrain_frequency = 30  # Re-entrainer tous les 30 jours
    self.days_since_train = 0
    self.Schedule.On(
        self.DateRules.EveryDay(self.symbol),
        self.TimeRules.At(0, 0),
        self._check_retrain
    )

def _check_retrain(self):
    self.days_since_train += 1
    if self.days_since_train >= self.retrain_frequency:
        self._train_model_insitu()
        self.days_since_train = 0
        self.Debug(f"Modele re-entraine le {self.Time}")
```

**Impact attendu**: Sharpe +0.1 à +0.3, adaptation aux nouveaux regimes.

---

### 5.6 Ajouter des Stop-Loss et Take-Profit (HAUTE PRIORITE)

#### Problème
La strategie actuelle n'a aucun risk management. Une prediction erronee peut causer un gros drawdown.

#### Solution
```python
def OnData(self, slice):
    # ... (prediction du modele)

    if pred == 1:
        if not self.Portfolio[self.symbol].Invested:
            self.SetHoldings(self.symbol, 1.0)
            entry_price = current_price
            # Stop-loss à -5%
            self.StopMarketOrder(self.symbol, -self.Portfolio[self.symbol].Quantity, entry_price * 0.95)
            # Take-profit à +10%
            self.LimitOrder(self.symbol, -self.Portfolio[self.symbol].Quantity, entry_price * 1.10)
```

**Impact attendu**: Drawdown -10% à -20%, Win Rate +5% à +10%.

---

## 6. Plan d'Action Priorise

| # | Amelioration | Impact Attendu | Effort | Priorite |
|---|--------------|----------------|--------|----------|
| 1 | Corriger data leakage (train 2021-2022, test 2023) | Sharpe realiste | LOW | **HAUTE** |
| 2 | Ajouter stop-loss/take-profit (-5% / +10%) | DD -15% | LOW | **HAUTE** |
| 3 | Ajouter re-training periodique (30 jours) | Sharpe +0.2 | MEDIUM | **HAUTE** |
| 4 | Position sizing probabiliste (predict_proba) | Sharpe +0.15, DD -8% | MEDIUM | MOYENNE |
| 5 | Enrichir features (vol regime, EMA slope, crosses) | Accuracy +3%, Sharpe +0.1 | MEDIUM | MOYENNE |
| 6 | Tester XGBoost/LightGBM | Sharpe +0.1 | MEDIUM | BASSE |

---

## 7. Execution Immediate

### Etape 1: Lancer un Backtest Initial (via UI web)
Aller sur https://www.quantconnect.com/project/21047688 et lancer un backtest manuel pour obtenir une baseline de performance.

### Etape 2: Implementer les Ameliorations HAUTE PRIORITE
Modifier `main.py` pour:
1. Separer train (2021-2022) et test (2023)
2. Ajouter stop-loss/take-profit
3. Ajouter re-training periodique

### Etape 3: Comparer les Resultats
Backtester la version amelioree et comparer:
- Sharpe Ratio
- Max Drawdown
- Win Rate
- Net Profit
- Nombre de trades

---

## 8. Metriques Cibles

| Metrique | Valeur Actuelle | Cible Amelioree | Cible Excellente |
|----------|----------------|-----------------|------------------|
| Sharpe Ratio | Inconnu (0 backtests) | > 0.3 | > 0.8 |
| Max Drawdown | Inconnu | < 30% | < 15% |
| Win Rate | Inconnu | > 50% | > 60% |
| Trades | Inconnu | > 50 | > 100 |
| Net Profit | Inconnu | > 0% | > 20% |
| CAGR | Inconnu | > 5% | > 15% |

---

## 9. Risques et Limitations

### 9.1 Data Quality
Les donnees Binance BTCUSDT Daily peuvent contenir des gaps (weekends, maintenances). Le modele doit gerer les donnees manquantes.

### 9.2 Overfitting Risk
Avec 9 features et un RandomForest de 100 arbres, le modele peut overfit sur les donnees d'entrainement. Utiliser la cross-validation dans le notebook.

### 9.3 Regime Change
BTC a connu 3 regimes distincts:
- 2021: Bull market (ATH $69k)
- 2022: Bear market (crash -70%)
- 2023-2024: Recovery

Un modele entraine sur 2021-2022 peut mal performer sur 2023+ si les regimes sont trop differents.

### 9.4 Transaction Costs
Binance facture ~0.1% par trade. Avec un all-in/all-out, cela peut eroder les profits. Ajouter un `slippage_model` dans le backtest.

---

## 10. Conclusion

### Statut Actuel: COMPILATION OK - NEEDS_BACKTEST
Le projet compile sans erreur. Le code cloud contient bien l'entrainement in-situ (correction appliquee le 2026-02-13).

### Bloqueur: Aucun Backtest Disponible
Impossible de diagnostiquer la performance sans backtests. **Action immediate**: Lancer un backtest manuel via l'UI web.

### Problemes Principaux
1. **Data leakage** (entrainement sur donnees in-sample)
2. **Pas de risk management** (stop-loss/take-profit)
3. **Pas de re-training** (modele statique)

### Potentiel d'Amelioration: ELEVE
Avec les ameliorations proposees (surtout #1, #2, #3), le Sharpe peut passer de ~0 à >0.5.

### Prochaines Etapes
1. Lancer backtest initial (via UI web)
2. Implementer ameliorations HAUTE PRIORITE
3. Backtester et comparer
4. Iterer sur les ameliorations MOYENNE/BASSE PRIORITE
