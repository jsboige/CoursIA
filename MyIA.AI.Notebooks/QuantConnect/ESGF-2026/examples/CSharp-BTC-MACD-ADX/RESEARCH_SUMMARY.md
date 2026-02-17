# Research Summary: BTC-MACD-ADX Robustness Analysis

## Objectif

Valider la robustesse de la strategie BTC-MACD-ADX sur une periode etendue (2019-2025) et evaluer la valeur ajoutee de l'approche **adaptive ADX percentile** par rapport aux seuils fixes.

## Innovation Cle: Seuils ADX Adaptatifs

La strategie actuelle utilise des seuils ADX **dynamiques** calcules sur une fenetre glissante:

```csharp
// Seuils adaptatifs calcules sur 140 barres
var (medianAdx, q1Adx, q3Adx) = ComputeAdxPercentiles(_adxWindow);

// Entree: MACD bullish + ADX au-dessus du 86e percentile
if (adxValue >= q3Adx && isMacdBullish) {
    SetHoldings(_symbol, 1);
}

// Sortie: MACD bearish OU ADX en-dessous du 6e percentile
else if (adxValue < q1Adx && isMacdBearish) {
    Liquidate(_symbol);
}
```

### Avantages de l'approche adaptative

1. **Auto-calibration**: S'adapte automatiquement aux regimes de volatilite changeants
2. **Robustesse temporelle**: Pas de recalibration manuelle necessaire
3. **Context-aware**: Les seuils refletent les conditions recentes du marche

### Comparaison avec approche fixe

| Approche | Seuil Haut | Seuil Bas | Probleme |
|----------|------------|-----------|----------|
| **Fixe** | ADX > 25 | ADX < 15 | Rigide, ne s'adapte pas aux regimes |
| **Adaptative** | ADX > P86(140 bars) | ADX < P6(140 bars) | S'adapte aux conditions de marche |

## Hypotheses de Recherche

### H1: Stabilite de la fenetre adaptative

**Hypothese**: La fenetre de 140 barres reste stable sur 2019-2025

**Test**: Analyse de sensibilite sur windows [80, 100, 140, 180, 200]

**Validation**: Les parametres actuels (140, 6, 86) doivent figurer dans le top 3

### H2: MACD vs EMA Cross

**Hypothese**: MACD fournit des signaux de sortie plus precoces que simple EMA cross durant les crashes

**Test**: Comparaison performance MACD vs EMA(12/26) durant COVID crash (Mars 2020)

**Metrique**: Drawdown maximal durant la periode de crash

### H3: ADX Adaptatif vs Fixe

**Hypothese**: ADX adaptatif surperforme ADX fixe (>25) en termes de Sharpe ratio

**Test**: Backtest complet 2019-2025 avec 4 strategies:
1. MACD + ADX Adaptatif (strategie actuelle)
2. MACD + ADX Fixe (>25)
3. MACD seul
4. EMA Cross simple

**Validation**: Sharpe(Adaptatif) > Sharpe(Fixe) > Sharpe(MACD seul)

### H4: Walk-Forward Robustesse

**Hypothese**: Walk-forward validation confirme la robustesse des parametres

**Test**:
- Train: 252 jours (1 an)
- Test: 63 jours (3 mois)
- Step: 63 jours

**Metrique**: Walk-Forward Efficiency (WFE) = Sharpe(out-sample) / Sharpe(in-sample)

**Validation**: WFE > 60%

### H5: Complexite Justifiee

**Hypothese**: La complexite MACD+ADX est justifiee vs strategie EMA simple

**Test**: Comparaison Sharpe ratio, CAGR, Max DD, Win Rate

**Validation**: MACD+ADX > EMA simple d'au moins 10% en Sharpe

## Methodologie

### 1. Donnees

- **Source**: Yahoo Finance (BTC-USD comme proxy pour BTCUSDT)
- **Periode**: 2019-01-01 → 2026-02-17 (7+ annees)
- **Resolution**: Daily
- **Regimes identifies**:
  - Bear 2019
  - Bull 2019-2020
  - COVID Crash (Mars 2020)
  - COVID Recovery
  - Bull 2021
  - Correction 2021
  - Bear 2022
  - Sideways 2023
  - Bull 2024-2025

### 2. Indicateurs

**MACD (12, 26, 9)**:
```python
ema_fast = close.ewm(span=12).mean()
ema_slow = close.ewm(span=26).mean()
macd = ema_fast - ema_slow
signal = macd.ewm(span=9).mean()
histogram = macd - signal
```

**ADX (period=25)**:
```python
# Directional Movement
plus_dm = high.diff().where(lambda x: x > 0, 0)
minus_dm = -low.diff().where(lambda x: x > 0, 0)

# True Range
tr = max(high - low, |high - close[-1]|, |low - close[-1]|)

# Directional Indicators
atr = tr.rolling(25).mean()
plus_di = 100 * plus_dm.rolling(25).mean() / atr
minus_di = 100 * minus_dm.rolling(25).mean() / atr

# ADX
dx = 100 * |plus_di - minus_di| / (plus_di + minus_di)
adx = dx.rolling(25).mean()
```

**Seuils Adaptatifs**:
```python
lower_threshold = adx.rolling(140).quantile(0.06)
upper_threshold = adx.rolling(140).quantile(0.86)
```

### 3. Backtest Vectorise

**Logique d'entree**:
```python
position = 1 if (histogram > 0 and adx > adx_upper) else 0
```

**Logique de sortie**:
```python
position = 0 if (histogram < 0 or adx < adx_lower) else position
```

**Metriques calculees**:
- Sharpe Ratio (annualise, 365 jours)
- CAGR (Compound Annual Growth Rate)
- Max Drawdown
- Win Rate
- Nombre de trades

### 4. Analyse de Sensibilite

**Grid search** sur parametres ADX:
- Windows: [80, 100, 140, 180, 200]
- Percentiles: [(5, 85), (6, 86), (10, 90)]
- Total: 15 configurations

**Sortie**: Tableau classe par Sharpe ratio decroissant

### 5. Walk-Forward Validation

**Procedure**:
1. Train sur 252 jours
2. Optimiser parametres sur train (grid search reduit)
3. Tester parametres optimaux sur 63 jours suivants
4. Repeter avec fenetre glissante de 63 jours

**Metriques**:
- Sharpe moyen in-sample
- Sharpe moyen out-of-sample
- WFE = out-of-sample / in-sample

## Resultats Attendus

### Performance Actuelle (2021-04-09 → Now)

- **Sharpe**: 1.224
- **CAGR**: 38.1%
- **Max DD**: ~20% (estime)

### Performance Attendue (2019-01-01 → 2025-12-31)

- **Sharpe**: 0.8 - 1.0 (degradation due aux regimes bear 2019, 2022)
- **CAGR**: 25-30%
- **Max DD**: 30-40% (COVID crash + Bear 2022)

### Comparaison Strategies

**Ordre de performance attendu (Sharpe)**:
1. MACD + ADX Adaptatif: 0.9-1.0
2. MACD + ADX Fixe: 0.7-0.8
3. MACD seul: 0.6-0.7
4. EMA Cross: 0.5-0.6
5. Buy & Hold: N/A (reference)

### Walk-Forward Efficiency

- **WFE attendu**: 65-75% (signe de robustesse)
- **Periodes difficiles**: Bear 2022 (Sharpe test pourrait etre negatif)
- **Periodes favorables**: Bull 2021, 2024-2025

## Recommandations (Conditionnelles)

### Si H1, H3, H4 confirmees

**ACTION IMMEDIATE**:
```csharp
// Main.cs - Ligne 353
SetStartDate(2019, 1, 1);  // Etendre de 2021-04-09 a 2019-01-01
```

**Parametres a conserver**:
- MACD: (12, 26, 9) - standard, robuste
- ADX: period=25, window=140, percentiles=(6, 86)

### Si H1 refutee (parametres non optimaux)

**ACTION**: Ajuster selon resultats sensibilite

Exemple si meilleure config est (Window=180, P10-90):
```csharp
[Parameter("adx-window")]
public int AdxWindowPeriod = 180;  // au lieu de 140

[Parameter("adx-lower-percentile")]
public int AdxLowerPercentile = 10;  // au lieu de 6

[Parameter("adx-upper-percentile")]
public int AdxUpperPercentile = 90;  // au lieu de 86
```

### Si H3 refutee (ADX fixe meilleur)

**ACTION**: Simplifier la strategie

```csharp
// Remplacer approche adaptative par seuils fixes
if (adxValue >= 25 && isMacdBullish) {
    SetHoldings(_symbol, 1);
}
else if (adxValue < 15 && isMacdBearish) {
    Liquidate(_symbol);
}
```

### Si H5 refutee (complexite non justifiee)

**ACTION**: Revenir a EMA Cross simple

```csharp
// Strategie simplifiee
var emaFast = EMA(_symbol, 12, Resolution.Daily);
var emaSlow = EMA(_symbol, 26, Resolution.Daily);

if (emaFast > emaSlow && !Portfolio.Invested) {
    SetHoldings(_symbol, 1);
}
else if (emaFast < emaSlow && Portfolio.Invested) {
    Liquidate(_symbol);
}
```

## Execution du Notebook

### Prerequis

```bash
cd MyIA.AI.Notebooks/QuantConnect
python -m venv venv
venv\Scripts\activate
pip install pandas numpy yfinance matplotlib seaborn scipy
```

### Execution

```bash
cd ESGF-2026/examples/CSharp-BTC-MACD-ADX
python execute_research.py
```

### Sortie Attendue

Le notebook genere:
1. **Tableaux de comparaison** (4 strategies)
2. **Analyse de sensibilite** (15 configurations ADX)
3. **Walk-forward results** (10-15 periodes)
4. **Recommandations finales** basees sur les hypotheses validees

### Temps d'execution

- **Estime**: 3-5 minutes
- **Critique**: Walk-forward validation (grid search repete)

## Prochaines Etapes

### Si recherche concluante

1. **Compiler** la strategie mise a jour sur QuantConnect
2. **Lancer backtest** complet 2019-2025 via web UI
3. **Valider metriques** vs predictions du notebook
4. **Deployer** en paper trading si Sharpe > 0.8

### Si recherche non concluante

1. **Explorer alternatives**:
   - Bollinger Bands + RSI
   - Machine Learning (RandomForest sur features MACD+ADX)
   - Regime switching (HMM pour detecter bull/bear)
2. **Creer nouveau research notebook** pour approche alternative
3. **Iterer** jusqu'a trouver strategie robuste

## Notes Techniques

### Limitations

1. **Donnees**: Yahoo Finance peut avoir gaps vs Binance reel
2. **Frais**: Backtest vectorise ignore slippage/fees (assume 0.1% Binance)
3. **Execution**: Pas de simulation realiste des ordres (assume remplissage instantane)
4. **Capital**: Assume capital constant (pas de compounding exact)

### Differences QuantConnect vs Notebook

| Aspect | QuantConnect (C#) | Notebook (Python) |
|--------|-------------------|-------------------|
| Donnees | BTCUSDT Binance | BTC-USD Yahoo |
| Resolution | Daily bars | Daily bars |
| Frais | Binance model | Non simule |
| Warmup | 500 jours | Inclus dans donnees |
| Execution | Event-driven | Vectorise |

**Conclusion**: Les resultats notebook sont une **approximation** des vrais resultats QuantConnect. La validation finale doit se faire via backtest cloud QuantConnect.

---

**Notebook cree**: `research_robustness.ipynb`

**Execution**: En cours...

**Auteur**: Claude Opus 4.6 (qc-research-notebook agent)

**Date**: 2026-02-17
