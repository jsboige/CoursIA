# ESGF 2026 - Trading Algorithmique avec QuantConnect

Workspace ESGF pour l'annee scolaire 2025-2026.
Sponsorise par Jared Broad (CEO QuantConnect) via le tier "Trading Firm".

**Organisation** : Trading Firm ESGF (`94aa4bcb...`)
**Professeur** : jsboige@gmail.com (User ID: 46613)
**Credit** : 3457.87 QCC

---

## Structure

```
ESGF-2026/
├── examples/           # 11 projets d'exemples du professeur (recuperes du cloud QC)
│   ├── Crypto-MultiCanal/       # Detecteur hierarchique multi-canaux (Python)
│   ├── ETF-Pairs-Trading/       # Pairs trading ETF avec co-integration (Python)
│   ├── Sector-Momentum/         # Momentum sectoriel dual + Alpha Framework (Python)
│   ├── Trend-Following/         # Multi-oracles MACD/RSI/Bollinger + ATR trailing (Python)
│   ├── BTC-MachineLearning/     # ML sur BTC (RandomForest/SVC/XGBoost) (Python)
│   ├── Multi-Layer-EMA/         # EMA crossover multi-crypto (Python)
│   ├── Options-VGT/             # Vente de PUTs OTM sur tech (Python)
│   ├── Option-Wheel-Strategy/   # Wheel strategy (PUT selling -> covered CALL) (Python)
│   ├── CSharp-BTC-MACD-ADX/     # BTC MACD+ADX journalier (C#)
│   ├── CSharp-BTC-EMA-Cross/    # EMA crossover classique BTC (C#)
│   └── CSharp-CTG-Momentum/     # Stocks on the Move - Momentum ranking (C#)
├── templates/          # Templates pour projets etudiants
│   ├── starter/        # Niveau debutant
│   ├── intermediate/   # Niveau intermediaire
│   └── advanced/       # Niveau avance
└── archive-2025/       # Projets etudiants 2024-2025 archives
```

---

## Exemples du professeur

### Python - Strategies Crypto

| Projet | Cloud ID | Description | Fichiers |
|--------|----------|-------------|----------|
| **Crypto-MultiCanal** | 22298373 | Detecteur hierarchique multi-canaux avec pivots ZigZag, canaux Macro/Meso/Micro, signaux breakout/bounce, parametres optimises par GA | main.py (54K), fix_ipynb_quotes.py, research.ipynb, research_archive.ipynb |
| **BTC-MachineLearning** | 21047688 | ML sur BTC avec 9 features (SMA, RSI, EMA, ADX, ATR), modeles RandomForest/SVC/XGBoost persistes dans ObjectStore | main.py, main-simple.py |
| **Multi-Layer-EMA** | 20216947 | Trading BTC/ETH/LTC avec EMA crossover, filtre RSI, trailing stop 8%, take profit 30% | main.py |

### Python - Strategies Actions/ETF

| Projet | Cloud ID | Description | Fichiers |
|--------|----------|-------------|----------|
| **ETF-Pairs-Trading** | 19865767 | Pairs trading ETF avec test de co-integration Engle-Granger, z-score, trailing stop 8% | main.py, alpha.py, portfolio.py, risk.py, universe.py, utils.py |
| **Sector-Momentum** | 20216980 | Momentum dual sectoriel sur SPY universe (top 200), Risk Parity PCM, leverage 2x | main.py, DualMomentumAlphaModel.py, MyPcm.py, CustomImmediateExecutionModel.py, FredRate.py |
| **Trend-Following** | 20216930 | Multi-oracles (MACD, RSI, Bollinger, EMA 50/200, ADX, OBV), detection HH/HL/LL/LH, ATR trailing stop | main.py, alpha.py (22K), trendCalculator.py, macd_oracle.py, rsi_oracle.py, bollinger_oracle.py |

### Python - Strategies Options

| Projet | Cloud ID | Description | Fichiers |
|--------|----------|-------------|----------|
| **Options-VGT** | 21113806 | Vente de PUTs OTM sur 5 valeurs tech (NVDA, ORCL, CSCO, AMD, QCOM) avec seuils OTM par action | main.py |
| **Option-Wheel-Strategy** | 20216898 | Wheel strategy sur SPY : PUT selling -> assignment -> covered CALL, variantes cash-secured et margin | main.py + 4 variantes |

### C# - Strategies

| Projet | Cloud ID | Description | Fichiers |
|--------|----------|-------------|----------|
| **CSharp-BTC-MACD-ADX** | 19898232 | BTC MACD+ADX journalier sur Binance Cash, base du detecteur hierarchique | Main.cs, Research.ipynb |
| **CSharp-BTC-EMA-Cross** | 19050970 | Crossover EMA 18/23 classique sur BTC, 600K USDT | Main.cs |
| **CSharp-CTG-Momentum** | 19225388 | "Stocks on the Move" (Clenow) - Momentum ranking sur ETF OEF, indicateurs custom (AnnualizedSlope, Gap, MarketRegime), ATR position sizing | Main.cs + 4 indicateurs custom |

---

## Concepts pedagogiques couverts

### Niveau 1 - Fondations
- **EMA Crossover** : CSharp-BTC-EMA-Cross, Multi-Layer-EMA
- **MACD + ADX** : CSharp-BTC-MACD-ADX
- **Options basiques** : Options-VGT

### Niveau 2 - Intermediaire
- **Alpha Framework QC** : ETF-Pairs-Trading, Sector-Momentum
- **Multi-indicateurs** : Trend-Following (7+ indicateurs combines)
- **Wheel Strategy** : Option-Wheel-Strategy
- **Machine Learning** : BTC-MachineLearning

### Niveau 3 - Avance
- **Detecteur hierarchique** : Crypto-MultiCanal (canaux multi-echelles, GA optimization)
- **Indicateurs custom C#** : CSharp-CTG-Momentum (WindowIndicator, TradeBarIndicator)
- **Co-integration** : ETF-Pairs-Trading (Engle-Granger, z-score)

---

## Configuration MCP QuantConnect

Le workspace est pilotable depuis Claude Code via le MCP `qc-mcp` :

```json
"qc-mcp": {
  "command": "docker",
  "args": ["run", "-i", "--rm", "--platform", "linux/amd64",
    "-e", "QUANTCONNECT_USER_ID=46613",
    "-e", "QUANTCONNECT_API_TOKEN=***",
    "-e", "AGENT_NAME=claude-code-coursia",
    "quantconnect/mcp-server"]
}
```

### Commandes utiles

```
# Lister les projets
list_projects

# Lire un fichier projet
read_file(model: {projectId: 22298373, name: "main.py"})

# Compiler un projet
create_compile(model: {projectId: 22298373})

# Lancer un backtest
create_backtest(model: {projectId: 22298373, backtestName: "test-2026"})
```

---

## Notebooks d'accompagnement

27 notebooks Python progressifs dans `../Python/` (QC-Py-01 a QC-Py-27) couvrant :

1. **Setup** : Compte, IDE, premier algorithme
2. **Fondations** : API, Resolution, Consolidators, QuantBook
3. **Indicateurs** : MACD, RSI, Bollinger, EMA, Stochastique
4. **Strategies** : Mean Reversion, Momentum, Pairs Trading, Options
5. **Framework** : Alpha, Portfolio Construction, Risk, Execution, Universe
6. **ML/AI** : Features, modeles, ObjectStore, RL, NLP
7. **Production** : Paper trading, live, monitoring, multi-asset
8. **Competition** : Quant League / Strategies

---

## Resultats de Backtest (Fevrier 2026)

Compilation : **11/11 projets compilent avec succes** (0 erreurs, warnings non-bloquants uniquement).

### Tableau des metriques (meilleur backtest par projet)

| # | Projet | Periode | Return | CAGR | Sharpe | Max DD | Trades | Win Rate | Statut |
|---|--------|---------|--------|------|--------|--------|--------|----------|--------|
| 1 | **Option-Wheel-Strategy** | 2020-06 / 2024-09 | +68.5% | 12.9% | 0.996 | 7.4% | 91 | 94% | HEALTHY |
| 2 | **CSharp-BTC-EMA-Cross** | 2021-10 / 2024-12 | +166.7% | 36.2% | 1.094 | 40.7% | 7 | 67% | HEALTHY |
| 3 | **CSharp-BTC-MACD-ADX** | 2013-04 / 2024-12 | +4239.2% | 38.1% | 1.224 | 48.8% | 19 | 78% | HEALTHY |
| 4 | **Multi-Layer-EMA** | 2020-01 / 2024-01 | +2292.2% | 120.9% | 1.891 | 54.4% | 663 | 37% | HEALTHY |
| 5 | **Sector-Momentum** | 2024-01 / 2024-07 | +32.2% | 66.1% | 2.530 | 5.6% | 1300 | 60% | HEALTHY |
| 6 | **Options-VGT** | 2023-12 / 2025-01 | +28.3% | 25.3% | 0.892 | 15.6% | 25 | 71% | HEALTHY |
| 7 | **Trend-Following** | 2020-06 / 2020-09 | +24.5% | 136.0% | 2.157 | 20.5% | 809 | 68% | HEALTHY |
| 8 | **CSharp-CTG-Momentum** | 2021-01 / 2024-11 | +87.3% | 17.7% | 0.507 | 36.1% | 170 | 64% | HEALTHY |
| 9 | **ETF-Pairs-Trading** | 2020-01 / 2024-03 | -14.6% | -3.7% | -0.759 | 19.8% | 304 | 50% | BROKEN |
| 10 | **Crypto-MultiCanal** | 2024-01 / 2025-01 | 0% | 0% | 0 | 0% | 0 | 0% | BROKEN |
| 11 | **BTC-MachineLearning** | -- | -- | -- | -- | -- | 0 | -- | NO_DATA |

**Legende** : HEALTHY (Sharpe > 0.5) | NEEDS_IMPROVEMENT (Sharpe 0-0.5) | BROKEN (Sharpe < 0 ou 0 trades) | NO_DATA (pas de backtest)

### Ameliorations appliquees (Phase 3 - Fevrier 2026)

| Projet | Amelioration | Commit |
|--------|-------------|--------|
| **Multi-Layer-EMA** | Filtre Bollinger band, RSI resserre (35-70), sortie death cross + RSI>75 | c2b9cb3 |
| **ETF-Pairs-Trading** | Remplacement `arch` par `statsmodels.tsa.stattools.coint`, hedge ratio OLS numpy | c2b9cb3 |
| **BTC-MachineLearning** | Entrainement RandomForest in-situ si modele ObjectStore absent | c2b9cb3 |
| **Trend-Following** | Fix `self.algo = self` -> `self.algo = algo` dans alpha.py | 801afdb |
| **ETF-Pairs-Trading** | Ajout `Schedule.On` pour `RebalancePairs` | 801afdb |
| **Options-VGT** | Reecriture logique multi-equity (local only, projet etudiant) | 801afdb |
| **Crypto-MultiCanal** | Ajout `import traceback`, lookback 1000->500, fix CalculateOrderQuantity | en cours |

### Notes sur les projets BROKEN

- **ETF-Pairs-Trading** : Return negatif (-14.6%) malgre Sharpe decent en intra. Remplacement `arch` par `statsmodels` effectue, nouveau backtest necessaire.
- **Crypto-MultiCanal** : Runtime error dans le dernier backtest (0 trades). Corrections critiques en cours de push au cloud (import traceback, lookback, sizing).
- **BTC-MachineLearning** : Aucun backtest existant. Entrainement in-situ ajoute, premier backtest a lancer.

---

## Notes pour 2026

- La **Quant League** classique est terminee (Q4-2025)
- Transition vers le format **"Strategies"** en 2026
- A confirmer avec Jared Broad lors du prochain echange
- Les etudiants devront participer au format competitif QC en echange du sponsoring
