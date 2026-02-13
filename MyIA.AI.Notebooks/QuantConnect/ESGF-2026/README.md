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

## Notes pour 2026

- La **Quant League** classique est terminee (Q4-2025)
- Transition vers le format **"Strategies"** en 2026
- A confirmer avec Jared Broad lors du prochain echange
- Les etudiants devront participer au format competitif QC en echange du sponsoring
