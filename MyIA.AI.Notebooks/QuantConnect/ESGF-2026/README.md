# ESGF 2026 - Trading Algorithmique avec QuantConnect

Workspace ESGF pour l'annee scolaire 2025-2026.
Sponsorise par Jared Broad (CEO QuantConnect) via le tier "Trading Firm".

**Organisation** : Trading Firm ESGF (`94aa4bcb...`)
**Professeur** : <email> (User ID: 46613)
**Credit** : <solde QCC>

---

## 🎓 Inscription Étudiants

### Processus d'inscription au cours ESGF

Pour participer au cours ESGF 2026 et bénéficier du sponsoring QuantConnect (Trading Firm tier), suivez ces étapes :

1. **Créer un compte QuantConnect gratuit**
   - Allez sur [quantconnect.com](https://www.quantconnect.com)
   - Inscrivez-vous avec votre **email scolaire** (recommandé pour identification étudiante)
   - Validez votre adresse email

2. **Envoyer votre identifiant QuantConnect au professeur**
   - Une fois inscrit, votre compte QuantConnect a un username (ex: `john.doe`)
   - Envoyez ce username par email au professeur : `<email>`
   - Le professeur vous ajoutera à l'organisation ESGF sponsorisée

3. **Accès à l'organisation sponsorisée**
   - Une fois ajouté, vous verrez l'organisation "Trading Firm ESGF" dans votre compte
   - Le code education `education2025` est appliqué automatiquement au niveau de l'organisation
   - Vous bénéficiez du tier "Trading Firm" (plus de CPU, backtests illimités, etc.)

4. **Commencer les exercices**
   - Suivez les notebooks QC-Py-01 à QC-Py-04 (prérequis)
   - Passez aux exercices ESGF dans `ESGF_EXERCISES.md`
   - Utilisez les templates dans `templates/` comme point de départ

### Workflow Cloud-First

**Important** : Ce cours utilise une approche **cloud-first**. Tout le développement se fait sur QuantConnect Cloud (QC Lab), pas en local avec LEAN CLI.

- **Avantages** : Pas d'installation locale, accès aux données historiques QC, compilation instantanée
- **Local** : Le dossier `lean-workspace/` contient un seul exemple (`Multi-Layer-EMA-Researcher`) pour illustrer le workflow local, mais les étudiants travaillent sur le cloud
- **Projets** : Créez vos projets directement dans QuantConnect Lab, puis clonez-les localement si nécessaire pour versioning

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

## Strategies Researcher (org personnelle, Mars 2026)

10 strategies supplementaires deployees sur le cloud QC (org personnelle `d600793e...`) pour exploration et backtesting agentique. Couvrent des classes d'actifs et concepts complementaires aux exemples ESGF.

### ETF / Actions

| Projet | Cloud ID | Description | Sharpe | CAGR | Max DD |
|--------|----------|-------------|--------|------|--------|
| **Sector-Momentum-Researcher** | 28433643 | Dual momentum SPY/TLT/GLD, composite multi-lookback, SMA200 filter | **0.554** | 13.1% | 23.0% |
| **FamaFrench-Researcher** | 28657910 | Factor ETF rotation (VLUE/MTUM/SIZE/QUAL/USMV), risk parity weighting | **0.365** | 8.7% | 31.1% |
| **MomentumStrategy-Researcher** | 28657837 | Rotation momentum 11 ETFs sectoriels (XLK-XLC), top 3, SMA200 filter | 0.216 | 6.5% | 29.9% |
| **AllWeather-Researcher** | 28657833 | Portfolio Ray Dalio (SPY 30%/TLT 40%/IEF 15%/GLD 7.5%/DBC 7.5%), rebalancement trimestriel | 0.25 | 5.9% | 23.5% |
| **MeanReversion-Researcher** | 28657904 | RSI mean reversion long-only, universe top 100, SMA200 regime filter | -0.042 | 0.7% | 46.5% |

### Options

| Projet | Cloud ID | Description | Sharpe | CAGR | Max DD |
|--------|----------|-------------|--------|------|--------|
| **OptionsIncome-Researcher** | 28657838 | Covered Call sur SPY (Minute), delta 0.30, roll a 7 jours | 0.288 | 9.6% | 4.0% |

### Futures / Macro

| Projet | Cloud ID | Description | Sharpe | CAGR | Max DD |
|--------|----------|-------------|--------|------|--------|
| **FuturesTrend-Researcher** | 28657834 | Donchian breakout E-mini S&P 500, ATR trailing stop | 0.019 | 2.1% | 31.9% |
| **TurnOfMonth-Researcher** | 28657905 | Anomalie calendaire (J-4 a J+4), SPY+QQQ 1.5x, SMA200 filter | 0.127 | 4.8% | 23.7% |

### Forex / Volatilite

| Projet | Cloud ID | Description | Sharpe | CAGR | Max DD |
|--------|----------|-------------|--------|------|--------|
| **ForexCarry-Researcher** | 28657908 | FX momentum G7 (EURUSD, GBPUSD, etc.), SPY SMA200 risk-off | -1.80 | -0.7% | 9.5% |
| **VIX-TermStructure-Researcher** | 28657907 | Contango/backwardation VIX via VIXY/SVXY, trailing stop 8% | -0.97 | -1.1% | 20.8% |

---

## Concepts pedagogiques couverts

### Niveau 1 - Fondations
- **EMA Crossover** : CSharp-BTC-EMA-Cross, Multi-Layer-EMA
- **MACD + ADX** : CSharp-BTC-MACD-ADX
- **Options basiques** : Options-VGT
- **Anomalie calendaire** : TurnOfMonth-Researcher (saisonnalite, EMH)

### Niveau 2 - Intermediaire
- **Alpha Framework QC** : ETF-Pairs-Trading, Sector-Momentum
- **Multi-indicateurs** : Trend-Following (7+ indicateurs combines)
- **Wheel Strategy** : Option-Wheel-Strategy
- **Machine Learning** : BTC-MachineLearning
- **Multi-Asset / Risk Parity** : AllWeather-Researcher (Ray Dalio)
- **Momentum sectoriel** : MomentumStrategy-Researcher (rotation ETF)
- **Factor Investing** : FamaFrench-Researcher (Fama-French via ETFs)
- **Mean Reversion** : MeanReversion-Researcher (RSI contrarian)
- **Covered Call** : OptionsIncome-Researcher (premium income)

### Niveau 3 - Avance
- **Detecteur hierarchique** : Crypto-MultiCanal (canaux multi-echelles, GA optimization)
- **Indicateurs custom C#** : CSharp-CTG-Momentum (WindowIndicator, TradeBarIndicator)
- **Co-integration** : ETF-Pairs-Trading (Engle-Granger, z-score)
- **Volatilite** : VIX-TermStructure-Researcher (contango, structure a terme)
- **Forex** : ForexCarry-Researcher (carry trade, UIP puzzle)
- **Futures** : FuturesTrend-Researcher (Donchian breakout, position sizing)

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

## Resultats de Backtest

### Exemples ESGF (org ESGF, Fevrier 2026)

Compilation : **11/11 projets compilent avec succes** (0 erreurs, warnings non-bloquants uniquement).

| # | Projet | Periode | Return | CAGR | Sharpe | Max DD | Trades | Win Rate | Statut |
|---|--------|---------|--------|------|--------|--------|--------|----------|--------|
| 1 | **Option-Wheel-Strategy** | 2015-01 / 2026-03 | +12.7% | 12.7% | 0.524 | 26.4% | — | — | HEALTHY |
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

### Strategies Researcher (org personnelle, Mars 2026)

Compilation : **10/10 projets compilent avec succes**.

| # | Projet | Periode | Return | CAGR | Sharpe | Max DD | Trades | Win Rate | Statut |
|---|--------|---------|--------|------|--------|--------|--------|----------|--------|
| 1 | **Sector-Momentum-Researcher** | 2015-01 / 2026-03 | +102.7% | 13.1% | **0.554** | 23.0% | ~120 | 67% | HEALTHY |
| 2 | **FamaFrench-Researcher** | 2015-01 / 2026-03 | +153.5% | 8.7% | **0.365** | 31.1% | 453 | 74% | NEEDS_IMPROVEMENT |
| 3 | **OptionsIncome-Researcher** | 2024-01 / 2024-12 | +9.6% | 9.6% | 0.288 | 4.0% | 48 | 43% | NEEDS_IMPROVEMENT |
| 4 | **AllWeather-Researcher** | 2015-01 / 2026-03 | +86.8% | 5.9% | 0.25 | 23.5% | ~150 | 65% | NEEDS_IMPROVEMENT |
| 5 | **MomentumStrategy-Researcher** | 2015-01 / 2026-03 | +102.7% | 6.5% | 0.216 | 29.9% | 437 | 67% | NEEDS_IMPROVEMENT |
| 6 | **TurnOfMonth-Researcher** | 2015-01 / 2026-03 | +66.3% | 4.8% | 0.127 | 23.7% | ~250 | 52% | NEEDS_IMPROVEMENT |
| 7 | **FuturesTrend-Researcher** | 2020-01 / 2026-03 | +13.4% | 2.1% | 0.019 | 31.9% | ~80 | 50% | NEEDS_IMPROVEMENT |
| 8 | **MeanReversion-Researcher** | 2018-01 / 2026-03 | +6.3% | 0.7% | -0.042 | 46.5% | ~800 | 55% | BROKEN |
| 9 | **VIX-TermStructure-Researcher** | 2018-01 / 2026-03 | -8.9% | -1.1% | -0.97 | 20.8% | ~60 | 40% | BROKEN |
| 10 | **ForexCarry-Researcher** | 2018-01 / 2026-03 | -5.3% | -0.7% | -1.80 | 9.5% | ~300 | 45% | BROKEN |

**Legende** : HEALTHY (Sharpe > 0.5) | NEEDS_IMPROVEMENT (Sharpe 0-0.5) | BROKEN (Sharpe < 0 ou 0 trades) | NO_DATA (pas de backtest)

**Bilan** : 9/21 strategies HEALTHY ou NEEDS_IMPROVEMENT avec Sharpe positif. Les strategies Forex et VIX sont les plus difficiles a rendre rentables (classes d'actifs complexes). Les strategies ETF sectorielles et multi-asset sont les plus robustes.

### Ameliorations appliquees

**Phase 3 (Fevrier 2026) - Exemples ESGF :**

| Projet | Amelioration | Commit |
|--------|-------------|--------|
| **Multi-Layer-EMA** | Filtre Bollinger band, RSI resserre (35-70), sortie death cross + RSI>75 | c2b9cb3 |
| **ETF-Pairs-Trading** | Remplacement `arch` par `statsmodels.tsa.stattools.coint`, hedge ratio OLS numpy | c2b9cb3 |
| **BTC-MachineLearning** | Entrainement RandomForest in-situ si modele ObjectStore absent | c2b9cb3 |
| **Trend-Following** | Fix `self.algo = self` -> `self.algo = algo` dans alpha.py | 801afdb |
| **ETF-Pairs-Trading** | Ajout `Schedule.On` pour `RebalancePairs` | 801afdb |
| **Options-VGT** | Reecriture logique multi-equity (local only, projet etudiant) | 801afdb |
| **Crypto-MultiCanal** | Ajout `import traceback`, lookback 1000->500, fix CalculateOrderQuantity | en cours |

**Phase 4 (Mars 2026) - Strategies Researcher :**

| Projet | Iterations | Ameliorations cles |
|--------|-----------|-------------------|
| **Sector-Momentum** | v1 -> v2 | Passage 2 assets -> 3 (SPY/TLT/GLD), multi-lookback composite, SMA200 filter. Sharpe 0.197 -> 0.554 |
| **VIX-TermStructure** | v1 -> v2 | Ajout trailing stop 8%, VIX SMA regime filter, reduction SVXY 50% -> 30%. Perte -49.7% -> -8.9% |
| **ForexCarry** | v1 -> v2 | Passage carry trade -> FX pure momentum, SPY SMA200 risk-off filter. Perte -16.2% -> -5.3% |
| **TurnOfMonth** | v1 -> v2 | Ajout QQQ, leverage 1.5x, SMA200 filter. Sharpe -0.243 -> +0.127 |
| **MeanReversion** | v1 -> v2 | Passage long/short -> long-only, SMA200 regime filter. Return -45.4% -> +6.3% |
| **MomentumStrategy** | v1 -> v2 | Remplacement Universe Selection (trop lent) par 11 ETFs sectoriels fixes |
| **FamaFrench** | v1 -> v2 | Remplacement Universe Selection par 5 ETFs factoriels (VLUE/MTUM/SIZE/QUAL/USMV) |
| **OptionsIncome** | v1 -> v4 | Resolution Daily -> Minute (options chain vide en Daily), periode raccourcie 1 an |

### Notes sur les projets BROKEN

- **ETF-Pairs-Trading** (ESGF) : Return negatif (-14.6%). Remplacement `arch` par `statsmodels` effectue, nouveau backtest necessaire.
- **Crypto-MultiCanal** (ESGF) : Runtime error (0 trades). Corrections critiques en cours.
- **BTC-MachineLearning** (ESGF) : Aucun backtest existant. Entrainement in-situ ajoute.
- **MeanReversion-Researcher** : Sharpe legerement negatif (-0.042) malgre return positif (+6.3%). Necessite affinage des seuils RSI.
- **VIX-TermStructure-Researcher** : Classe d'actif difficile (tail risk). Ameliore de -49.7% a -8.9% mais reste negatif.
- **ForexCarry-Researcher** : FX momentum faible sur la periode. Classe d'actif peu directionnelle.

---

## Mapping pedagogique complet (21 strategies)

| Concept | Strategies | Niveau | Classes d'actifs |
|---------|-----------|--------|-----------------|
| **EMA Crossover** | CSharp-BTC-EMA-Cross, Multi-Layer-EMA | 1 | Crypto |
| **MACD + ADX** | CSharp-BTC-MACD-ADX | 1 | Crypto |
| **Options basiques** | Options-VGT | 1 | Actions |
| **Anomalie calendaire** | TurnOfMonth-Researcher | 1 | ETF |
| **Multi-Asset** | AllWeather-Researcher (3 variantes) | 1-2 | Multi |
| **Momentum sectoriel** | MomentumStrategy-Researcher, Sector-Momentum, CSharp-CTG | 1-2 | ETF/Actions |
| **Mean Reversion** | MeanReversion-Researcher, ETF-Pairs-Trading | 1-2 | Actions/ETF |
| **Trend Following** | FuturesTrend-Researcher, Trend-Following | 2 | Futures/Actions |
| **Wheel Strategy** | Option-Wheel-Strategy, OptionsIncome-Researcher | 2 | Options |
| **Factor Investing** | FamaFrench-Researcher (Fama-French via ETFs) | 2-3 | ETF |
| **Machine Learning** | BTC-MachineLearning | 3 | Crypto |
| **Volatilite** | VIX-TermStructure-Researcher | 3 | Volatilite |
| **Forex** | ForexCarry-Researcher | 3 | FX |
| **Detecteur hierarchique** | Crypto-MultiCanal | 3 | Crypto |
| **Indicateurs custom** | CSharp-CTG-Momentum | 3 | Actions |

**Couverture** : 8 classes d'actifs (Actions, ETF, Crypto, Options, Futures, FX, Volatilite, Multi-Asset), 10+ concepts de trading.

---

## Notes pour 2026

- La **Quant League** classique est terminee (Q4-2025)
- Transition vers le format **"Strategies"** en 2026
- A confirmer avec Jared Broad lors du prochain echange
- Les etudiants devront participer au format competitif QC en echange du sponsoring
- **21 strategies** disponibles (11 ESGF + 10 Researcher) couvrant tous les niveaux
