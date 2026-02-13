# QuantConnect Workspaces - Inventaire (Fevrier 2026)

**Compte** : jsboige@gmail.com (User ID: 46613)
**Credit Balance** : 3457.87 QCC

---

## Organisation 1 : Trading Firm ESGF (94aa4bcb...)

Workspace sponsorise par Jared Broad pour l'enseignement.

### Exemples/Templates du professeur (10 projets)

| ID | Nom | Lang | Fichiers | Description |
|----|-----|------|----------|-------------|
| 22298373 | Exemple-Python-Crypto-MultiCanal | Py | main.py (54K), research.ipynb (210K), fix_ipynb_quotes.py, research_archive.ipynb | **Detecteur hierarchique multi-canaux** - Projet principal, le plus avance |
| 21047688 | Exemple-Python-BTC-MachineLearning | Py | main.py, research.ipynb, main-simple.py, research-simple.ipynb | ML sur BTC avec version simplifiee |
| 20216947 | Exemple-Python-multi layer ema | Py | main.py, research.ipynb | Strategie multi-couches EMA |
| 21113806 | Trading des Options sur VGT Equities | Py | main.py, essai_pour_voir.ipynb | Options trading sur VGT |
| 20216898 | Exemple-Python-option wheel strategy | Py | main.py + 4 variantes (covered_puts, margin, current, updates) | Wheel strategy (options income) |
| 20216980 | Exemple-Python-sector momentum exploit | Py | main.py + DualMomentumAlphaModel + FredRate + CustomExecution + MyPcm | Momentum sectoriel avec Alpha Framework |
| 20216930 | Exemple-Python-Trend following | Py | main.py + alpha.py (22K) + trendCalculator + oracles (MACD, RSI, Bollinger) | Trend following multi-indicateurs |
| 19865767 | Exemple-Python-ETF Basket Pairs Trading | Py | main.py + alpha + portfolio + risk + universe + utils + research (38K) | Pairs trading ETF avec Framework complet |
| 19898232 | Exemple-CSharp-BTC-MACD-ADX-Daily-1 | C# | Main.cs (13K), Research.ipynb (48K) + versions temp | BTC MACD+ADX journalier (base du detecteur) |
| 19050970 | Exemple-CSharp-BTC-EMA-Cross-Daily-1 | C# | Main.cs (11K), Research.ipynb (8K) | Crossover EMA classique sur BTC |
| 19225388 | Exemple-CSharp-ctgmomentum | C# | Main.cs (12K) + 3 indicateurs custom + Research | Momentum avec indicateurs custom (Gap, AnnualizedSlope, MarketRegime) |

### Projets d'iteration/recherche (4 projets)

| ID | Nom | Lang | Fichiers | Description |
|----|-----|------|----------|-------------|
| 22275116 | BTC-MultiCanal-ZigZag-Hour-1 | C# | Main.cs (8K), Research.ipynb | Evolution horaire du MACD+ADX avec seuils adaptatifs par percentiles |
| 20423659 | BTC-MACD-ADX-Hour-1 | C# | Main.cs (8K), Research.ipynb | Version horaire du MACD+ADX |
| 21073730 | WOLF | Py | main.py (8K), research.ipynb | Projet etudiant recupere/ameliore |
| 20931062 | Renard | Py | main.py (3K), research.ipynb | Projet etudiant recupere |

### Projets etudiants (originaux)

| ID | Nom | Lang | Description |
|----|-----|------|-------------|
| 21050250 | GOLDEN ALGO FOR BTC | Py | Algorithme BTC |
| 20939368 | Crypto Portfolio Project | Py | Portfolio crypto |
| 20931449 | crypto_monnaie | Py | Trading crypto |
| 21106901 | Analyse_Tesla | Py | Analyse technique Tesla |
| 20931882 | Trading AX | Py | Strategie Trading AX |

### Clones ESGF-2025 (workspace etudiant - 7 projets)

| ID | Nom | Lang | Origine |
|----|-----|------|---------|
| 21223311 | ESGF-2025-GOLDEN ALGO FOR BTC | Py | Clone de 21050250 |
| 21223317 | ESGF-2025-Crypto Portfolio Project | Py | Clone de 20939368 |
| 21223328 | ESGF-2025-Renard | Py | Clone de 20931062 |
| 21223338 | ESGF-2025-crypto_monnaie | Py | Clone de 20931449 |
| 21223350 | ESGF-2025-Trading des Options sur VGT | Py | Clone de 21113806 |
| 21223358 | ESGF-2025-Analyse_Tesla | Py | Clone de 21106901 |
| 21223367 | ESGF-2025-WOLF | Py | Clone de 21073730 |

---

## Organisation 2 : Researcher Personnel (d600793e...)

Workspace personnel en mode Research.

| ID | Nom | Lang | Fichiers | Description |
|----|-----|------|----------|-------------|
| 20217024 | multi alpha fusion | Py | main.py + alpha.py (13K) + PortfolioConstructor.py (7K) + indicators.py | Fusion multi-alpha avec Framework |
| 20217040 | Tested mean reversion | Py | main.py (4K), research.ipynb | Strategie mean reversion |
| 1003996 | Library/Basic Library Template C 1 | C# | - | Template de base |
| 1003981 | Library/Basic Library Template C | C# | - | Template de base |

---

## Projets cles a recuperer pour 2026

### 1. Detecteur Hierarchique Multi-Canaux
- **Version Python** : `Exemple-Python-Crypto-MultiCanal` (22298373) - 54K de code, le plus avance
- **Version C# (v1)** : `Exemple-CSharp-BTC-MACD-ADX-Daily-1` (19898232) - base originale
- **Version C# (v2 horaire)** : `BTC-MultiCanal-ZigZag-Hour-1` (22275116) - seuils adaptatifs par percentiles
- **Version C# (v2bis)** : `BTC-MACD-ADX-Hour-1` (20423659) - iteration intermediaire

### 2. Exemples pedagogiques riches
- `Exemple-Python-ETF Basket Pairs Trading` - Architecture Framework complete (alpha, portfolio, risk, universe)
- `Exemple-Python-sector momentum exploit` - Momentum avec Alpha Framework
- `Exemple-Python-Trend following` - Multi-oracles (MACD, RSI, Bollinger)
- `Exemple-CSharp-ctgmomentum` - Indicateurs custom avances

### 3. Projets etudiants reutilisables
- Les 7 clones ESGF-2025 servent de modele pour la structure des workspaces ecoles

---

## Configuration MCP

```json
// ~/.claude.json
"qc-mcp": {
  "command": "docker",
  "args": ["run", "-i", "--rm", "--platform", "linux/amd64",
    "-e", "QUANTCONNECT_USER_ID=46613",
    "-e", "QUANTCONNECT_API_TOKEN=***",
    "-e", "AGENT_NAME=claude-code-coursia",
    "quantconnect/mcp-server"]
}
```

**Outils MCP disponibles** : 64 (list_projects, read_file, create_backtest, create_compile, etc.)
