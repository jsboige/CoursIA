# QC Helpers Skill

Skill de reference pour les operations QuantConnect via MCP.

## Type

Reference (auto-loaded)

## Description

Documente les patterns et helpers pour utiliser les outils MCP QuantConnect.

## Configuration

- **User ID**: 46613
- **Org personnelle (PAID)**: `d600793ee4caecb03441a09fc2d00f7f` - Backtest API OK
- **Org ESGF (FREE)**: `94aa4bcb45ff1d1ef286d93817104cce` - Compile OK, backtest API REFUSE
- **IMPORTANT**: Toujours specifier `organizationId` dans create_project, sinon defaut = ESGF (FREE)

## Outils MCP disponibles

### Gestion de projets

| Outil | Description |
|-------|-------------|
| `list_projects` | Lister tous les projets |
| `create_project` | Creer un projet (specifier organizationId!) |
| `read_project` | Lire details d'un projet |
| `update_project` | Modifier nom/description |
| `delete_project` | Supprimer un projet |

### Fichiers

| Outil | Description |
|-------|-------------|
| `read_file` | Lire un fichier du cloud |
| `update_file_contents` | Modifier un fichier (read_file AVANT!) |
| `create_file` | Creer un nouveau fichier |
| `delete_file` | Supprimer un fichier |
| `update_file_name` | Renommer un fichier |
| `patch_file` | Modifier des lignes specifiques (plus efficace) |

### Compilation

| Outil | Description |
|-------|-------------|
| `create_compile` | Demarrer une compilation |
| `read_compile` | Lire le resultat (BuildSuccess ou erreurs) |

### Backtests

| Outil | Description |
|-------|-------------|
| `list_backtests` | Lister les backtests (includeStatistics=true!) |
| `create_backtest` | Lancer un backtest (1 a la fois!) |
| `read_backtest` | Lire resultats (Sharpe, CAGR, DD, trades) |
| `read_backtest_orders` | Analyser les ordres executes |
| `read_backtest_chart` | Visualiser equity curve |
| `read_backtest_insights` | Insights detailles |
| `delete_backtest` | Supprimer un backtest |

### Autres

| Outil | Description |
|-------|-------------|
| `search_quantconnect` | Rechercher dans la doc/forum QC |
| `check_syntax` | Verifier la syntaxe Python/C# |
| `update_code_to_pep8` | Convertir en PEP8 style |
| `enhance_error_message` | Expliquer une erreur QC |

## Patterns critiques

### Pattern: read_file AVANT update_file_contents

```
OBLIGATOIRE: Toujours lire le fichier avant de le modifier.
Sinon erreur "prevent code loss" (collaboration lock).

1. read_file(projectId, "main.py")     -> acquiert le lock
2. update_file_contents(projectId, ...) -> ecrit avec le lock
```

### Pattern: Compiler un projet

```
1. create_compile(projectId) -> compileId
2. read_compile(projectId, compileId) -> state: "BuildSuccess" ou erreurs
   - Si "BuildSuccess": pret pour backtest
   - Si erreurs: lire errors[], corriger, recompiler
```

### Pattern: Lancer et lire un backtest

```
1. create_backtest(projectId, compileId, backtestName) -> backtestId
2. Attendre 60-240s selon la strategie
3. read_backtest(projectId, backtestId) -> resultats

ATTENTION: Si status = "In Progress...", le MCP Pydantic plante!
Le validator n'accepte que: "Completed.", "In Queue...", "Running: X%", "Runtime Error"
Solution: attendre 30s et reessayer. Ou utiliser list_backtests pour checker le status.
```

### Pattern: Creer un projet dans l'org perso

```
create_project(name, language="Py", organizationId="d600793ee4caecb03441a09fc2d00f7f")

SANS organizationId -> cree dans ESGF (FREE) -> pas de backtest API!
```

## Project IDs

### Org personnelle (d600793e) - Strategies Researcher

| Projet | Cloud ID | Sharpe | Statut | Plafond? |
|--------|----------|--------|--------|----------|
| AllWeather | 28657833 | 0.602 | HEALTHY | OUI |
| Sector-Momentum | 28433643 | 0.555 | HEALTHY | OUI |
| FamaFrench | 28657910 | 0.540 | HEALTHY | OUI |
| MomentumStrategy | 28657837 | 0.472 | NEEDS_IMPROVEMENT | OUI |
| EMA-Cross-Index | 28789945 | 0.470 | NEEDS_IMPROVEMENT | OUI |
| RiskParity | 28692653 | 0.399 | NEEDS_IMPROVEMENT | OUI |
| MeanReversion | 28657904 | 0.365 | NEEDS_IMPROVEMENT | ~ |
| DualMomentum | 28692516 | 0.350 | NEEDS_IMPROVEMENT | OUI |
| FuturesTrend | 28657834 | 0.301 | NEEDS_IMPROVEMENT | OUI |
| OptionsIncome | 28657838 | 0.234 | NEEDS_IMPROVEMENT | OUI |
| Trend-Following | 28797562 | 0.212 | NEEDS_IMPROVEMENT | NON |
| TurnOfMonth | 28657905 | 0.128 | NEEDS_IMPROVEMENT | OUI |
| VIX-TermStructure | 28657907 | 0.051 | NEEDS_IMPROVEMENT | OUI |
| ForexCarry | 28657908 | -0.324 | BROKEN | OUI |
| PairsTrading | 28693651 | -0.361 | BROKEN | ~ |
| ETF-Pairs | 28433746 | -0.706 | BROKEN | ~ |
| Crypto-MultiCanal | 28733256 | 0.486 | NEEDS_IMPROVEMENT | OUI |
| EMA-Cross-Crypto | 28789943 | 1.272 | HEALTHY | — |
| EMA-Cross-Stocks | 28789946 | 0.872 | HEALTHY | — |

### Org ESGF (94aa4bcb) - Exemples pedagogiques

| Projet | Cloud ID | Sharpe | Lang | Note |
|--------|----------|--------|------|------|
| Multi-Layer-EMA | 20216947 | 1.891 | Python | HEALTHY |
| CSharp-BTC-MACD-ADX | 19898232 | 1.224 | C# | HEALTHY, Docker requis |
| CSharp-BTC-EMA-Cross | 19050970 | 1.094 | C# | HEALTHY |
| Option-Wheel | 20216898 | 0.996 | Python | HEALTHY |
| Options-VGT | 21113806 | 0.892 | Python | HEALTHY |
| CSharp-CTG-Momentum | 19225388 | 0.507 | C# | HEALTHY |
| Sector-Momentum | 20216980 | 2.530 | Python | HEALTHY (courte periode) |
| Trend-Following | 20216930 | 2.157 | Python | HEALTHY (courte periode) |
| Crypto-MultiCanal | 22298373 | 0 | Python | BROKEN (0 trades) |
| ETF-Pairs-Trading | 19865767 | -0.759 | Python | BROKEN |
| BTC-MachineLearning | 21047688 | N/A | Python | NO_DATA |

## Fichiers locaux

Les strategies Researcher ont leur code local dans:
```
MyIA.AI.Notebooks/QuantConnect/projects/{StrategyName}/main.py
```

Les exemples ESGF sont dans:
```
MyIA.AI.Notebooks/QuantConnect/ESGF-2026/examples/{ProjectName}/main.py
```

## Classification des performances

| Statut | Sharpe | Description |
|--------|--------|-------------|
| HEALTHY | > 0.5 | Performances acceptables |
| NEEDS_IMPROVEMENT | 0-0.5 | A ameliorer |
| BROKEN | < 0 | Sharpe negatif ou 0 trades |
| NO_DATA | N/A | Pas de backtest |

### Cibles

| Metrique | Target | Acceptable |
|----------|--------|------------|
| Sharpe Ratio | > 1.0 | > 0.5 |
| Max Drawdown | < 20% | < 30% |
| CAGR | > 15% | > 5% |

## Backlog d'optimisation (LIRE EN PREMIER)

**Fichier**: `MyIA.AI.Notebooks/QuantConnect/projects/OPTIMIZATION_BACKLOG.md`

Ce fichier commite contient:
- Regles universelles confirmees (18 patterns)
- Plafonds structurels par strategie (ne plus iterer)
- Hypotheses testees et rejetees (ne pas retester)
- Divergences yfinance vs QC Cloud
- Meta-lecons sur le processus d'optimisation

**OBLIGATOIRE**: Lire ce fichier avant toute optimisation de strategie.

## Gotchas et lecons apprises

1. **Options = Resolution.MINUTE** : option_chains est vide avec Resolution.DAILY
2. **Universe Selection** : 500 stocks x history() = 20+ min. Remplacer par ETFs fixes
3. **Short selling en bull market** : Mean reversion long-short perd enormement. Long-only + SMA200
4. **SVXY** : ETN inverse VIX, perd 90% en crise. Max 30% + trailing stop
5. **FX carry taux statiques** : Ne marche pas, politique monetaire change. Utiliser momentum FX pur
6. **Factor ETFs** : VLUE, MTUM, SIZE, QUAL, USMV couvrent Fama-French sans Universe Selection
7. **Sector ETFs** : XLK, XLF, XLE, XLV, XLI, XLY, XLP, XLU, XLB, XLRE, XLC = 11 GICS
8. **OptionsIncome** : Minute sur 1 an = ~4 min backtest. 2 ans = trop lent
9. **BTC-MACD-ADX** : C# + Docker lean:latest (42.5 GB), chaque pull renomme le projet cloud
10. **QC PEP8** : `Futures.Indices.SP_500_E_MINI`, `OptionRight.CALL`, `Resolution.DAILY`
