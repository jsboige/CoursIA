---
name: qc-iterative-improve
description: Execute iterative improvement workflow for QuantConnect strategies. Arguments: [strategy|issue#] [--iterations=N] [--no-backtest] [--commit]
---

# QC Iterative Improve Skill

Orchestre l'amelioration iterative des strategies QuantConnect.
**Methodologie**: Research notebook d'abord, implementation ensuite.

**Action**: `$ARGUMENTS`

## Arguments

| Argument | Type | Defaut | Description |
|----------|------|--------|-------------|
| `strategy` | string | - | Nom de la strategie OU numero d'issue GitHub (#17-#29) |
| `--iterations` | int | 3 | Nombre max d'iterations par strategie |
| `--no-backtest` | bool | false | Skip les backtests (notebook research seulement) |
| `--commit` | bool | false | Commit automatiquement les progres |

## Mapping Issues -> Strategies

| Issue | Strategie | Cloud ID | Sharpe | Priorite |
|-------|-----------|----------|--------|----------|
| #17 | ForexCarry | 28657908 | -1.80 | HIGH |
| #18 | VIX-TermStructure | 28657907 | -0.97 | HIGH |
| #19 | MeanReversion | 28657904 | -0.042 | HIGH |
| #27 | Crypto-MultiCanal | (a creer) | 0 | HIGH |
| #20 | FuturesTrend | 28657834 | 0.019 | MEDIUM |
| #21 | TurnOfMonth | 28657905 | 0.127 | MEDIUM |
| #22 | MomentumStrategy | 28657837 | 0.216 | MEDIUM |
| #23 | AllWeather | 28657833 | 0.25 | MEDIUM |
| #24 | OptionsIncome | 28657838 | 0.288 | MEDIUM |
| #25 | FamaFrench | 28657910 | 0.365 | MEDIUM |
| #26 | Sector-Momentum | 28433643 | 0.554 | LOW |

Tracker global: issue #29

## Workflow principal

```
                    ┌─────────────────────────────────────┐
                    │  /qc-iterative-improve #XX          │
                    └──────────────┬──────────────────────┘
                                   │
                    ┌──────────────▼──────────────────────┐
                    │  1. CONTEXT: Lire issue + code +    │
                    │     backtests + notebook existant    │
                    └──────────────┬──────────────────────┘
                                   │
                    ┌──────────────▼──────────────────────┐
                    │  2. RESEARCH NOTEBOOK                │
                    │  Creer/enrichir research.ipynb       │
                    │  - Analyse exploratoire (QuantBook)  │
                    │  - Hypotheses et tests               │
                    │  - Visualisations                    │
                    │  - Conclusions argumentees           │
                    └──────────────┬──────────────────────┘
                                   │
                    ┌──────────────▼──────────────────────┐
                    │  3. IMPLEMENT                        │
                    │  Appliquer findings dans main.py     │
                    │  (seulement si notebook concluant)   │
                    └──────────────┬──────────────────────┘
                                   │
                    ┌──────────────▼──────────────────────┐
                    │  4. VALIDATE                         │
                    │  Compiler + backtester sur QC cloud  │
                    └──────────────┬──────────────────────┘
                                   │
                    ┌──────────────▼──────────────────────┐
                    │  5. EVALUATE + UPDATE                │
                    │  Comparer metriques, MAJ issue #29   │
                    │  Iterer si necessaire                │
                    └─────────────────────────────────────┘
```

## Phase 0: Lire le backlog (OBLIGATOIRE)

```
1. Lire projects/OPTIMIZATION_BACKLOG.md
   - Verifier si la strategie a un plafond confirme -> STOP si oui
   - Lire les hypotheses deja testees et rejetees -> NE PAS retester
   - Appliquer les regles universelles (18 patterns confirmes)

2. A la fin de l'iteration: mettre a jour le backlog avec les nouvelles lecons
```

## Phase 1: Lire le contexte

```
1. Lire l'issue GitHub (gh issue view #XX)
   - Problemes identifies
   - Travail demande
   - Lecons apprises des sessions precedentes

2. Lire le code cloud actuel
   - MCP: read_file(projectId, "main.py")
   - Local: projects/{Strategy}/main.py

3. Lire les derniers backtests
   - MCP: list_backtests(projectId, includeStatistics=true)
   - MCP: read_backtest(projectId, backtestId) pour le meilleur

4. Verifier si un notebook existe deja
   - projects/{Strategy}/research.ipynb
   - ESGF-2026/examples/{Strategy}/research.ipynb
   - ESGF-2026/lean-workspace/{Strategy}-Researcher/research.ipynb
```

## Phase 2: Research Notebook (COEUR DU WORKFLOW)

Le notebook est l'artefact principal. Il doit etre:
- **Pedagogique**: expliquer le raisonnement a chaque etape
- **Reproductible**: executable avec QuantBook ou standalone
- **Conclusif**: chaque hypothese testee a un verdict clair

### Structure recommandee du notebook

```
Cell 1 (md): # Research: {Strategy Name}
  - Contexte et objectif
  - Performance actuelle et problemes
  - Hypotheses a tester

Cell 2 (code): Setup & Data Loading
  - qb = QuantBook() ou import yfinance
  - Charger les donnees historiques
  - Afficher statistiques de base

Cell 3 (md): ## Analyse Exploratoire
  - Description de ce qu'on va explorer

Cell 4 (code): Analyse exploratoire
  - Distributions, correlations, regimes
  - Visualisations (matplotlib/plotly)

Cell 5-N: Hypotheses et tests
  Pour chaque hypothese:
  - Cell (md): Description de l'hypothese
  - Cell (code): Test de l'hypothese
  - Cell (md): Verdict (CONFIRMEE/INFIRMEE) et impact

Cell N+1 (md): ## Conclusions et Recommendations
  - Resume des findings
  - Configuration recommandee
  - Changements a implementer dans main.py

Cell N+2 (code): Configuration finale
  - Parametres recommandes en format dict/JSON
  - Backtest vectorise simplifie si possible
```

### Deux approches possibles

**Approche A: QuantBook (si lean research disponible)**
```python
qb = QuantBook()
symbol = qb.add_equity("SPY", Resolution.DAILY).symbol
history = qb.history(symbol, datetime(2015,1,1), datetime.now(), Resolution.DAILY)
```
Avantage: donnees QC exactes, memes indicateurs que l'algo

**Approche B: Standalone (yfinance/pandas)**
```python
import yfinance as yf
data = yf.download("SPY", start="2015-01-01", end="2026-01-01")
```
Avantage: pas besoin de Docker/lean, executable n'importe ou
Inconvenient: donnees peuvent differer legerement de QC

**Recommandation**: Utiliser l'approche B (standalone) pour la recherche,
puis valider avec un backtest cloud QC. Plus rapide et plus accessible pedagogiquement.

## Phase 3: Implementation

Seulement si le notebook a produit des conclusions claires.

```
1. Modifier main.py localement en appliquant les findings du notebook
2. MCP: read_file(projectId, "main.py")  -- acquiert le lock
3. MCP: update_file_contents(projectId, "main.py", newContent)
```

## Phase 4: Validation

```
1. MCP: create_compile(projectId) -> compileId
2. MCP: read_compile(projectId, compileId) -> BuildSuccess?
3. MCP: create_backtest(projectId, compileId, "v{N}")
4. Attendre 60-240s selon type
5. MCP: read_backtest(projectId, backtestId) -> metriques
```

## Phase 5: Evaluation et mise a jour

```
1. Comparer Sharpe avant/apres
2. Si ameliore: garder, MAJ fichier local + notebook
3. Si degrade: revert
4. MAJ issue GitHub avec le nouveau Sharpe
5. MAJ tracker #29 avec le statut
6. Si --commit: git add + commit
```

## Reprise apres saturation de contexte

Le workflow est concu pour survivre aux redemarrages:

**Etat persistant (survit au redemarrage):**
- Issue GitHub (#XX) avec checklist de progression
- Notebook research.ipynb avec les cellules deja creees
- Code main.py (local + cloud)
- Backtests sur le cloud QC

**Pour reprendre:**
1. Relancer `/qc-iterative-improve #XX`
2. L'agent lit l'issue, le notebook, les backtests
3. Il identifie ou on en est et continue

## Regles critiques

0. **BACKLOG AVANT TOUT** - Lire `projects/OPTIMIZATION_BACKLOG.md` avant de commencer. Ne pas retester des hypotheses rejetees.
1. **Notebook AVANT code** - Ne jamais modifier main.py sans avoir d'abord explore dans le notebook
2. **read_file AVANT update_file_contents** - Collaboration lock QC
3. **1 seul backtest a la fois** - Node unique QC
4. **Options = Resolution.MINUTE** - Sinon chain vide
5. **Pas de Universe Selection** - Trop lent. ETFs fixes
6. **Long-only en bull market** - Short = catastrophique
7. **"In Progress..." = bug MCP** - Attendre et reessayer
8. **Org perso seulement** - ESGF = FREE, pas de backtest API

## Sub-Agent

| Agent | Role | Model |
|-------|------|-------|
| qc-strategy-improver | Execute le workflow complet | sonnet |

## Output attendu

```markdown
# QC Improvement Report: {Strategy} (Issue #{N})

**Date**: {timestamp}
**Iterations**: {actual}/{max}
**Resultat**: {SUCCESS|IN_PROGRESS|NO_CHANGE|FAILED}

## Research Notebook
- Chemin: projects/{Strategy}/research.ipynb
- Cellules: {N} ({code}/{md})
- Hypotheses testees: {list}
- Conclusions: {summary}

## Metriques

| Metric | Avant | Apres | Changement |
|--------|-------|-------|------------|
| Sharpe | {X} | {Y} | {delta} |
| CAGR | {X%} | {Y%} | {delta} |
| Max DD | {X%} | {Y%} | {delta} |

## Prochaines etapes
{next_steps pour la prochaine iteration}
```
