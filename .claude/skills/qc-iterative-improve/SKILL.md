---
name: qc-iterative-improve
description: Execute iterative improvement workflow for QuantConnect strategies. Arguments: [strategy] [--iterations=N] [--no-backtest]
---

# QC Iterative Improve Skill

Skill pour orchestrer l'amelioration iterative complete des strategies QuantConnect avec notebooks de recherche.

**Action**: `$ARGUMENTS`

## Arguments

| Argument | Type | Defaut | Description |
|----------|------|--------|-------------|
| `strategy` | string | all | Nom de la strategie (ex: BTC-ML, Multi-Layer-EMA). Si omis: toutes |
| `--iterations` | int | 3 | Nombre max d'iterations par strategie |
| `--no-backtest` | bool | false | Skip les backtests (compile seulement) |
| `--commit` | bool | true | Commit automatiquement les progres |

## Strategies disponibles

Les strategies sont detectees automatiquement dans `lean-workspace/*-Researcher/`:
- `BTC-ML`
- `Multi-Layer-EMA`
- `Sector-Momentum`
- `Option-Wheel`
- `BTC-MACD-ADX`

## Workflow

```
┌──────────────────────────────────────────────────────────────────┐
│                    QC ITERATIVE IMPROVE                          │
└──────────────────────────────────────────────────────────────────┘
                               │
        ┌──────────────────────┼──────────────────────┐
        │                      │                      │
        ▼                      ▼                      ▼
   ┌─────────┐           ┌──────────┐          ┌──────────┐
   │ ENV     │           │ RESEARCH │          │ IMPLEMENT│
   │ CHECK   │           │ NOTEBOOK │          │ & TEST   │
   └─────────┘           └──────────┘          └──────────┘
        │                      │                      │
        ▼                      ▼                      ▼
   ┌─────────────────────────────────────────────────────────┐
   │                   ITERATION LOOP                        │
   │  1. Read notebook + algo + doc                          │
   │  2. Read last backtest results                          │
   │  3. Add diagnostic cells to notebook                    │
   │  4. Execute cells, analyze results                      │
   │  5. Propose improvement idea                            │
   │  6. Add exploration cells for idea                      │
   │  7. Execute until idea confirmed/rejected               │
   │  8. Implement confirmed idea in algo                    │
   │  9. Push to cloud + compile                             │
   │  10. Run backtest + validate                            │
   │  11. If improved: commit, else: revert                  │
   └─────────────────────────────────────────────────────────┘
```

## Phase 1: Verification environnement

```bash
# Commands to verify
docker ps                    # Docker running
lean --version               # lean-cli available
lean cloud list-projects     # QC cloud connected
```

Si echec: arreter et signaler le probleme.

## Phase 2: Lecture du contexte

Pour la strategie donnee:
1. Lire `lean-workspace/{Strategy}-Researcher/research.ipynb`
2. Lire `lean-workspace/{Strategy}-Researcher/main.py`
3. Lire `lean-workspace/{Strategy}-Researcher/README.md` (si existe)
4. Lire `RAPPORT_FINAL.md` pour derniers resultats
5. Extraire metriques du dernier backtest

## Phase 3: Diagnostic dans notebook

Ajouter cellules de diagnostic au notebook research.ipynb:
- Cellule markdown avec resume du dernier backtest
- Cellule code pour analyse des metriques par regime
- Cellule code pour identification des points faibles

## Phase 4: Exploration iterative

Pour chaque idee d'amelioration:
1. Ajouter cellules d'exploration au notebook
2. Executer via `lean research` ou MCP Jupyter
3. Analyser les resultats
   - Si positif: Implementer dans l'algo
   - Si negatif: Abandonner l'idee
   - Si incertain: Ajuster et reessayer (max 3 fois)

Categories d'idees courantes:
- **Filtres**: Volatilite, VIX, trend, correlation
- **Parametres**: Seuils, periodes, allocations
- **Risk management**: Stop-loss, take-profit, position sizing
- **Signaux**: Nouveaux indicateurs, conditions d'entree/sortie

## Phase 5: Implementation et validation

1. Modifier main.py avec les changements valides
2. Pousser vers QC cloud: `lean cloud push --project {Strategy}-Researcher`
3. Compiler: attendre BuildSuccess
4. Lancer backtest: `lean cloud backtest {Strategy}-Researcher --push`
5. Comparer metriques:
   - Si Sharpe ameliore: Garder les changements
   - Si Sharpe degrade: Revert et documenter

## Phase 6: Commit unitaire

```bash
git add lean-workspace/{Strategy}-Researcher/
git commit -m "feat(qc): {Strategy} improvements - Sharpe X.XXX->Y.YYY"
```

## Sub-Agent Used

| Agent | Role | Model |
|-------|------|-------|
| qc-strategy-improver | Execute the improvement workflow | sonnet |

## Output attendu

```markdown
# QC Strategy Improvement Report: {Strategy}

**Date**: {timestamp}
**Iterations**: {actual}/{max}
**Resultat**: {SUCCESS|NO_CHANGE|FAILED}

## Changements implements

| Fichier | Lignes | Description |
|---------|--------|-------------|
| main.py | X-Y | Description du changement |

## Metriques

| Metric | Avant | Apres | Changement |
|--------|-------|-------|------------|
| Sharpe | X.XXX | Y.YYY | +/-Z.ZZ |
| CAGR | XX% | YY% | +/-ZZ% |
| Max DD | XX% | YY% | +/-ZZ% |

## Commit

Hash: {commit_hash}
Message: {commit_message}
```
