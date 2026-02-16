# QC Iterative Improve Skill

Skill pour orchestrer l'amelioration iterative des strategies QuantConnect.

## Type

User-invocable (`/qc-iterative-improve`)

## Description

Orchestre un cycle complet d'amelioration iterative:
1. Analyser les backtests existants
2. Diagnostiquer les problemes
3. Proposer des ameliorations (avec recherche web si necessaire)
4. Implementer les changements
5. Compiler et verifier
6. Documenter les resultats

## Usage

```
/qc-iterative-improve <project_id> [--mode=fix|improve|research] [--iterations=3]
```

### Arguments

| Argument | Type | Defaut | Description |
|----------|------|--------|-------------|
| `project_id` | int | required | ID du projet QC |
| `--mode` | string | improve | Mode: fix (bugs), improve (perf), research (ideation) |
| `--iterations` | int | 3 | Nombre max d'iterations |
| `--web-search` | bool | false | Activer la recherche web pour ideation |
| `--auto-push` | bool | true | Pousser automatiquement vers cloud |

### Modes

#### Mode `fix` - Correction de bugs

Pour les projets BROKEN (0 trades, runtime errors):

```
1. Lister les backtests et identifier les erreurs
2. Analyser la stacktrace
3. Lire le code source
4. Proposer et implementer la correction
5. Compiler
6. Verifier que le projet n'a plus d'erreurs runtime
```

#### Mode `improve` - Amelioration de performance

Pour les projets NEEDS_IMPROVEMENT (Sharpe 0-0.5):

```
1. Analyser les metriques des backtests existants
2. Identifier les points faibles (DD, Win Rate, etc.)
3. Proposer des ameliorations basees sur la theorie
4. Implementer les changements
5. Compiler
6. (Backtest a lancer manuellement via UI)
```

#### Mode `research` - Ideation et exploration

Pour explorer de nouvelles approches:

```
1. Analyser la strategie actuelle
2. Rechercher des approches alternatives (web search)
3. Creer un notebook de recherche
4. Tester des hypotheses
5. Proposer des changements bases sur les findings
```

## Workflow orchestration

```
┌─────────────────────────────────────────────────┐
│          QC Iterative Improve (Skill)           │
│                 (Orchestrator)                  │
└─────────────────────────────────────────────────┘
                      │
          ┌───────────┼───────────┐
          │           │           │
          ▼           ▼           ▼
    ┌─────────┐ ┌──────────┐ ┌──────────┐
    │Analyzer │ │ Improver │ │ Research │
    │ Agent   │ │  Agent   │ │  Agent   │
    └─────────┘ └──────────┘ └──────────┘
          │           │           │
          └───────────┼───────────┘
                      │
                      ▼
              ┌─────────────┐
              │   Compile   │
              │   + Push    │
              └─────────────┘
```

## Processus iteratif

```python
iteration = 0
improvements_made = []

while iteration < max_iterations:
    iteration += 1
    print(f"=== Iteration {iteration}/{max_iterations} ===")

    # 1. Analyser l'etat actuel
    analysis = analyze_project(project_id)
    print(f"Status: {analysis['status']}")
    print(f"Sharpe: {analysis['sharpe']}")

    # 2. Verifier si on a atteint l'objectif
    if mode == 'fix' and analysis['status'] != 'BROKEN':
        print("SUCCESS: Project is no longer BROKEN")
        break
    if mode == 'improve' and analysis['sharpe'] > 0.5:
        print("SUCCESS: Sharpe > 0.5 achieved")
        break

    # 3. Generer des propositions
    if web_search and iteration == 1:
        proposals = research_improvements(analysis)
    else:
        proposals = generate_improvements(analysis)

    if not proposals:
        print("No more improvements to propose")
        break

    # 4. Implementer la meilleure proposition
    best_proposal = proposals[0]
    result = implement_improvement(best_proposal)
    improvements_made.append(result)

    # 5. Compiler
    compile_result = compile_project(project_id)
    if compile_result['state'] != 'BuildSuccess':
        print(f"ERROR: Compilation failed")
        rollback_changes()
        continue

    print(f"Implemented: {best_proposal['title']}")

print(f"\n=== Final Results ===")
print(f"Iterations: {iteration}")
print(f"Improvements: {len(improvements_made)}")
print(f"Status: {analysis['status']}")
```

## Exemples

### Exemple 1: Corriger un projet BROKEN

```
/qc-iterative-improve 22298373 --mode=fix
```

Workflow:
1. Analyse: BROKEN (0 trades)
2. Diagnostic: Runtime error 'lookback_days_macro' not defined
3. Fix: Add self.lookback_days_macro = 500 in Initialize()
4. Compile: BuildSuccess
5. Status: HEALTHY (pending backtest)

### Exemple 2: Ameliorer un projet NEEDS_IMPROVEMENT

```
/qc-iterative-improve 19865767 --mode=improve --iterations=5
```

Workflow:
1. Analyse: Sharpe -0.759, 304 trades
2. Propositions:
   - Augmenter zscore_threshold (2.0 -> 2.5)
   - Ajouter filtre correlation > 0.7
   - Reduire position sizing
3. Implementer chaque proposition
4. Compiler
5. (Backtest via UI pour mesurer improvement)

### Exemple 3: Recherche de nouvelles idees

```
/qc-iterative-improve 19865767 --mode=research --web-search
```

Workflow:
1. Analyser la strategie pairs trading actuelle
2. Web search: "pairs trading improvements 2024"
3. Trouver des approches: Kalman filter, ML-based pairs selection
4. Creer notebook de recherche
5. Proposer des changements bases sur la recherche

## Output format

```markdown
# QC Iterative Improvement Report: {project_name}

**Project ID**: {project_id}
**Mode**: {mode}
**Date**: {timestamp}
**Iterations**: {actual}/{max}

---

## Initial State

| Metric | Value |
|--------|-------|
| Status | {initial_status} |
| Sharpe | {initial_sharpe} |
| Max DD | {initial_dd} |
| Trades | {initial_trades} |

---

## Iterations

### Iteration 1

**Analysis**: {analysis_summary}
**Proposal**: {proposal_title}
**Implementation**: {changes_made}
**Compile**: {compile_result}
**Result**: {result_summary}

### Iteration 2
...

---

## Final State

| Metric | Value | Change |
|--------|-------|--------|
| Status | {final_status} | {status_change} |
| Sharpe | {final_sharpe} | {sharpe_change} |
| Max DD | {final_dd} | {dd_change} |
| Trades | {final_trades} | {trades_change} |

---

## Summary

- Improvements implemented: {count}
- Compilation successes: {compile_successes}
- Time spent: {duration}

**Next Steps**:
1. Run backtest via QC web UI
2. Analyze new metrics
3. Iterate if needed

---

## Files Modified

| File | Lines Changed | Description |
|------|---------------|-------------|
| {file1} | {lines} | {desc} |
```

## Integration avec les agents

Ce skill orchestre les agents suivants:

- `qc-strategy-analyzer`: Pour l'analyse des backtests
- `qc-strategy-improver`: Pour l'implementation des changements
- `general-purpose`: Pour la recherche web et l'ideation

## Prerequis

- MCP `qc-mcp` configure dans `~/.claude.json`
- Compte QuantConnect avec credits
- Fichiers locaux syncs avec le cloud

## Limitations

- Les backtests doivent etre lances manuellement via UI (API payante)
- Maximum 3 iterations sans intervention utilisateur
- Les recherches web consomment des tokens
