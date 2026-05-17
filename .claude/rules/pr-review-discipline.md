# PR Review Discipline — anti-complaisance

S'applique à **tous les reviewers**, humains et bots (clusterManager-Myia, jsboige self-bot, ai-01 coordinateur).

**Contexte (incident 2026-05-08), workflow ai-01, anti-patterns détaillés** : [docs/pr-review-context.md](../../docs/pr-review-context.md).

## Critères CHANGES_REQUESTED obligatoires (HARD)

Un reviewer **DOIT** poster `state: CHANGES_REQUESTED` (pas COMMENTED, pas APPROVED) si **un seul** des points suivants est violé. Posting APPROVED malgré violation = complicité de complaisance.

### A. Composites trop larges (split obligatoire)

| Métrique | Seuil "split required" |
|----------|------------------------|
| `additions + deletions` | > 3000 lignes hors notebooks |
| `changedFiles` | > 15 fichiers (hors `_output.ipynb` et données) |
| Features distinctes dans `## Summary` | > 4 |
| Domaines différents (ML + Lean + GenAI mélangés) | > 1 domaine |

Si dépassement : refuser le merge, exiger split en PRs cohérentes par feature.

### B. Lean PRs : preuve de progrès vérifiable

Toute PR touchant `*.lean` ou `agent_tests/prover/` **DOIT** inclure dans le body :
1. `grep -c sorry` avant/après par fichier modifié
2. Lien vers `Lake build SUCCESS` (CI ou commit local prouvable)
3. Lien vers `Proof integrity SUCCESS` (axiom check)
4. Si refactor du prover Python : justifier pourquoi le refactor est nécessaire pour le claim Lean (sinon split en 2 PRs)

Sans ces 4 éléments → **CHANGES_REQUESTED** automatique.

### C. ML PRs : multi-seed obligatoire

Toute PR claim "BEATS" ou "improvement" sur métriques ML/trading **DOIT** inclure :
1. Walk-forward 5-fold (pas single split)
2. **≥4 seeds** parmi 0/1/7/42/99
3. Edge ≥ 2σ cross-seed sinon flag "noise"
4. Comparaison à majority baseline + transaction costs (5bps SPY, 10bps crypto)
5. **Pas de FAANG/Mag7** en training set
6. Verdict honnête : "BEATS" / "NO BEATS" / "INCONCLUSIVE" — pas de "promising"

Single-seed ou single-fold = **CHANGES_REQUESTED** sauf si flag explicite `[POC]` dans le titre.

### D. Notebook PRs : preuve d'exécution réelle

Toute PR touchant `*.ipynb` **DOIT** inclure :
1. Sortie de `papermill` ou kernel exec (coller les premières lignes des outputs)
2. Vérification 0 NotImplementedError (`grep -nE "raise NotImplementedError|assert False|1/0" <nb>`)
3. Cellules code = `execution_count: <int>` ET `outputs: [...]` cohérents (règle C.2 CLAUDE.md)
4. Diff ne supprime pas de cellules `# Solution` ou `# Exemple résolu` sans issue référencée (anti-régression)

### E. Documentation/Admin PRs : groupement obligatoire

PRs dont le contenu = uniquement docs/README/CLAUDE.md/rules :
- Single PR < 50 lignes : refuser, exiger groupement
- Single PR < 20 lignes : refuser systématiquement
- Multiple READMEs sans cohérence cross-series : refuser

### F. Audit reassessment / "false positive" PRs

Reassessment d'un audit existant **DOIT** documenter :
1. Critère exact violé par l'audit initial (cite le pattern reconnu)
2. Méthodologie de vérification (pas "j'ai regardé visuellement")
3. Au moins 3 cellules-types vérifiées avec preuve (sortie cell ou diff)

Cf [.claude/rules/audit-reassessment.md](audit-reassessment.md).

### G. QC PRs : backtest obligatoire

Toute PR touchant `MyIA.AI.Notebooks/QuantConnect/projects/` **DOIT** inclure :
1. Backtest run (`create_compile` + `create_backtest` via MCP qc-mcp)
2. Métriques Sharpe/CAGR/MaxDD reportées dans le body
3. Période OOS distincte de training (pas de same-period leak)
