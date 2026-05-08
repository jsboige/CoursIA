# PR Review Discipline — anti-complaisance

**Contexte** : règle créée 2026-05-08 après constat user que "vous êtes tous trop complaisants, on n'avance pas". Audit cycles 5-7 : 9/10 PRs nuit du 7→8 APPROVED par clusterManager-Myia sans contestation, dont #801 mega-composite 7183 lignes / 41 files, #806 +2 lignes, #807 +46 lignes doc, #791 du 7/05 +3561/-3543 prover refactor caché derrière "shapley sorry 2→1".

Cette rule s'applique à **tous les reviewers**, humains et bots (clusterManager-Myia, jsboige bot, ai-01 coordinateur).

## Critères CHANGES_REQUESTED obligatoires

Un reviewer **DOIT** poster `state: CHANGES_REQUESTED` (pas COMMENTED, pas APPROVED) si **un seul** des points suivants est violé. Posting APPROVED malgré violation = complicité de complaisance.

### A. Composites trop larges (split obligatoire)

| Métrique | Seuil "split required" |
|----------|------------------------|
| `additions + deletions` | > 3000 lignes hors notebooks |
| `changedFiles` | > 15 fichiers (hors `_output.ipynb` et données) |
| Features distinctes mentionnées dans le `## Summary` | > 4 |
| Fichiers de domaines différents (ML + Lean + GenAI mélangés) | > 1 domaine |

Si dépassement : refuser le merge, exiger split en PRs cohérentes par feature.

### B. Lean PRs : preuve de progrès vérifiable

Toute PR touchant `*.lean` ou `agent_tests/prover/` **DOIT** inclure dans le body :
1. `grep -c sorry` avant/après par fichier modifié
2. Lien vers `Lake build SUCCESS` (CI ou commit local prouvable)
3. Lien vers `Proof integrity SUCCESS` (axiom check)
4. Si refactor du prover Python : justifier pourquoi le refactor est nécessaire pour le claim Lean (sinon split en 2 PRs)

Sans ces 4 éléments, **CHANGES_REQUESTED** automatique.

### C. ML PRs : multi-seed obligatoire

Toute PR claim "BEATS" ou "improvement" sur métriques ML/trading **DOIT** inclure :
1. Walk-forward 5-fold (pas single split)
2. **≥4 seeds** parmi 0/1/7/42/99 (cf [feedback_multi_seed_required.md])
3. Edge ≥ 2σ cross-seed sinon flag "noise"
4. Comparaison à majority baseline + transaction costs (5bps SPY, 10bps crypto)
5. **Pas de FAANG/Mag7** en training set (cf [dataset_paths.md])
6. Verdict honnête : "BEATS" / "NO BEATS" / "INCONCLUSIVE" — pas de "promising"

Single-seed ou single-fold = **CHANGES_REQUESTED** sauf si flag explicite `[POC]` dans le titre.

### D. Notebook PRs : preuve d'exécution réelle

Toute PR touchant `*.ipynb` **DOIT** inclure :
1. Sortie de `papermill` ou kernel exec (pas juste "Papermill SUCCESS" — coller les premières lignes des outputs)
2. Vérification 0 NotImplementedError (`grep -nE "raise NotImplementedError|assert False|1/0" <nb>`)
3. Cellules code = `execution_count: <int>` ET `outputs: [...]` cohérents (règle C.2 CLAUDE.md)
4. Diff ne supprime pas de cellules `# Solution` ou `# Exemple résolu` sans issue référencée (anti-régression)

Pas de validation visuelle (PPTX/Slidev) jamais "OK" sur "j'ai screenshotté". Liens vers screenshots.

### E. Documentation/Admin PRs : groupement obligatoire

PRs dont le contenu = uniquement docs/README/CLAUDE.md/rules :
- Single PR < 50 lignes : refuser, exiger groupement avec autre PR du même cycle
- Single PR < 20 lignes : refuser systématiquement (commit direct sur main si trivial)
- Multiple READMEs touchés sans cohérence cross-series : refuser, exiger un seul focus

Anti-pattern visé : PRs micro qui inflate le compteur "PRs livrées" sans valeur réelle (#806 +2 lignes, #807 +46 lignes doc seul, etc.)

### F. Audit reassessment / "false positive" PRs

Reassessment d'un audit existant **DOIT** documenter :
1. Critère exact violé par l'audit initial (cite le pattern reconnu)
2. Méthodologie de vérification (pas "j'ai regardé visuellement")
3. Au moins 3 cellules-types vérifiées avec preuve (sortie cell ou diff)

Ré-classification "false positive" sans preuve = **CHANGES_REQUESTED**.

### G. QC PRs : backtest obligatoire

Toute PR touchant `MyIA.AI.Notebooks/QuantConnect/projects/` ou strategies cataloguées **DOIT** inclure :
1. Backtest run (`create_compile` + `create_backtest` via MCP qc-mcp)
2. Métriques Sharpe/CAGR/MaxDD reportées dans le body
3. Période OOS distincte de training (pas de same-period leak)

## Anti-pattern : APPROVED en lot batch 5 PRs en 5 minutes

Si un reviewer APPROVE >3 PRs dans une fenêtre <10 minutes : flag automatique. Probable rubber-stamp.

## Mention explicite des bots

@clusterManager-Myia : ces critères s'appliquent à toi en priorité. Tu es la première ligne de défense. Si tu APPROVE une PR violant un des critères ci-dessus, le coordinateur ai-01 contestera explicitement et la PR sera bloquée jusqu'au split / fix.

@jsboige (self-review bot) : self-approval sans valeur GitHub. Reste en COMMENTED + signale les violations dans le body comme tu le fais déjà.

## Workflow ai-01 (coordinateur)

Avant tout merge cascade, ai-01 lit :
1. `gh pr view <N> --json files,additions,deletions,body,reviews` (pas juste mergeStateStatus)
2. Vérifie chacun des critères A-G applicables
3. Si violation : commente sur la PR (`gh pr comment <N>`) avec demande explicite (split, multi-seed, sorry-count, etc.) + ne merge pas
4. Si conforme : merge avec mention dans le bilan dashboard

Pas de merge en parallèle 5 PRs sans avoir lu les 5 bodies.

## Liens

- [feedback_multi_seed_required.md](../projects/d--CoursIA/memory/feedback_multi_seed_required.md)
- [feedback_use_bot_reviews_for_dispatch.md](../projects/d--CoursIA/memory/feedback_use_bot_reviews_for_dispatch.md)
- [feedback_review_state_filter.md](../projects/d--CoursIA/memory/feedback_review_state_filter.md)
- [anti-regression.md](anti-regression.md)
- CLAUDE.md section B (Reviews PR 5 points obligatoires)
