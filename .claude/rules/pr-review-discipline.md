# PR Review Discipline — anti-complaisance

S'applique à **tous les reviewers**, humains et bots (clusterManager-Myia, jsboige self-bot, ai-01 coordinateur).

**Exception — PRs de TP étudiantes (mandat user 2026-05-20).** Les critères CHANGES_REQUESTED A-G ci-dessous visent les PRs **internes/contributeurs** (agents cluster `myia-*`, staff). Les PRs soumises par des **étudiants** (forks ou comptes étudiants de `jsboige/CoursIA`) suivent [student-pr-reviews.md](student-pr-reviews.md) : review **bienveillante**, bypass template + CI, **pas de CHANGES_REQUESTED** sur scaffolding (template vide, CI rouge, exec_count manquant). Ne PAS appliquer A-G à un TP étudiant.

**Contexte (incident 2026-05-08), workflow ai-01, anti-patterns détaillés** : [docs/pr-review-context.md](../../docs/reference/pr-review-context.md).

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

**Advisory `.NET execution_count` ≠ outputs vides autorisés (#5214).** La CI ne peut pas Papermill-exécuter les notebooks .NET Interactive (pas de kernel en CI) — l'advisory autorise à **sauter la ré-exécution CI**, **pas** à committer des sorties vides. `.NET Interactive` s'exécute **localement** sur chaque machine worker (`dotnet-interactive`), donc une cellule .NET committée **DOIT** porter `execution_count != null` = preuve d'exécution locale. Le validateur `scripts/notebook_tools/validate_pr_notebooks.py` FAIL désormais sur un notebook .NET avec `execution_count: null` (verdict forensique H.5 `STRUCTURAL_ONLY`), et ne tolère `null` que là où l'exécution locale est aussi impossible (QC Cloud = besoin QuantBook ; Lean = advisory propre, hors scope). Incident fondateur : PRs Tweety-3 C# (#5194/#5199/#5202) mergées avec notebooks à `execution_count: null` + `outputs: []`. Verdict attendu dans le body : `EXEC_PROVED` (outputs réels) vs `STRUCTURAL_ONLY` (refus).

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

### H. Notebook : vrai outil SOTA + problème non-trivial

Source : mandat user 2026-06-21, EPIC #3801. Détail + 5 verdicts : [.claude/rules/sota-not-workaround.md](sota-not-workaround.md).

Toute PR notebook (interne/contributeur) **DOIT** être refusée (`CHANGES_REQUESTED`) si :
1. **Workaround dégradé sans verdict SOTA écrit** : la cellule commit une sortie de substitution (ASCII au lieu d'une image générée, réimplémentation jouet au lieu de la lib, stub au lieu d'un appel de service, sortie fabriquée au lieu d'un backtest) **alors que l'outil réel est installable/invocable/rebranchable**, sans un des 5 verdicts (SOTA-OK / RECOVERABLE-LOCAL / RECOVERABLE-MACHINE / RECOVERABLE-USER-HAND / INTRINSIC) écrit dans le body.
2. **Problème dégénéré** : le notebook démontre un moteur/solveur/modèle sur un cas trivial où le SOTA équivaut à une baseline (ex: BFS vs A* sur graphe à coût uniforme, cf `8905f8845`) → exiger complexification du problème ou ajout d'un problème plus riche (modulo runtime raisonnable).

`APPROVED` malgré 1 ou 2 = complaisance. **Exception PR étudiante** ([student-pr-reviews.md](student-pr-reviews.md)) : NE PAS appliquer H (review bienveillante).
