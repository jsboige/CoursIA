# Dette Technique Branches — Audit 2026-05-27

> Audit complet des branches remote non-mergees sur `origin` (exclut les 31 branches deja identifiees en attente sign-off user).
> Genere par po-2023 sur directive ai-01 `msg-l1smuv`.

## Resume

| Categorie | Count | Action recommandee |
|-----------|-------|--------------------|
| **ZERO-DIFF** (squash-merged, contenu deja dans main) | 78 | **SAFE DELETE** — zero contenu unique |
| **REVIEW** (>14 jours, >400 commits behind, contenu potentiellement obsolete) | 9 | Verifier PR mergees correspondantes avant delete |
| **ACTIVE** (recent ou contenu unique non-merge) | 83 | **CONSERVER** — travail en cours ou non-merge |
| **FORK** (L9DJULO etudiant) | 3 | Conserver (TP etudiant actif) |
| **TOTAL** | **173** | |

Classification par `git cherry main origin/<branch>` — ZERO-DIFF = 0 new commits (= tout le contenu existe dans main via squash merge).

## ZERO-DIFF — SAFE DELETE (78 branches)

Contenu deja present dans main via squash-merge. La branche remote est un residu.

### alpha/ (11 branches) — promotion scaffolding, 11 jours
```
alpha/promotion-infer101
alpha/promotion-lab12-ds-star-workshop
alpha/promotion-lab17-final-project
alpha/promotion-lab5-viz-ml
alpha/promotion-ml1-introduction
alpha/promotion-stable-baseline-1-cartpole
alpha/promotion-sudoku12-z3-csharp
alpha/promotion-sudoku3-genetic-csharp
alpha/promotion-sudoku7-norvig-csharp
alpha/promotion-sudoku8-humanstrategies-csharp
alpha/promotion-sudoku9-graphcoloring-csharp
```

### enrich/ (5 branches) — pedagogy batches 3-7, 12 jours
```
enrich/pedagogy-batch3
enrich/pedagogy-batch4
enrich/pedagogy-batch5
enrich/pedagogy-batch6
enrich/pedagogy-batch7
```

### feat/ cycle 25 (15 branches) — squash-merged work, 14-15 jours
```
feat/cooperative-games-convex-core-route-a-ai01
feat/cycle25-graphsage-po2025
feat/cycle25-har-extended-po2024
feat/cycle25-har-long-horizon-ai01
feat/cycle25-hmm-multiasset-po2024
feat/cycle25-lstm-crypto-fix-po2025
feat/cycle25-qc-934-po2026
feat/cycle25-qc-strategy-po2026
feat/cycle25-tft-crypto-rank-po2025
feat/cycle25-voting-proof-strategy-ai01
feat/h7-stable-snapshot-p1-po2023
feat/lean-bg-prover-po2025-cycle27-cooperative-games-shapley
feat/m10-realized-garch-verdict
feat/m11d-hmm-regime-kelly-ai01
feat/m11g-fee-aware-kelly-null
feat/m11h-kelly-cap-relaxed-sweep
feat/m15-beats-pr
feat/m16-har-asym-doc
feat/readme-bridges-968-po2023
```

### feat/ QC + trading (5 branches) — backtest lots, 3-4 jours
```
feat/qc-py-backtest-lot16
feature/qc-py-backtest-lot6
feature/qc-py-backtest-lot7
feature/qc-py-backtest-lot8
feature/qc-py-backtest-lot9
feature/qc-py13-backtest-lot12
feature/qc-py14-backtest-lot13
feature/qc-py15-backtest-lot14
feature/qc-py16-backtest-lot15
```

### feature/ misc (18 branches) — various squash-merged, 2-12 jours
```
feature/1385-finetuning-FT03
feature/conway-calibration-batch2
feature/curriculum-v2-meta-analysis
feature/game-theory-622-lean8b-correction
feature/leaks-symbolicai-lean
feature/lean-9-emile-jouannet
feature/lean2-student-examples
feature/misc-modernization
feature/po2025-env-documentation
feature/proactive-coordination-governance
feature/prover-b2-searchagent-gate
feature/prover-mmaaz-upstream-snapshot
feature/s4-inverse-vol-ridge
feature/s7-composite-design-skeleton
feature/sc-modernization-batch2
feature/semantic-web-slides
feature/sprint-b-search-enrichment
feature/sudoku-modernization
```

### fix/ (14 branches) — various squash-merged fixes, 2-15 jours
```
fix/1320-gale-shapley-clean
fix/1460-probe-goal-cache
fix/cycle25-prover-build-verified-snapshots
fix/cycle25-prover-comment-preservation-ai01
fix/gradebook-group-code-match
fix/har-model-gil-np-clip
fix/lean-shapley-restructure-forward-refs
fix/planners-fastdownward-13-13
fix/search-solution-leaks
fix/secret-scanner-1076
fix/slides-03-logique-revision-visuelle-23-44-po2026
fix/sw-4b-7b-collision-merge
fix/sweep-checkpoint-clean-1053
```

### chore/ + docs/ (3 branches)
```
chore/catalog-regen-post1457
docs/claude-skepticism-274
docs/student-tp-pr-policy
```

## REVIEW — Verification requise (9 branches)

Branches avec contenu potentiellement unique mais >14 jours et >400 commits behind main. Verifier si les PRs correspondantes ont ete mergees.

| Branch | Age | Ahead | Behind | New commits | Note |
|--------|-----|-------|--------|-------------|------|
| `feat/cycle24-broad-ex08-ex11-research-po2026` | 15d | 2 | 666 | 2 | Research notebooks, likely superseded |
| `feat/cycle24-hmm-alpha-po2024` | 15d | 4 | 667 | 4 | HMM alpha, check if PR merged |
| `feat/cycle25-broad-ch10-audit-po2023` | 15d | 1 | 685 | 1 | Ch10 audit, check if merged |
| `feat/cycle25-voting-l385-prover-bg-po2026` | 15d | 1 | 661 | 1 | Prover BG, 1 commit likely in main |
| `feat/esgf-kit-cycle19-3-strategies` | 16d | 16 | 871 | 16 | Partner course strategies kit, large |
| `feat/lean-median-voter-strict-args` | 16d | 7 | 716 | 7 | Lean proof, check PR |
| `feat/ml-dm-stage012-rerun-m4` | 16d | 14 | 871 | 14 | ML rerun, large |
| `feat/probas-pymc-scaffolds-exec-cycle23` | 15d | 3 | 674 | 3 | Probas scaffolds |
| `fix/sudoku-nn-checkpoints-hardcoded-cell32` | 16d | 17 | 871 | 16 | Sudoku fix, large |

## ACTIVE — Conserver (83 branches)

Branches avec contenu recent (<14 jours) ou contenu unique non-present dans main. A conserver.

### Hot (<3 jours, travail tres recent)
```
feature/1273-prosody-tags-only              (0d, audiobook #1273)
feature/audiobook-prosody-rescue-f1-f4       (0d, ai-01 worktree)
feature/l4-decision-transformer-1454         (0d, just merged via #1615)
feature/lean-consolidation-harness-p1-p2-p3  (0d, po-2026 harness)
feature/symbolic-learning-sl3-sl4           (0d, just merged via #1614)
fix/1240-slides-image-positioning           (0d, slides fix)
fix/1273-prosody-cleanup-report             (0d, prosody cleanup)
feature/prove-doctor-optimal-l795           (2d, Lean prover)
feature/prove-gale-shapley-man-optimal      (2d, Lean prover)
feature/prove-lattice-no-cross-axiom        (2d, Lean prover)
feature/sw8-tp-conversion                   (2d, SW TP)
fix/1460-probe-goal-cache                   (2d, prover harness)
fix/diarization-auto-detect-creds           (2d, diarization)
pr-1517                                     (2d, SW8 alias?)
```

### Warm (3-7 jours, travail en cours)
```
feature/1404-symboliclearning               (3d, SL series)
feature/1452-calibration-batch-1             (3d, Lean calibration)
feature/1452-conway-calibration-scaffold     (3d, Lean calibration)
feature/623-maturity-heuristic-improvement   (3d, catalog)
feature/epic-1455-sw-consolidation           (3d, SW consolidation)
feature/modernization-remaining             (3d, modernization batch)
feature/qc-py-backtest-lot17                (3d, QC execution)
feature/sc-modernization-batch2             (3d, SmartContracts)
feature/sprint-b-apps-reexec                (3d, sprint B)
feature/sprint-b-csp-reexec                 (3d, sprint B)
feature/sprint-b-gametheory-reexec          (3d, sprint B)
feature/sprint-b-search-batch4              (3d, sprint B)
feature/sprint-b-sw-python-fixes            (3d, sprint B)
feature/sprint-b-symbolicai-batch3          (3d, sprint B)
feature/student-lilou-mayot-semanticweb-tp  (4d, student TP)
feature/student-lilou-mayot-sw10            (4d, student TP)
feature/qc-py-backtest-lot2..5             (4d, QC lots)
feature/qc-py-voie1-execution               (5d, QC voie 1)
feature/gale-shapley-woman-pessimal         (6d, Lean proof)
feature/issue-1299-ventilation              (7d, ventilation)
feature/lean-end-exercises                  (6d, Lean exercises)
feature/symbolicai-planners-exercices-end   (7d, planners)
docs/readme-enrich-symbolicai-968           (7d, README)
fix/1334-spass-output                       (6d, SPASS fix)
fix/semanticweb-exercice-rename-revert      (6d, SW fix)
fix/tweety-dependencies                     (6d, Tweety fix)
fix/planners-1-descaffolding               (6d, planners fix)
fix/qcpy-exec-lot1..5                      (6d, QC Py exec lots)
fix/slides-03-logique-bug-slide-53          (8d, slides fix)
fix/esgf-deck2-m15-beats                   (8d, partner course)
fix/esgf-deck3-curriculum-v2               (8d, partner course)
```

### Cold (>7 jours mais contenu unique)
```
feature/epic-1028-p1-analytique             (9d, audiobook)
feature/slides-S7-lean                      (9d, slides)
feature/s2-vol-ensemble-dm                 (10d, DM research)
feature/s8-pilote-trend-long-horizon       (10d, DM research)
feature/lean-bondareva-2proofs             (11d, Lean proof)
feature/lean-gsstate-maximal              (11d, Lean proof)
feature/lean-sensitivity-theorem-1150     (11d, Lean proof)
feature/prover-c35-director-fix           (11d, prover fix)
feature/sweep-checkpoint-resume           (11d, sweep)
feat/lean-mobius-shapley                  (12d, Lean proof)
feat/m12-m11ef-qc-research               (12d, QC research)
feat/m15-lstm-rv                          (12d, LSTM research)
feat/portfolio-hybrid-phase1              (13d, portfolio)
feat/portfolio-hybride-skeleton           (13d, portfolio)
feat/qc-py-18-alpha-to-beta              (14d, QC Py exec)
feat/qc-playwright-batch1-esgf-po2026    (14d, Playwright partner course)
feat/cycle25-har-asymmetric-po2024       (14d, HAR research)
feat/cycle25-prover-voting-l355-wave3-po2026 (14d, prover)
feat/h7-p2-qc-never-executed-po2026     (14d, H7 audit)
fix/short-tail-consolidation-cycle26     (14d, consolidation)
fix/alpha-enrichment-needs-work-batch1   (12d, enrichment fix)
fix/catalog-maturity-heuristic-b2        (13d, catalog fix)
fix/fort-boyard-csharp-cs7021           (11d, C# fix)
fix/prover-f7-director-escalation       (11d, prover fix)
fix/lean-shapley-restructure-forward-refs (14d, Lean fix)
chore/prover-postmortem-kb-update        (11d, prover docs)
feature/lean-galeshapley-runsteps        (12d, Lean proof, 23 commits)
feature/sprint-b-symbolicai-batch1..2    (4d, sprint B)
docs/prover-b2-retrospective-1224        (7d, prover docs)
feature/lean-prove-meet-bijective        (2d, Lean proof)
feature/symbolicai-semanticweb-exercices-end (6d, SW exercises)
```

## FORK Branches (3) — TP etudiant

| Branch | Age | Auteur | Note |
|--------|-----|--------|------|
| `L9DJULO/feature/csp-4-scheduling-exercices` | 36d | Jules Lange | TP CSP |
| `L9DJULO/feature/sw9-jsonld-jules-lange` | 6d | Jules Lange | TP SW |
| `L9DJULO/tp/search-uninformed-jules-lange` | 37d | Jules Lange | TP Search |

Conserver tant que les TPs sont en cours.

## Recommandations

### Batch 1 — Safe delete (78 branches, ZERO-DIFF)
```bash
# Commande de nettoyage (dry-run prefixe avec echo)
git push origin --delete alpha/promotion-infer101 alpha/promotion-lab12-ds-star-workshop ...
# OU en batch:
for b in $(cat zero-diff-branches.txt); do git push origin --delete "$b"; done
```
**Risque**: ZERO. Tout le contenu existe deja dans main.

### Batch 2 — REVIEW (9 branches)
Verifier PRs correspondantes dans `gh pr list --state merged` avant suppression.
Priorite basse — peut attendre le batch suivant.

### Batch 3 — Fork (3 branches)
Conserver. Supprimer uniquement apres fin des TPs.

## Methodologie

1. `git fetch --all --prune`
2. `git branch -r --no-merged main` — liste 170 branches origin/ + 3 forks
3. `git cherry main origin/<branch>` — classification ZERO-DIFF (0 new) vs ACTIVE
4. Classification secondaire par age et distance to main
5. Exclusion des 31 branches deja identifiees (QC zero-diff + enrich/alpha en attente sign-off user)
