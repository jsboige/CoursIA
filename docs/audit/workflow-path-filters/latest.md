# Audit workflow path-filters

**Generated** : 2026-09-02T09:57:04.838900+00:00
**Workflows dir** : `C:\dev\CoursIA-12773-tranche2b\.github\workflows`

## Summary

| Metrique | Valeur |
|---|---|
| Total workflows | 131 |
| Avec `pull_request` trigger | 69 |
| **Avec filtre paths/paths-ignore** | **64** |
| Sans filtre | 5 |
| - dont required (gates/advisories) | 4 |
| - dont optional (a investiguer) | 1 |
| Sans `pull_request` trigger | 62 |

## Sans filtre `paths`/`paths-ignore`

### Required (gates/advisories - non-concerne par l'audit)

- `always-on-guards.yml`
- `always-on-metadata-guards.yml`
- `pr-gate.yml`
- `secret-scan.yml`

### Optional (a investiguer - devrait avoir un filtre)

- `orphaned-delivery-scan.yml`

## Avec filtre `paths`/`paths-ignore`

| Workflow | paths_count |
|---|---|
| `arxiv-attributions-guard.yml` | 10 |
| `banner-guard.yml` | 3 |
| `bare-cross-dir-load-gate.yml` | 3 |
| `bash-syntax-advisory.yml` | 2 |
| `catalog-drift.yml` | 5 |
| `cell-order-gate.yml` | 3 |
| `consecutive-code-cells-advisory.yml` | 2 |
| `harness-coauthor-guard.yml` | 7 |
| `hooks-parity.yml` | 4 |
| `ict-tests.yml` | 2 |
| `label-paths-guard.yml` | 3 |
| `lean-argumentation.yml` | 4 |
| `lean-assignment.yml` | 4 |
| `lean-asymmetric-information.yml` | 13 |
| `lean-calibration.yml` | 4 |
| `lean-conway-cgt.yml` | 5 |
| `lean-conway.yml` | 7 |
| `lean-decision-theory.yml` | 4 |
| `lean-discrepancy.yml` | 4 |
| `lean-erc20.yml` | 4 |
| `lean-finiteness.yml` | 4 |
| `lean-galois.yml` | 9 |
| `lean-game-defs-ext.yml` | 3 |
| `lean-game-defs.yml` | 3 |
| `lean-game-theory.yml` | 5 |
| `lean-grothendieck.yml` | 10 |
| `lean-i18n-drift.yml` | 3 |
| `lean-kelly.yml` | 4 |
| `lean-knot.yml` | 10 |
| `lean-learning-theory.yml` | 4 |
| `lean-mathlib-examples.yml` | 4 |
| `lean-mimo.yml` | 4 |
| `lean-minimax.yml` | 4 |
| `lean-planning.yml` | 4 |
| `lean-search.yml` | 4 |
| `lean-sensitivity.yml` | 8 |
| `lean-social-choice-peters.yml` | 4 |
| `lean-social-choice.yml` | 12 |
| `lean-sudoku.yml` | 4 |
| `manifest-description-visuelle-gate.yml` | 3 |
| `markdown-claims-output-advisory.yml` | 4 |
| `markdown-rendering-guard.yml` | 6 |
| `ml-tests.yml` | 4 |
| `notebook-cell-source-parses.yml` | 3 |
| `notebook-exec-sequence-ratchet.yml` | 4 |
| `notebook-execution-required.yml` | 5 |
| `notebook-interp-positioning.yml` | 4 |
| `notebook-navlink-check.yml` | 4 |
| `notebook-papermill-ratchet.yml` | 3 |
| `notebook-validation.yml` | 1 |
| `owui-playwright-check.yml` | 2 |
| `pip-leak-guard.yml` | 4 |
| `prose-counts-guard.yml` | 2 |
| `quantconnect-notebook-freshness.yml` | 4 |
| `quarto-pages-deploy.yml` | 8 |
| `scan-md-hierarchy-drift.yml` | 3 |
| `scripts-tests.yml` | 18 |
| `solution-leak-guard.yml` | 4 |
| `source-output-ratchet.yml` | 3 |
| `translation-drift.yml` | 3 |
| `translation-guard.yml` | 11 |
| `twin-parity.yml` | 3 |
| `unique-check-run-names-guard.yml` | 3 |
| `validation-matrix.yml` | 2 |

## Hygiene de checkout (fetch-depth: 0 sans filter: blob:none)

| Metrique | Valeur |
|---|---|
| Workflows PR clonant sans clone partiel | **5** |
| - conformes (blob:none present) | 16 |
| - exclus (clone complet necessaire) | 1 |
| Machines a clone (PR trigger + fetch-depth: 0) | 22 |

### Non conformes (a corriger en clone partiel)

- `consecutive-code-cells-advisory.yml`
- `harness-coauthor-guard.yml`
- `notebook-cell-source-parses.yml`
- `scan-md-hierarchy-drift.yml`
- `source-output-ratchet.yml`

### Controle positif hygiene-checkout

- Ran : `True`
- Attendu : `bad-clone.yml, bad-target.yml`
- Detecte : `bad-clone.yml, bad-target.yml`
- **OK**
