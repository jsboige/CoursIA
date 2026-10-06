# Audit CI matrix workflows non-lean (2026-10-06) — issue #19426

**Contexte** : la PR #19381 a traité les 23 dispatchers `lean-*.yml` + `lean-ci-matrix.yml` + `lean-visibility-advisory.yml` (issue #15652). Au-delà du périmètre lean, ce grain vérifie que les workflows CI non-lean utilisant `strategy: matrix:` ont une configuration de triggers cohérente (push + pull_request avec `branches: [main]`, ou absence justifiée de ces triggers).

**Méthodologie** : `yaml.safe_load` sur les 160 fichiers `.github/workflows/*.yml`, filtre des workflows ayant au moins un job `strategy: matrix:`, vérification de la cohérence des triggers (présence/absence de `push` et `pull_request`, présence de `branches:`).

## Résultats — 0 défaut mesuré

| Workflow | Triggers | matrix jobs | branches filter | Verdict |
|---|---|---|---|---|
| `ict-tests.yml` | push + pull_request + workflow_dispatch | `[ict-tests]` (2 suites via `matrix.include`) | oui (push + pull_request) | **OK** |
| `runner-starvation-advisory.yml` | schedule + workflow_dispatch | `[starve]` (2 labels via `matrix.include`) | N/A — pas de trigger PR | **OK** |
| `slow-lane.yml` | schedule + workflow_dispatch | `[codeql-scheduled]` (4 langages via `matrix`) | N/A — pas de trigger PR | **OK** |
| `lean-build.yml` | workflow_dispatch | `[ci-matrix]` | N/A — dispatch only | **OK** (couvert par #19381) |

`lean-ci-matrix.yml` (dispatcher de `lean-build.yml` via `uses:`) n'apparaît pas dans cette liste — il n'a pas de `strategy: matrix:` propre, c'est un wrapper qui passe la liste des lakes touchés à `lean-build.yml::ci-matrix`.

## Verdict

**0/4 workflows non-lean avec matrix ont un défaut de trigger.** Le pattern de #19381 (matrix unique + branches filter sur push et pull_request quand le workflow réagit aux PRs) est correctement généralisé à `ict-tests.yml`, et les workflows schedule-only (`runner-starvation-advisory.yml`, `slow-lane.yml`) n'ont pas besoin de `branches:`.

Aucune PR de correction nécessaire sur ce périmètre. Le suivi des autres workflows non-lean (qui n'utilisent pas `matrix:` mais peuvent avoir d'autres défauts) reste un chantier distinct.

## Livrables

- `docs/reference/ci-matrix-audit-2026-10-06.md` (ce fichier) — résultat de l'audit
- `scripts/ci/audit_matrix_workflows.py` (à venir si besoin récurrent) — automatisation

## Issue parente : #19426 · #15652
