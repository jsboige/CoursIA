# Couverture `proof-integrity` des workflows Lean

**Mesure au 2026-09-21** (cycle c.760, issue #17097, grain `MED/guard -- lane myia-po-2023:CoursIA-2`).

Cette page documente la couverture du gate `proof-integrity` sur les lakes Lean first-party du dépôt. Elle est produite par :

```bash
python scripts/ci/measure_proof_integrity_coverage.py [--json]
```

Le script applique exactement la procédure prescrite par `.claude/rules/pr-review-discipline.md` §B.3 (« câblage = exactement les workflows appelant `lean-axiom.yml` »).

## Synthèse au 2026-09-21

| | Compte |
|---|---|
| Workflows dédiés appelant `lean-axiom.yml` (câblés) | **12** |
| Workflows Lean sans `lean-axiom` (lean-build, lean-ci-matrix, lean-i18n-drift, lean-visibility-advisory) | **4** |
| Lakes servis par `lean-ci-matrix.yml` (via `lean-build.yml`, sans `lean-axiom`) | **19** |
| Lakes ayant PERDU leur gate par suppression de fichier (`git log -D`) | **0** |
| Lakes JAMAIS câblés sur `lean-axiom` | **19** (lakes du manifest) |

## Détail des 12 workflows câblés

```
lean-asymmetric-information.yml: 4 mentions lean-axiom
lean-conway.yml: 7 mentions lean-axiom
lean-formal-groups.yml: 3 mentions lean-axiom
lean-galois.yml: 5 mentions lean-axiom
lean-grothendieck.yml: 6 mentions lean-axiom
lean-hecke.yml: 3 mentions lean-axiom
lean-knot.yml: 7 mentions lean-axiom
lean-mimo.yml: 3 mentions lean-axiom
lean-percolation.yml: 3 mentions lean-axiom
lean-planning.yml: 4 mentions lean-axiom
lean-sensitivity.yml: 4 mentions lean-axiom
lean-social-choice.yml: 5 mentions lean-axiom
```

## Les 19 lakes du manifest `ci_lakes.json` (sans gate)

`scripts/lean/ci_lakes.json` liste 19 lakes dispatchés par `lean-ci-matrix.yml` :

```
sudoku_lean               sorry-baseline=0
kelly_lean                sorry-baseline=0
minimax_lean              sorry-baseline=0
search_lean               sorry-baseline=0
assignment_lean           sorry-baseline=0
discrepancy_lean          sorry-baseline=0
argumentation_lean        sorry-baseline=0
calibration_lean          sorry-baseline=0
conway_cgt_lean           sorry-baseline=0
erc20_lean                sorry-baseline=0
finiteness_lean           sorry-baseline=0
lean_game_defs            sorry-baseline=0
lean_game_defs_ext        sorry-baseline=0
learning_theory_lean      sorry-baseline=0
decision_theory_lean      sorry-baseline=2
game_theory_lean          sorry-baseline=1
mathlib_examples          sorry-baseline=0
social_choice_lean_peters sorry-baseline=0
tegmark_muh_lean          sorry-baseline=0
```

Aucun de ces 19 lakes n'a **perdu** son gate par suppression (le `git log --diff-filter=D` ne retourne **aucun** fichier supprimé). Les 19 sont entrés directement dans la matrice via #16709 / #16716 sans transiter par un dispatcher dédié — donc ils ne l'ont **jamais eu**.

## Ce que cela signifie pour §B.3

Le critère `B.3` de `pr-review-discipline.md` (« Proof integrity SUCCESS — câblé ou non applicable ») demande de **lire explicitement** dans le body PR si le gate est **câblé** sur le lake modifié. Pour les 19 lakes du manifest, le verdict `B.3 non applicable cas (a)` (câblage absent) **doit être déclaré** par le reviewer sur **chaque** PR qui touche ces fichiers `.lean`, à défaut d'un câblage partagé.

Constat pendant la passe de merge du 2026-09-21 sur **#16794** (`learning_theory_lean`) : le gate proof-integrity **n'a pas rougi** au rollup, mais c'est par construction — il n'existe pas. La PR est passée sur la base d'une vérification de substitution écrite en commentaire (cf. comment `5753926844`).

## Recommandation (issue de suivi)

Le **fix** est mécanique : câbler `lean-axiom.yml` sur chacun des 19 lakes du manifest, soit en l'appelant depuis `lean-build.yml` (job `ci-matrix` paramétré par lake), soit en restaurant un dispatcher dédié par lake. Cette correction est **hors scope** de la présente PR (elle modifie un workflow CI partagé) et fait l'objet d'une **issue de suivi** postée avec cette PR.

## Critère de réexécution

Pour trancher §B.3 sans enquêter, un reviewer peut rejouer :

```bash
python scripts/ci/measure_proof_integrity_coverage.py
```

Sortie stable, reproductible, lecture directe.

## Références

- **#17097** (issue) — ci(lean): les lakes servis par lean-ci-matrix.yml n'ont aucun gate proof-integrity
- **.claude/rules/pr-review-discipline.md §B.3** — câblage proof-integrity
- **#16709** — feat(ci,#13751): pilote matrice lean-ci — 6 dispatchers fondus dans lean-ci-matrix.yml
- **#16716** — feat(ci,#13751): pilote matrice lean-ci — suite
- **#16487** — fix(ci,#15652): drop branches:[main] from paths-scoped lean-* workflows (note la séparation lean-ci-matrix.yml)
- **#8677** — premier incident (criterion 4 = B.3)
- **#8782** — second incident (B.3 lu en non applicable cas b)
- **`scripts/lean/count_code_sorry.py --json`** — l'instrument canonique de mesure de dette formelle

## Statut au 2026-09-21

| Mesure | Valeur |
|---|---|
| `cabled_count` | 12 |
| `matrix_only_count` | 4 |
| `perdus_count` | 0 |
| `jamais_eu_count` | 0 |
| `manifest_count` | 19 |
| `cabled_lakes` | 12 (asymmetric-information, conway, formal-groups, galois, grothendieck, hecke, knot, mimo, percolation, planning, sensitivity, social-choice) |
| `sans_couverture` | 19 (ci_lakes.json) |

— po-2023 c.760, 2026-09-21T19:00Z
