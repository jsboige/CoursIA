# Lean 4 Projects Inventory — SymbolicAI/Planners

Cross-directory inventory of all Lean 4 formalization projects under `SymbolicAI/Planners/`.

Réconcilié le 2026-08-28 contre les pins effectifs (`lean-toolchain`, `lake-manifest.json`) et le
module-set réel du disque (issue #13366, matrice #13121 tranche 3). Comptes `sorry` mesurés avec
l'instrument canonique `scripts/lean/count_code_sorry.py --lake <root> --json` (champ
`distinct_code_sorry`), jamais `grep -c sorry`.

## Summary

**Lakes actifs (1)** :

| Directory | Toolchain | Production sorry | Modules | Status |
|-----------|-----------|-----------------|---------|--------|
| `planning_lean` | v4.32.1 | 0 | `Planning/{Strips, Relaxation, Admissibility}` (3 FR + 3 `_en`) | COMPLETE |

Note de cheminement : la matrice #13121 tranche 3 référençait `MyIA.AI.Notebooks/Planners/planning_lean` ;
le chemin effectif au disque est `MyIA.AI.Notebooks/SymbolicAI/Planners/planning_lean` (inventaire aligné
sur le disque).

---

## Directories

### 1. planning_lean

**Objective**: admissibilité de la relaxation sans-delete en planification STRIPS — le coût du plan
relaxé optimal `h⁺` n'excède jamais le coût du plan réel optimal `h*`
(`relaxed_plan_admissible` + `relaxed_plan_witness`), sur les sémantiques `step` (réelle) et
`stepR` (relaxée) avec `step_subset_stepR` et `run_mono`.

**Toolchain**: v4.32.1 (pin effectif mesuré `lean-toolchain` ; la prose du README annonce encore
`v4.31.0-rc1` — périmée, à corriger séparément) | **Dependencies**: Mathlib4

| Module group | sorry | Content |
|--------------|-------|---------|
| `Planning/Strips` (FR + `_en`) | 0 | domaine STRIPS : `applicable`, `step`, `stepR`, `goalSatisfied`, `step_subset_stepR` |
| `Planning/Relaxation` (FR + `_en`) | 0 | exécution relaxée : `run`, `runR`, `reaches`, `reachesR`, `run_mono` |
| `Planning/Admissibility` (FR + `_en`) | 0 | théorème-phare : `relaxed_plan_admissible`, `relaxed_plan_witness` |

**CI wiring**: caller workflow [`lean-planning.yml`](../../../.github/workflows/lean-planning.yml)
(push `main`, paths `MyIA.AI.Notebooks/SymbolicAI/Planners/planning_lean/**.lean` + `lakefile.*`), pipeline `standalone-tactic`.
