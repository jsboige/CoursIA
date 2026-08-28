# Lean 4 Projects Inventory — QuantConnect

Cross-directory inventory of all Lean 4 formalization projects under `QuantConnect/`.

Réconcilié le 2026-08-28 contre les pins effectifs (`lean-toolchain`, `lake-manifest.json`) et le
module-set réel du disque (issue #13366, matrice #13121 tranche 3). Comptes `sorry` mesurés avec
l'instrument canonique `scripts/lean/count_code_sorry.py --lake <root> --json` (champ
`distinct_code_sorry`), jamais `grep -c sorry`.

## Summary

**Lakes actifs (1)** :

| Directory | Toolchain | Production sorry | Modules | Status |
|-----------|-----------|-----------------|---------|--------|
| `kelly_lean` | v4.32.1 | 0 | `Kelly/{Kelly, Bet, Growth}` (3 FR + 3 `_en`) | COMPLETE |

---

## Directories

### 1. kelly_lean

**Objective**: optimalité du critère de Kelly — fraction optimale de mise, croissance log-optimale
du capital (`growthGrad_kelly_zero` : dérivée du growth nulle au point Kelly), faisabilité de la
fraction (`kellyFrac_feasible`), et formalisation du pari équivalent (`q`, `pq_add_eq_one`).

**Toolchain**: v4.32.1 | **Dependencies**: Mathlib4

| Module group | sorry | Content |
|--------------|-------|---------|
| `Kelly/Kelly` (FR + `_en`) | 0 | critère de Kelly : `kellyFrac_feasible`, richesses win/lose au point Kelly, `growthGrad_kelly_zero`, `growth_diff_le` |
| `Kelly/Bet` (FR + `_en`) | 0 | pari équivalent : `q`, `q_pos`, `q_lt_one`, `pq_add_eq_one`, `winWealth` |
| `Kelly/Growth` (FR + `_en`) | 0 | croissance : `growth_zero`, `growthGrad_zero` |

**CI wiring**: caller workflow [`lean-kelly.yml`](../../.github/workflows/lean-kelly.yml)
(push `main`, paths `MyIA.AI.Notebooks/QuantConnect/kelly_lean/**.lean` + `lakefile.*`), pipeline `standalone-tactic`.

**Notebooks in-lake (2, C.2 OK)** : `Kelly_companion.ipynb` (Python) et
`Kelly_companion_lean.ipynb` (Lean) à la racine du lake.
