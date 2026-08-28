# Lean 4 Projects Inventory — SymbolicAI/Tweety

Cross-directory inventory of all Lean 4 formalization projects under `SymbolicAI/Tweety/`.

Réconcilié le 2026-08-28 contre les pins effectifs (`lean-toolchain`, `lake-manifest.json`) et le
module-set réel du disque (issue #13366, matrice #13121 tranche 3). Comptes `sorry` mesurés avec
l'instrument canonique `scripts/lean/count_code_sorry.py --lake <root> --json` (champ
`distinct_code_sorry`), jamais `grep -c sorry`.

## Summary

**Lakes actifs (1)** :

| Directory | Toolchain | Production sorry | Modules | Status |
|-----------|-----------|-----------------|---------|--------|
| `argumentation_lean` | v4.32.1 | 0 | `Argumentation/{Basic, Fundamental, Grounded, Characteristic, Extensions}` (5 FR + 5 `_en`) + umbrella `Argumentation.lean` | COMPLETE |

---

## Directories

### 1. argumentation_lean

**Objective**: théorie de l'argumentation abstraite de Dung (1995) — cadres d'argumentation (AF),
les extensions canoniques (admissible, complète, grounded, preferred, stable), lemme fondamental
et fonction caractéristique, au-dessus de Mathlib.

**Toolchain**: v4.32.1 | **Dependencies**: Mathlib4

| Module group | sorry | Content |
|--------------|-------|---------|
| `Argumentation/Basic` (FR + `_en`) | 0 | conflit et défense : `conflictFree`, `defends`, `defendedBy`, `conflictFree_empty` |
| `Argumentation/Fundamental` (FR + `_en`) | 0 | lemme fondamental : `fundamental_lemma` (+ variantes `defends`/`defends_self`) |
| `Argumentation/Grounded` (FR + `_en`) | 0 | sémantique grounded : `grounded_fixed`, `grounded_defends_iff_mem`, `grounded_least_complete`, `F_preserves_conflictFree` |
| `Argumentation/Characteristic` (FR + `_en`) | 0 | fonction caractéristique : `characteristic`, `mem_characteristic_iff`, `characteristic_eq_defendedBy` |
| `Argumentation/Extensions` (FR + `_en`) | 0 | hiérarchie des extensions : `Admissible`, `Complete`, `grounded`, `Preferred` |
| `Argumentation.lean` (umbrella) | 0 | imports agrégés du lake |

**CI wiring**: caller workflow [`lean-argumentation.yml`](../../../.github/workflows/lean-argumentation.yml)
(push `main`, paths `MyIA.AI.Notebooks/SymbolicAI/Tweety/argumentation_lean/**.lean` + `lakefile.*`), pipeline `standalone-tactic`.
