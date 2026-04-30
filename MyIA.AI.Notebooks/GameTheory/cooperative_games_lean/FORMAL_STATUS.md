# Cooperative Games Lean - Formal Verification Status

## Build Info

| Item | Value |
|------|-------|
| Lean toolchain | `leanprover/lean4:v4.28.0-rc1` |
| Mathlib | pinned via lake-manifest.json |
| Total sorry | **7** (3 Basic + 4 Shapley) |
| Total lines | 398 |
| Total theorems | 11 |
| Total definitions | 29 |

**Note**: Toolchain still on v4.28.0-rc1. Upgrade to v4.29.1 recommended (see social_choice_lean for precedent).

## Per-File Status

### CooperativeGames/Basic.lean — FOUNDATIONAL

| Metric | Value |
|--------|-------|
| Lines | 167 |
| Definitions | 12 |
| Theorems | 4 |
| sorry | **3** |
| Status | FORMAL-PARTIAL |

Key definitions: `Coalition`, `TUGame`, `Superadditive`, `Convex`, `marginalContribution`,
`unanimityGame`, `majorityGame`, `Allocation`, `Core`, `CoreEmpty`, `Balanced`.

sorry locations:
- Line 136: `bondareva_shapski` theorem body (3 sorry)
- Line 153: `convex_core_nonempty` theorem body (2 sorry, partially proved)
- Line 165: auxiliary proof

### CooperativeGames/Shapley.lean — SHAPLEY VALUE

| Metric | Value |
|--------|-------|
| Lines | 231 |
| Definitions | 17 |
| Theorems | 7 |
| sorry | **4** |
| Status | FORMAL-PARTIAL |

Key definitions: `Solution`, `Efficiency`, `Symmetry`, `NullPlayerAxiom`, `Additivity`,
`shapleyCoef`, `shapleyValue`, `shapleySolution`, `WeightedVotingGame`, `Critical`,
`BanzhafRaw`, `VetoPlayer`, `Dictator`, `DummyPlayer`.

sorry locations:
- Line 117: `shapley_null_player` proof
- Line 132: `shapley_unanimity` proof
- Line 160: `shapley_symmetric` proof
- Line 197: `shapley_uniqueness` proof

## Theorem Inventory

### Fully Certified (0 sorry)

None yet.

### Partially Proved (contains sorry)

| Theorem | File | sorry | Statement |
|---------|------|-------|-----------|
| `superadditive_empty_nonneg` | Basic.lean | 0 | Superadditive games have v(empty) >= 0 |
| `superadditive_grand_coalition_nonneg_of_nonneg_singletons` | Basic.lean | 0 | Grand coalition value nonneg |
| `bondareva_shapski` | Basic.lean | 3 | Core nonempty iff balanced (Bondareva-Shapley) |
| `convex_core_nonempty` | Basic.lean | 2 | Convex games have nonempty core |
| `shapley_null_player` | Shapley.lean | 1 | Shapley value = 0 for null players |
| `shapley_unanimity` | Shapley.lean | 1 | Shapley value on unanimity games |
| `shapley_efficient` | Shapley.lean | 0 | Shapley value is efficient |
| `shapley_symmetric` | Shapley.lean | 1 | Shapley value treats symmetric players equally |
| `shapley_additive` | Shapley.lean | 0 | Shapley value is additive |
| `shapley_uniqueness` | Shapley.lean | 1 | Shapley value is the unique solution satisfying axioms |
| `dummy_shapley_zero` | Shapley.lean | 0 | Dummy players get zero Shapley value |

## Certification Level

| File | Level |
|------|-------|
| Basic.lean | PARTIAL (3 sorry — Bondareva-Shapley theorem) |
| Shapley.lean | PARTIAL (4 sorry — key Shapley axioms) |

**Project certification: PARTIAL** — 7 sorry remaining across 2 files.

## Remaining Work

| Priority | Task | sorry |
|----------|------|-------|
| HIGH | Complete `bondareva_shapski` proof | 3 |
| HIGH | Complete `shapley_uniqueness` proof | 1 |
| MEDIUM | Complete `shapley_null_player` proof | 1 |
| MEDIUM | Complete `shapley_unanimity` proof | 1 |
| MEDIUM | Complete `shapley_symmetric` proof | 1 |
| LOW | Upgrade toolchain to v4.29.1 (follow social_choice_lean) | 0 |

## References

- Shapley, L.S. (1953). "A Value for N-Person Games"
- Bondareva, O.N. (1963). "Some Applications of Linear Programming Methods to the Theory of Cooperative Games"
- Shapley, L.S. (1967). "On Balanced Sets and Cores"

## History

| Date | Change | Commit |
|------|--------|--------|
| 2026-01-31 | Initial creation with TU games, Shapley value | initial |
| 2026-04-30 | FORMAL_STATUS.md created | PR-G |
