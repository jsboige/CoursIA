# Cooperative Games Lean - Formal Verification Status

## Build Info

| Item | Value |
|------|-------|
| Lean toolchain | `leanprover/lean4:v4.30.0-rc2` |
| Mathlib | pinned via lake-manifest.json |
| Total sorry | **1** (0 Basic + 1 Shapley) |
| Honest unprovable (in Mathlib) | **0** |
| Total lines | ~990 (Basic 387 + Shapley 603) |
| Total theorems | 10 |
| Total definitions | 29 |

**Note**: Toolchain bumped to v4.30.0-rc2 (PR #1015). Bondareva backward proved (PR #1020).

## Per-File Status

### CooperativeGames/Basic.lean — FOUNDATIONAL

| Metric | Value |
|--------|-------|
| Definitions | 12 |
| Theorems | 4 |
| sorry | **0** |
| Status | FORMAL-COMPLETE |

Key definitions: `Coalition`, `TUGame`, `Superadditive`, `Convex`, `marginalContribution`,
`unanimityGame`, `majorityGame`, `Allocation`, `Core`, `CoreEmpty`, `Balanced`.

Previously-proved theorems (sorry resolved):
- `bondareva_shapley_backward` (PR #1020, po-2026, 2026-05-13)
- `convex_core_nonempty` (PR #981, Route A marginal vectors)

### CooperativeGames/Shapley.lean — SHAPLEY VALUE

| Metric | Value |
|--------|-------|
| Definitions | 17 |
| Theorems | 7 |
| sorry | **1** |
| Status | FORMAL-PARTIAL |

Key definitions: `Solution`, `Efficiency`, `Symmetry`, `NullPlayerAxiom`, `Additivity`,
`shapleyCoef`, `shapleyValue`, `shapleySolution`, `WeightedVotingGame`, `Critical`,
`BanzhafRaw`, `VetoPlayer`, `Dictator`, `DummyPlayer`.

Previously-proved theorems (sorry resolved):
- `shapley_null_player` (PR earlier in 2026-04)
- `shapley_unanimity` (PR #791)
- `shapley_symmetric` (PR earlier in 2026-04)
- `shapleyCoef_top` (PR #757)
- `bondareva_shapley_forward` (PR #802)

sorry locations:
- Line 570: `shapley_uniqueness` — WIP_HARD (Mobius decomposition into unanimity games;
  DEMO 6/8 in `prover/config.py` target this).

## Theorem Inventory

### Fully Certified (0 sorry)

| Theorem | File | Statement |
|---------|------|-----------|
| `superadditive_empty_nonneg` | Basic.lean | v(empty) >= 0 (trivial) |
| `superadditive_grand_coalition_nonneg_of_nonneg_singletons` | Basic.lean | Grand coalition value nonneg |
| `bondareva_shapley_forward` | Basic.lean | Core nonempty implies balanced |
| `bondareva_shapley_backward` | Basic.lean | Balanced implies Core nonempty (PR #1020) |
| `convex_core_nonempty` | Basic.lean | Convex games have nonempty Core (PR #981) |
| `shapley_efficient` | Shapley.lean | Shapley value is efficient |
| `shapley_additive` | Shapley.lean | Shapley value is additive |
| `shapley_null_player` | Shapley.lean | Shapley value = 0 for null players |
| `shapley_unanimity` | Shapley.lean | Shapley value on unanimity games |
| `shapley_symmetric` | Shapley.lean | Shapley value treats symmetric players equally |
| `shapleyCoef_top` | Shapley.lean | Shapley coefficient for full coalition |
| `dummy_shapley_zero` | Shapley.lean | Dummy players get zero Shapley value |

### Partially Proved (contains sorry)

| Theorem | File | Line | Category | sorry | Statement |
|---------|------|------|----------|-------|-----------|
| `shapley_uniqueness` | Shapley.lean | 570 | WIP_HARD | 1 | Shapley value is unique solution satisfying axioms |

## Certification Level

| File | Level |
|------|-------|
| Basic.lean | COMPLETE (0 sorry) |
| Shapley.lean | PARTIAL (1 sorry — WIP, Shapley uniqueness via Mobius) |

**Project certification: PARTIAL** — 1 sorry remaining, WIP_HARD (0 HONEST_UNPROVABLE).

## Remaining Work

| Priority | Task | sorry | Category |
|----------|------|-------|----------|
| HIGH | Complete `shapley_uniqueness` proof | 1 | WIP_HARD (DEMO 6/8) |

## References

- Shapley, L.S. (1953). "A Value for N-Person Games"
- Bondareva, O.N. (1963). "Some Applications of Linear Programming Methods to the Theory of Cooperative Games"
- Shapley, L.S. (1967). "On Balanced Sets and Cores"
- Shapley, L.S. (1971). "Cores of Convex Games"

## History

| Date | Change | Commit |
|------|--------|--------|
| 2026-01-31 | Initial creation with TU games, Shapley value | initial |
| 2026-04-30 | FORMAL_STATUS.md created | PR-G |
| 2026-04-30 | `shapleyCoef_top` proved | PR #757 |
| 2026-04-30 | `shapley_unanimity` 2->1 sorry | PR #791 |
| 2026-05-01 | `bondareva_shapley_forward` proved | PR #802 |
| 2026-05-12 | Reclassified bondareva_shapley_backward: HONEST_UNPROVABLE -> WIP_HARD (Farkas available in Mathlib 2025); added BONDAREVA_SHAPLEY_HARDNESS.md | Cycle 28 Track A |
| 2026-05-13 | Toolchain bump to v4.30.0-rc2; `bondareva_shapley_backward` proved (0 sorry Basic.lean); `convex_core_nonempty` proved | PR #1015, #1020, #981 |
| 2026-05-13 | FORMAL_STATUS realigned: 3->1 sorry, Basic COMPLETE | po-2025 |
