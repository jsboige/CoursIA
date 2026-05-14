# Cooperative Games Lean - Formal Verification Status

## Build Info

| Item | Value |
|------|-------|
| Lean toolchain | `leanprover/lean4:v4.30.0-rc2` |
| Mathlib | pinned via lake-manifest.json |
| Total sorry | **0** (0 Basic + 0 Shapley) |
| Honest unprovable (in Mathlib) | **0** |
| Total lines | ~1430 (Basic 388 + Shapley 1042) |
| Total theorems | 19 |
| Total definitions | 35 |

**Note**: Toolchain bumped to v4.30.0-rc2 (PR #1015). Bondareva backward + convex_core + shapley_uniqueness all proved.

## Per-File Status

### CooperativeGames/Basic.lean — FOUNDATIONAL

| Metric | Value |
|--------|-------|
| Definitions | 12 |
| Theorems | 7 |
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
| Definitions | 23 |
| Theorems | 12 |
| sorry | **0** |
| Status | FORMAL-COMPLETE |

Key definitions: `Solution`, `Efficiency`, `Symmetry`, `NullPlayerAxiom`, `Additivity`,
`shapleyCoef`, `shapleyValue`, `shapleySolution`, `WeightedVotingGame`, `Critical`,
`BanzhafRaw`, `VetoPlayer`, `Dictator`, `DummyPlayer`.

Previously-proved theorems (sorry resolved):
- `shapley_null_player` (PR earlier in 2026-04)
- `shapley_unanimity` (PR #791)
- `shapley_symmetric` (PR earlier in 2026-04)
- `shapleyCoef_top` (PR #757)
- `bondareva_shapley_forward` (PR #802)
- `shapley_uniqueness` (PR #1024, commit `1eb5a4a0`, 2026-05-13 — Mobius decomposition)

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
| `shapley_uniqueness` | Shapley.lean | Shapley value is unique solution satisfying axioms (PR #1024) |
| `dummy_shapley_zero` | Shapley.lean | Dummy players get zero Shapley value |

### Partially Proved (contains sorry)

None — all theorems fully certified.

## Certification Level

| File | Level |
|------|-------|
| Basic.lean | COMPLETE (0 sorry) |
| Shapley.lean | COMPLETE (0 sorry) |

**Project certification: COMPLETE** — 0 sorry remaining in cooperative_games_lean module.

## Remaining Work

No sorry work remaining in this module. Possible extensions:
- Banzhaf power index theorems (definitions `BanzhafRaw`/`Critical` exist, no theorems yet)
- Shapley value computational properties

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
| 2026-05-12 | BG iter 3: HONEST_UNPROVABLE annotation Basic.lean L234; FORMAL_STATUS realigned (7->3 sorry) | (this PR) |
| 2026-05-12 | Reclassified bondareva_shapley_backward: HONEST_UNPROVABLE -> WIP_HARD | Cycle 28 Track A |
| 2026-05-13 | Toolchain bump to v4.30.0-rc2; `bondareva_shapley_backward` proved; `convex_core_nonempty` proved | PR #1015, #1020, #981 |
| 2026-05-13 | `shapley_uniqueness` proved (Mobius decomposition) — 0 sorry Shapley.lean | PR #1024, commit `1eb5a4a0` |
| 2026-05-14 | FORMAL_STATUS realigned: 3->0 sorry, module COMPLETE | po-2026 T-A |
