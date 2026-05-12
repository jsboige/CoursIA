# Cooperative Games Lean - Formal Verification Status

## Build Info

| Item | Value |
|------|-------|
| Lean toolchain | `leanprover/lean4:v4.28.0-rc1` |
| Mathlib | pinned via lake-manifest.json |
| Total sorry | **3** (2 Basic + 1 Shapley) |
| Honest unprovable (in Mathlib) | **1** (Basic.lean:234) |
| Total lines | ~440 |
| Total theorems | 11 |
| Total definitions | 29 |

**Note**: Toolchain still on v4.28.0-rc1. Upgrade to v4.29.1 recommended (see social_choice_lean for precedent).

## Per-File Status

### CooperativeGames/Basic.lean — FOUNDATIONAL

| Metric | Value |
|--------|-------|
| Definitions | 12 |
| Theorems | 4 |
| sorry | **2** |
| Status | FORMAL-PARTIAL |

Key definitions: `Coalition`, `TUGame`, `Superadditive`, `Convex`, `marginalContribution`,
`unanimityGame`, `majorityGame`, `Allocation`, `Core`, `CoreEmpty`, `Balanced`.

sorry locations (post-2026-05-12 BG iter 3 annotations):
- Line 234: `bondareva_shapley_backward` — HONEST_UNPROVABLE in current Mathlib
  (LP duality / Farkas' lemma missing). Registered in `prover/config.py` HONEST_SORRIES.
- Line 262: `convex_core_nonempty` — WIP_HARD (~1-2 weeks Mathlib infrastructure).

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
- Line 566: `shapley_uniqueness` — WIP_HARD (Mobius decomposition into unanimity games;
  DEMO 6/8 in `prover/config.py` target this).

## Theorem Inventory

### Fully Certified (0 sorry)

| Theorem | File | Statement |
|---------|------|-----------|
| `superadditive_empty_nonneg` | Basic.lean | v(empty) >= 0 (trivial) |
| `superadditive_grand_coalition_nonneg_of_nonneg_singletons` | Basic.lean | Grand coalition value nonneg |
| `bondareva_shapley_forward` | Basic.lean | Core nonempty implies balanced |
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
| `bondareva_shapley_backward` | Basic.lean | 234 | HONEST_UNPROVABLE | 1 | Balanced implies Core nonempty (needs LP duality) |
| `convex_core_nonempty` | Basic.lean | 262 | WIP_HARD | 1 | Convex games have nonempty Core |
| `shapley_uniqueness` | Shapley.lean | 566 | WIP_HARD | 1 | Shapley value is unique solution satisfying axioms |

## Certification Level

| File | Level |
|------|-------|
| Basic.lean | PARTIAL (2 sorry — 1 HONEST + 1 WIP) |
| Shapley.lean | PARTIAL (1 sorry — WIP, Shapley uniqueness via Mobius) |

**Project certification: PARTIAL** — 3 sorry remaining, of which 1 is documented HONEST_UNPROVABLE.

## Remaining Work

| Priority | Task | sorry | Category |
|----------|------|-------|----------|
| HIGH | Complete `shapley_uniqueness` proof | 1 | WIP_HARD (DEMO 6/8) |
| MEDIUM | Complete `convex_core_nonempty` proof | 1 | WIP_HARD (Route A: marginal vectors) |
| BLOCKED | `bondareva_shapley_backward` | 1 | Awaits Mathlib LP duality / Farkas |
| LOW | Upgrade toolchain to v4.29.1 | 0 | (follow social_choice_lean) |

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
| 2026-05-12 | BG iter 3: HONEST_UNPROVABLE annotation Basic.lean L234 (LP duality missing); FORMAL_STATUS realigned (7->3 sorry: stale doc) | (this PR) |
