# Cooperative Games Lean - Formal Verification Status

## Build Info

| Item | Value |
|------|-------|
| Lean toolchain | `leanprover/lean4:v4.30.0-rc2` |
| Mathlib | pinned via lake-manifest.json |
| Total sorry | **1** (1 Basic + 0 Shapley) |
| Honest unprovable (in Mathlib) | **1** (`hb_witness`, Farkas/LP-dual kernel) |
| Total lines | ~1430 (Basic 388 + Shapley 1042) |
| Total theorems | 19 |
| Total definitions | 35 |

**Note**: Toolchain bumped to v4.30-0-rc2 (PR #1015). PR #1020's "prove bondareva_shapley_backward" was a **`apply?` placeholder** (non-proof); PR #2959 refactored honestly to isolate the irreducible LP-dual kernel `hb_witness` (`Basic.lean:312`) as a named sorry. That kernel requires `ProperCone.hyperplane_separation` (Farkas) — WIP, not yet proved.

## Per-File Status

### CooperativeGames/Basic.lean — FOUNDATIONAL

| Metric | Value |
|--------|-------|
| Definitions | 12 |
| Theorems | 7 |
| sorry | **1** (`hb_witness` @ L312, LP-dual kernel of `bondareva_shapley_backward`) |
| Status | WIP_HARD (Farkas required) |

Key definitions: `Coalition`, `TUGame`, `Superadditive`, `Convex`, `marginalContribution`,
`unanimityGame`, `majorityGame`, `Allocation`, `Core`, `CoreEmpty`, `Balanced`.

Previously-proved theorems (sorry resolved):
- `bondareva_shapley_forward` (PR #802)
- `convex_core_nonempty` (PR #981, Route A marginal vectors)
- `bondareva_shapley_backward` — **decomposition skeleton** (PR #2959): `hP_conv`/`hP_closed`/`hP_nonempty`/`hK_empty`/`hP_lb` all proved; only `hb_witness` (Farkas) remains open.

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

| Theorem | File | Open kernel | Strategy |
|---------|------|-------------|----------|
| `bondareva_shapley_backward` | Basic.lean | `hb_witness` @ L312 (∃ x ∈ P, ∑ xᵢ ≤ v(N)) | Farkas / `ProperCone.hyperplane_separation` (WIP_HARD, ~150-200 lines, cf `BONDAREVA_SHAPLEY_HARDNESS.md`) |

## Certification Level

| File | Level |
|------|-------|
| Basic.lean | WIP_HARD (1 sorry: `hb_witness` LP-dual kernel) |
| Shapley.lean | COMPLETE (0 sorry) |

**Project certification: WIP** — 1 sorry remaining (`hb_witness`, Farkas kernel). Shapley module complete.

## Remaining Work

Prove `hb_witness` (Bondareva-Shapley backward, LP-dual kernel) via `ProperCone.hyperplane_separation` (Farkas). Possible extensions:
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
| 2026-06-20 | **Correction (G.1 verify-before-claiming):** PR #1020's `bondareva_shapley_backward` "proof" was `apply?` (non-proof); PR #2959 refactored to isolate `hb_witness` LP-dual kernel as named sorry @ L312. FORMAL_STATUS corrected: 0→1 sorry, COMPLETE→WIP_HARD | po-2026 #2959 |
