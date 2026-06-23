# Cooperative Games Lean - Formal Verification Status

## Build Info

| Item | Value |
|------|-------|
| Lean toolchain | `leanprover/lean4:v4.30.0-rc2` |
| Mathlib | pinned via lake-manifest.json |
| Total sorry | **0** |
| Honest unprovable (in Mathlib) | **0** |
| Total lines | ~2628 (Basic 594 + ConeKernel 733 + Shapley 1301) |
| Total theorems | 27 (Basic 8 + ConeKernel 4 + Shapley 15) |
| Total lemmas | 10 (Basic 2 + ConeKernel 8) |
| Total definitions | 41 (Basic 13 + ConeKernel 4 + Shapley 24) |

**Note**: Toolchain bumped to v4.30-0-rc2 (PR #1015). PR #1020's "prove bondareva_shapley_backward" was a **`apply?` placeholder** (non-proof); PR #2959 refactored honestly to isolate the irreducible LP-dual kernel `hb_witness` as a named sorry. That kernel — long tagged **INTRACTABLE_UNTIL_BONDAREVA_HYPERPLANE_SEPARATION** — was then **closed across PRs #3933 → #3954** by building the cone-separation machinery in `CooperativeGames/ConeKernel.lean` (Farkas via `ProperCone.hyperplane_separation_point` from Mathlib `Analysis.Convex.Cone.Dual`). `hb_witness` is now a fully-proved `have` at `Basic.lean:348`. The project is **COMPLETE (0 sorry, 0 axiom beyond Lean's core)**.

## Per-File Status

### CooperativeGames/Basic.lean — FOUNDATIONAL

| Metric | Value |
|--------|-------|
| Definitions | 13 |
| Theorems | 8 |
| Lemmas | 2 |
| Lines | 594 |
| sorry | **0** |
| Status | FORMAL-COMPLETE |

Key definitions: `Coalition`, `TUGame`, `Superadditive`, `Convex`, `marginalContribution`,
`unanimityGame`, `majorityGame`, `Allocation`, `Core`, `CoreEmpty`, `Balanced`.

Proved theorems (sorry resolved):
- `bondareva_shapley_forward` (PR #802)
- `convex_core_nonempty` (PR #981, Route A marginal vectors)
- `bondareva_shapley_backward` — **fully proved** (PR #3954, sorry 1→0): the decomposition
  `hP_conv`/`hP_closed`/`hP_nonempty`/`hK_empty`/`hP_lb` plus the former `hb_witness` kernel,
  now a certified `have` (`Basic.lean:348`) that invokes
  `ProperCone.hyperplane_separation_point` over the augmented cone `augCone G.v`.

### CooperativeGames/ConeKernel.lean — BONDAREVA-FArkAS KERNEL (NEW)

| Metric | Value |
|--------|-------|
| Definitions | 4 |
| Theorems | 4 |
| Lemmas | 8 |
| Lines | 733 |
| sorry | **0** |
| Status | FORMAL-COMPLETE |

The cone-separation infrastructure that closes the former `hb_witness` sorry. Key results:

- `augCone` (`:69`) — the `ProperCone ℝ ((Option N) → ℝ)` encoding balanced-weight violations.
- `conicHull_linearIndependent_isClosed` (`:88`), `finGenCone_isClosed` (`:294`) — closedness
  of the relevant cones (finite generation ⇒ closed).
- `augCone_mem_iff` (`:363`), `augCone_dual_iff` (`:443`) — dual-characterisation bridge.
- `separatingFunctional_none_neg` (`:601`) — the separating functional `f` from
  `ProperCone.hyperplane_separation_point` is non-negative on the cone.
- `balancedUnit_decomp` (`:667`), `exists_preimputation_strict_core` (`:688`) — witness
  decoding: the separator yields an imputation in the Core, completing the backward direction.

Largely **TUGame-free** (cone lemmas stated over `(Option N) → ℝ` so the kernel is reusable
and decoupled from the cooperative-game structure), wired into `Basic.lean` by PR #3951.

### CooperativeGames/Shapley.lean — SHAPLEY VALUE

| Metric | Value |
|--------|-------|
| Definitions | 24 |
| Theorems | 15 |
| Lines | 1301 |
| sorry | **0** |
| Status | FORMAL-COMPLETE |

Key definitions: `Solution`, `Efficiency`, `Symmetry`, `NullPlayerAxiom`, `Additivity`,
`shapleyCoef`, `shapleyValue`, `shapleySolution`, `WeightedVotingGame`, `Critical`,
`BanzhafRaw`, `BanzhafIndex`, `VetoPlayer`, `Dictator`, `DummyPlayer`.

Proved theorems (sorry resolved):
- `shapley_null_player` (PR earlier in 2026-04)
- `shapley_unanimity` (PR #791)
- `shapley_symmetric` (PR earlier in 2026-04)
- `shapleyCoef_top` (PR #757)
- `bondareva_shapley_forward` (PR #802)
- `shapley_uniqueness` (PR #1024, commit `1eb5a4a0`, 2026-05-13 — Mobius decomposition)
- `dummy_shapley_zero` (dummy players get zero Shapley value)
- `dummy_banzhaf_raw_zero` (PR #4011 — dummy players get zero raw Banzhaf index)
- `banzhaf_index_symmetric` (normalized Banzhaf index treats symmetric players equally)
- `banzhaf_index_dummy_zero` (dummy players get zero normalized Banzhaf index)

## Theorem Inventory

### Fully Certified (0 sorry)

| Theorem | File | Statement |
|---------|------|-----------|
| `superadditive_empty_nonneg` | Basic.lean | v(empty) >= 0 (trivial) |
| `superadditive_grand_coalition_nonneg_of_nonneg_singletons` | Basic.lean | Grand coalition value nonneg |
| `bondareva_shapley_forward` | Basic.lean | Core nonempty implies balanced |
| `convex_core_nonempty` | Basic.lean | Convex games have nonempty Core (PR #981) |
| `bondareva_shapley_backward` | Basic.lean | Balanced implies Core nonempty (PR #3954, Farkas via ConeKernel) |
| `conicHull_linearIndependent_isClosed` | ConeKernel.lean | Finite-generation ⇒ closed cone |
| `augCone_dual_iff` | ConeKernel.lean | Dual characterisation of the augmented cone |
| `separatingFunctional_none_neg` | ConeKernel.lean | Separator non-negative on the cone |
| `exists_preimputation_strict_core` | ConeKernel.lean | Separator ⇒ imputation in Core (witness decoding) |
| `shapley_efficient` | Shapley.lean | Shapley value is efficient |
| `shapley_additive` | Shapley.lean | Shapley value is additive |
| `shapley_null_player` | Shapley.lean | Shapley value = 0 for null players |
| `shapley_unanimity` | Shapley.lean | Shapley value on unanimity games |
| `shapley_symmetric` | Shapley.lean | Shapley value treats symmetric players equally |
| `shapleyCoef_top` | Shapley.lean | Shapley coefficient for full coalition |
| `shapley_uniqueness` | Shapley.lean | Shapley value is unique solution satisfying axioms (PR #1024) |
| `dummy_shapley_zero` | Shapley.lean | Dummy players get zero Shapley value |
| `dummy_banzhaf_raw_zero` | Shapley.lean | Dummy players get zero raw Banzhaf index (PR #4011) |
| `banzhaf_index_symmetric` | Shapley.lean | Normalized Banzhaf index treats symmetric players equally |
| `banzhaf_index_dummy_zero` | Shapley.lean | Dummy players get zero normalized Banzhaf index |

### Partially Proved (contains sorry)

None — all theorems are fully certified (0 sorry).

## Certification Level

| File | Level |
|------|-------|
| Basic.lean | COMPLETE (0 sorry) |
| ConeKernel.lean | COMPLETE (0 sorry) |
| Shapley.lean | COMPLETE (0 sorry) |

**Project certification: COMPLETE** — 0 sorry, 0 axiom beyond Lean's core. The Bondareva-Shapley
theorem is proved in both directions (`forward` + `backward`), the Shapley value is fully
characterised, and the Farkas/cone-separation kernel lives in `ConeKernel.lean`.

## Remaining Work

No open sorry. Possible extensions:
- Banzhaf power index: `dummy_banzhaf_raw_zero` proved (PR #4011); a symmetry theorem
  `banzhaf_raw_symmetric` (interchangeable players have equal raw Banzhaf indices, the
  Banzhaf analog of `shapley_symmetric`) is in progress in PR #4037
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
| 2026-05-13 | Toolchain bump to v4.30.0-rc2; `convex_core_nonempty` proved | PR #1015, #981 |
| 2026-05-13 | `shapley_uniqueness` proved (Mobius decomposition) — 0 sorry Shapley.lean | PR #1024, commit `1eb5a4a0` |
| 2026-05-14 | FORMAL_STATUS realigned: 3->0 sorry, module COMPLETE | po-2026 T-A |
| 2026-06-20 | **Correction (G.1 verify-before-claiming):** PR #1020's `bondareva_shapley_backward` "proof" was `apply?` (non-proof); PR #2959 refactored to isolate `hb_witness` LP-dual kernel as named sorry. FORMAL_STATUS corrected: 0→1 sorry, COMPLETE→WIP_HARD | po-2026 #2959 |
| 2026-06-23 | **ConeKernel construction closes `hb_witness` (sorry 1→0):** #3933 (ConeKernel TUGame-free kernel) → #3941 (balancedUnit bridge) → #3945 (witness-decoding core) → #3951 (wire cone-separation→decoding pipeline) → #3954 (sorry 1→0). `hb_witness` now a certified `have` @ `Basic.lean:348`. FORMAL_STATUS realigned: 1→0 sorry, WIP_HARD→COMPLETE. Lake build SUCCESS (8435 jobs). | po-2026 |
| 2026-06-23 | **Banzhaf docs anti-dérive:** FORMAL_STATUS corrected — `dummy_banzhaf_raw_zero` (PR #4011) added to proved list + inventory; stale "no theorems yet" line fixed; Shapley.lean counts 12→13 theorems / 1042→1081 lines. README.md (FR) + README.en.md document the Banzhaf framework (`Critical`/`BanzhafRaw`). See #4037 (symmetry theorem in progress). | po-2026 |
