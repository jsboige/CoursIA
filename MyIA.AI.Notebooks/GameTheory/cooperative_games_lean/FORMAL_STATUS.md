# Cooperative Games Lean - Formal Verification Status

## Build Info

| Item | Value |
|------|-------|
| Lean toolchain | `leanprover/lean4:v4.30.0-rc2` |
| Mathlib | pinned via lake-manifest.json |
| Total sorry | **0** (0 Basic + 0 Shapley + 0 ConeKernel) |
| Honest unprovable | **0** |
| Total lines | ~2369 (Basic 594 + Shapley 1042 + ConeKernel 733) |
| Certification | **COMPLETE** — all theorems proved, no added axiom |

**Note**: Toolchain v4.30.0-rc2 (PR #1015). PR #1020's earlier "prove bondareva_shapley_backward" was an `apply?` placeholder (non-proof); PR #2959 refactored honestly to isolate the irreducible kernel `hb_witness` (`Basic.lean:348`) as a named sorry. That kernel was **closed** by PR #3954 (2026-06-22) via a compact-slice Weierstrass argument — no `ProperCone.hyperplane_separation` (Farkas) was ultimately required. The project is now 0-sorry.

## Per-File Status

### CooperativeGames/Basic.lean — FOUNDATIONAL

| Metric | Value |
|--------|-------|
| Definitions | 9 |
| Theorems | 8 |
| sorry | **0** |
| Status | COMPLETE |

Key definitions: `TUGame`, `Superadditive`, `Convex`, `Core`, `CoreEmpty`, `Balanced`, `marginalVector`, plus the Bondareva-Shapley scaffolding.

Proved theorems:
- `bondareva_shapley_forward` (PR #802) — Core nonempty implies balanced
- `bondareva_shapley_backward` (PR #2959 skeleton → #3954 attainment) — balanced implies Core nonempty
- `bondareva_shapley : G.Core.Nonempty ↔ G.Balanced` (L434) — bi-implication, fully certified
- `convex_core_nonempty` (PR #981, Route A marginal vectors, L588) — convex games have nonempty Core
- `marginalVector_mem_core` (L581)

### CooperativeGames/ConeKernel.lean — CONE SEPARATION

| Metric | Value |
|--------|-------|
| Definitions | 4 |
| Theorems / lemmas | 12 |
| sorry | **0** |
| Status | COMPLETE |

The finite-dimensional cone machinery powering the backward direction. Key items: `augCone` (augmented incidence cone over `(Option N) → ℝ`), `balancedUnit`, `conicHull_linearIndependent_isClosed`, `mem_cone_iff_exists_li_subset`, `finGenCone_isClosed`, `augCone_mem_iff`, `augCone_dual_iff` (dual characterization), `separatingFunctional_none_neg`. Imported by `Basic.lean` (L22).

Lineage: cone kernel extraction (#3933) → bridge `balancedUnit ∉ augCone` (#3941) → decoding `exists_preimputation_strict_core` (#3945) → `hb_strict` (#3951) → attainment `hb_witness` (#3954).

### CooperativeGames/Shapley.lean — SHAPLEY VALUE

| Metric | Value |
|--------|-------|
| Definitions | 23 |
| Theorems | 12 |
| sorry | **0** |
| Status | FORMAL-COMPLETE |

Key definitions: `Solution`, `Efficiency`, `Symmetry`, `NullPlayerAxiom`, `Additivity`, `shapleyCoef`, `shapleyValue`, `shapleySolution`, `WeightedVotingGame`, `Critical`, `BanzhafRaw`, `VetoPlayer`, `Dictator`, `DummyPlayer`.

Proved theorems (sorry resolved): `shapley_null_player`, `shapley_unanimity` (PR #791), `shapley_symmetric`, `shapley_efficient`, `shapley_additive`, `shapleyCoef_top` (PR #757), `shapley_uniqueness` (PR #1024, Möbius decomposition), `mobius_decomposition`, `dummy_shapley_zero`.

## Theorem Inventory

### Fully Certified (0 sorry)

| Theorem | File | Statement |
|---------|------|-----------|
| `bondareva_shapley` | Basic.lean (L434) | `G.Core.Nonempty ↔ G.Balanced` — Bondareva-Shapley characterization |
| `bondareva_shapley_forward` | Basic.lean | Core nonempty implies balanced |
| `bondareva_shapley_backward` | Basic.lean | Balanced implies Core nonempty |
| `convex_core_nonempty` | Basic.lean (L588) | Convex games have nonempty Core (Shapley 1971) |
| `shapley_efficient` | Shapley.lean | Shapley value is efficient |
| `shapley_additive` | Shapley.lean | Shapley value is additive |
| `shapley_null_player` | Shapley.lean | Shapley value = 0 for null players |
| `shapley_unanimity` | Shapley.lean | Shapley value on unanimity games |
| `shapley_symmetric` | Shapley.lean | Symmetric players treated equally |
| `shapley_uniqueness` | Shapley.lean | Unique solution satisfying the four axioms (Möbius) |
| `mobius_decomposition` | Shapley.lean | Möbius decomposition of a TU game |

### Partially Proved

*None.* The project has no remaining `sorry`.

## Certification Level

| File | Level |
|------|-------|
| Basic.lean | COMPLETE (0 sorry) |
| Shapley.lean | COMPLETE (0 sorry) |
| ConeKernel.lean | COMPLETE (0 sorry) |

**Project certification: COMPLETE** — 0 sorry, no added axiom. `bondareva_shapley` (iff form) is fully proved.

## Remaining Work (extensions, not gaps)

- Banzhaf power index theorems (definitions `BanzhafRaw`/`Critical` exist, no theorems yet)
- Shapley value computational properties

## References

- Shapley, L.S. (1953). "A Value for N-Person Games"
- Bondareva, O.N. (1963). "Some Applications of Linear Programming Methods to the Theory of Cooperative Games"
- Shapley, L.S. (1967). "On Balanced Sets and Cores"
- Shapley, L.S. (1971). "Cores of Convex Games"

## History

| Date | Change | Commit / PR |
|------|--------|-------------|
| 2026-01-31 | Initial creation with TU games, Shapley value | initial |
| 2026-04-30 | FORMAL_STATUS.md created | PR-G |
| 2026-04-30 | `shapleyCoef_top` proved | PR #757 |
| 2026-04-30 | `shapley_unanimity` 2->1 sorry | PR #791 |
| 2026-05-01 | `bondareva_shapley_forward` proved | PR #802 |
| 2026-05-12 | BG iter 3: HONEST_UNPROVABLE annotation; FORMAL_STATUS realigned (7->3 sorry) | (this PR) |
| 2026-05-13 | Toolchain bump v4.30.0-rc2; `convex_core_nonempty` proved | PR #1015, #981 |
| 2026-05-13 | `shapley_uniqueness` proved (Möbius) — 0 sorry Shapley.lean | PR #1024 (`1eb5a4a0`) |
| 2026-06-20 | **G.1 correction:** PR #1020's `bondareva_shapley_backward` "proof" was `apply?` (non-proof); PR #2959 refactored to isolate `hb_witness` LP-dual kernel as named sorry @ L348. FORMAL_STATUS: 0→1 sorry | po-2026 #2959 |
| 2026-06-20 | Cone-separation strategy: Farkas plan via `(Option N) → ℝ` documented (`docs/BONDAREVA_FARKAS_PLAN.md`) | po-2026 #2959 |
| 2026-06-22 | **`hb_witness` attainment crux PROVEN** via compact-slice Weierstrass (Basic.lean +61/-7). `bondareva_shapley` iff now 0 sorry. Lineage: #3933 (cone kernel) → #3941 (bridge) → #3945 (decoding) → #3951 (`hb_strict`) → #3954 (attainment). Project COMPLETE. | PR #3954 (`a5288f0a7`) |
