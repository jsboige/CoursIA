# Lean 4 Projects Inventory — GameTheory

Cross-directory inventory of all Lean 4 formalization projects under `GameTheory/`.

## Summary

| Directory | Toolchain | Production sorry | Modules | Status |
|-----------|-----------|-----------------|---------|--------|
| `stable_marriage_lean` | v4.30.0-rc2 | 0 | 5 files | COMPLETE |
| `cooperative_games_lean` | v4.30.0-rc2 | 0 | 3 files | COMPLETE |
| `social_choice_lean` | v4.30.0-rc2 | 0 | 7 files | COMPLETE |
| `social_choice_lean_peters` | v4.27.0-rc1 | 0 | 1 file | Reference only |
| **Total** | — | **0** | **16 files** | — |

Note: `_GoalExtract.lean` (former prover test file) has been removed from the repo. `SymbolicAI/Lean/examples/llm_assisted_proof.lean` (2 sorry) is a pedagogical example, not production.

**Conway tribute series relocated**: `conway_lean/` (Conway hommage — Doomsday, FRACTRAN, Look-and-Say, Nim, Angel) was moved to [`SymbolicAI/Lean/conway_lean/`](../SymbolicAI/Lean/conway_lean/) since it formalizes lesser-known Conway results (not game-theoretic content per se). The prover calibration targets defined in `agent_tests/prover/config.py` follow the new path.

**Calibration relocated**: `calibration_lean/` was moved to [`SymbolicAI/Lean/calibration_lean/`](../SymbolicAI/Lean/calibration_lean/) (issue #1764) since it is a prover harness component, not game-theoretic content.

---

## Directories

### 1. stable_marriage_lean

**Objective**: Formalize the Gale-Shapley stable marriage algorithm and its lattice-theoretic properties.

**Toolchain**: v4.30.0-rc2 | **Dependencies**: Mathlib4

| File | sorry | Description |
|------|-------|-------------|
| `StableMarriage/GaleShapley.lean` | 0 | GS algorithm, termination, stability, man_optimal (via `exists_isManOptimal`), woman_pessimal |
| `StableMarriage/GSState.lean` | 0 | GS state machine, gsChooseMax |
| `StableMarriage/Lemmas.lean` | 0 | Helper lemmas (gsFinalMatching, gsAllWomenMatched, gsNoBlockingPairs) |
| `StableMarriage/Definitions.lean` | 0 | Core type definitions |
| `StableMarriage/Lattice.lean` | 0 | Knuth lattice, `exists_isManOptimal`, refutations of former false statements |

**Build**: `lake build StableMarriage` — SUCCESS (755 jobs)

**COMPLETE: 0 sorry.** The former `no_cross_match`, `man_optimality_key_step`, and `doctor_optimal_eq_top` statements were **false** (refuted by a 3x3 latin-square counterexample, kernel-checked). They have been replaced by: honest `exists_isManOptimal` (minimal-weight argument on join semilattice), `meetSpouse_injective` (counting/pigeonhole), and three refutation theorems.

**Key proofs**:
- `gale_shapley_stable` — PR #1194
- `gale_shapley_man_optimal` — `exists_isManOptimal` + `gale_shapley_stable` (no false-lemma dependency)
- `woman_pessimal` — PR #1521 (constructive, from man-optimality)
- `meetSpouse_injective` — counting/pigeonhole argument (no anti-crossing needed)
- `joinSpouse_injective` — PR #1522
- `no_cross_match_is_false` / `doctor_optimal_eq_top_is_false` — kernel-checked refutations

---

### 2. cooperative_games_lean

**Objective**: Formalize cooperative game theory (Shapley value, core).

**Toolchain**: v4.30.0-rc2 | **Dependencies**: Mathlib4

| File | sorry | Description |
|------|-------|-------------|
| `CooperativeGames/Shapley.lean` | 0 | Shapley value, characterization + uniqueness (Möbius decomposition) |
| `CooperativeGames/Basic.lean` | 0 | TU games, Core, balanced games, `bondareva_shapley : Core.Nonempty ↔ Balanced` (iff, L434), `convex_core_nonempty` (L588) |
| `CooperativeGames/ConeKernel.lean` | 0 | Cone-separation machinery (augmented incidence cone, closure, dual characterization) for the backward direction |

**Build**: `lake build CooperativeGames` — SUCCESS (0 sorry, no added axiom)

**Status: COMPLETE (0 sorry).** `bondareva_shapley` (`Core.Nonempty ↔ Balanced`) is fully proved. The backward direction's attainment crux `hb_witness` (formerly tagged `INTRACTABLE_UNTIL_BONDAREVA_HYPERPLANE_SEPARATION`) was closed by PR #3954 via a compact-slice Weierstrass argument — bypassing the missing Mathlib `ProperCone.hyperplane_separation` without any added axiom. Lineage: #3933 (cone kernel) → #3941 (bridge) → #3945 (decoding) → #3951 (`hb_strict`) → #3954 (attainment). See [`cooperative_games_lean/FORMAL_STATUS.md`](cooperative_games_lean/FORMAL_STATUS.md).

---

### 3. social_choice_lean

**Objective**: Port asouther4/lean-social-choice (Lean 3) to Lean 4. Arrow, Sen, Voting, Mechanism Design.

**Toolchain**: v4.30.0-rc2 | **Dependencies**: Mathlib4

| File | sorry | Description |
|------|-------|-------------|
| `SocialChoice/Arrow.lean` | 0 | Arrow's Impossibility Theorem (Geanakoplos 2005) |
| `SocialChoice/Sen.lean` | 0 | Sen's Liberal Paradox |
| `SocialChoice/Voting.lean` | 0 | Median Voter Theorem, Split Cycle, clones |
| `SocialChoice/MechanismDesign.lean` | 0 | Vickrey truthfulness, first-price counter-example (#1469) |
| `SocialChoice/Basic.lean` | 0 | Core definitions (PrefOrder, Profile, SWF) |
| `SocialChoice/Framework.lean` | 0 | Framework utilities |
| `SocialChoice/SortedListCounting.lean` | 0 | Sorted list counting helper |
| `SocialChoice/_SmokeTest.lean` | 0 | Build verification |

**Build**: `lake build SocialChoice` — SUCCESS | **COMPLETE: 0 sorry**

---

### 4. social_choice_lean_peters

**Objective**: Reference project importing DominikPeters/SocialChoiceLean as a Lake dependency.

**Toolchain**: v4.27.0-rc1 (pinned to Peters' version) | **Dependencies**: Mathlib4, SocialChoiceLean (external)

| File | sorry | Description |
|------|-------|-------------|
| `PetersTour.lean` | 0 | Curated tour of Peters' formalized results |

**Build**: `lake build` — SUCCESS | **Reference only, not for proving**

**Content**: Imports Peters' library (Gibbard-Satterthwaite, Duggan-Schwartz, 4 Condorcet impossibilities, 15+ voting rules with axiom verification). Serves as the backend for notebook `GameTheory-16e-SocialChoiceLean-Tour.ipynb`.

**Relationship to `social_choice_lean`**: Complementary, not duplicate. `social_choice_lean` uses custom `PrefOrder` framework (our proofs). `social_choice_lean_peters` uses Peters' `LinearOrder` framework (external reference). Both kept for pedagogical completeness.

---

## Remaining Proving Targets

| Priority | Target                       | Dir                    | sorry | Feasibility                        |
|----------|------------------------------|------------------------|-------|------------------------------------|
| P1       | Basic.lean L309 hCore        | cooperative_games_lean | 1     | Very Low (Hahn-Banach separation)  |

## GO/NO-GO per Project (for BG iter cycles)

| Project                | Decision | Reasoning                                                      |
|------------------------|----------|----------------------------------------------------------------|
| stable_marriage_lean   | COMPLETE | 0 sorry. Former false statements refuted, honest `exists_isManOptimal` proved. |
| cooperative_games_lean | NO-GO    | hCore requires Hahn-Banach / hyperplane separation.           |
| social_choice_lean     | N/A      | COMPLETE (0 sorry). MechanismDesign added (#1469).             |
| social_choice_lean_peters | N/A   | Reference only (pinned v4.27.0-rc1).                           |

Conway calibration targets (Doomsday / FRACTRAN / Look-and-Say / Nim / Angel) live in `SymbolicAI/Lean/conway_lean/` and are still consumed by `agent_tests/prover/config.py` (#1453 prover harness co-evolution).

---

## Related documentation

- [docs/lean/sota-2026-analysis.md](../../../docs/lean/sota-2026-analysis.md) — SOTA in automated Lean 4 proving
- [docs/lean/prover_iteration_history.md](../../../docs/lean/prover_iteration_history.md) — Prover iterations F6-F11, B3
- [docs/lean/llm-endpoints.md](../../../docs/lean/llm-endpoints.md) — LLM providers for the prover
- [docs/lean/coordinator-workflow.md](../../../docs/lean/coordinator-workflow.md) — Coordinator build + BG iter workflow
