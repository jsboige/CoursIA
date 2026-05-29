# Lean 4 Projects Inventory — GameTheory

Cross-directory inventory of all Lean 4 formalization projects under `GameTheory/`.

## Summary

| Directory | Toolchain | Production sorry | Modules | Status |
|-----------|-----------|-----------------|---------|--------|
| `stable_marriage_lean` | v4.30.0-rc2 | 3 | 5 files | Active proving |
| `cooperative_games_lean` | v4.30.0-rc2 | 1 | 2 files | Active proving |
| `social_choice_lean` | v4.30.0-rc2 | 0 | 7 files | COMPLETE |
| `social_choice_lean_peters` | v4.27.0-rc1 | 0 | 1 file | Reference only |
| **Total** | — | **4** | **15 files** | — |

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
| `StableMarriage/GaleShapley.lean` | 0 (body) | GS algorithm, termination, stability, man_optimal, woman_pessimal — `gale_shapley_man_optimal` transitively depends on `doctor_optimal_eq_top` (Lattice L836 sorry) |
| `StableMarriage/GSState.lean` | 0 | GS state machine, gsChooseMax |
| `StableMarriage/Lemmas.lean` | 0 | Helper lemmas (gsFinalMatching, gsAllWomenMatched, gsNoBlockingPairs) |
| `StableMarriage/Definitions.lean` | 0 | Core type definitions |
| `StableMarriage/Lattice.lean` | 3 | Knuth rotation lattice (`no_cross_match` Case A2 L185, Case B L187, `doctor_optimal_eq_top` L836) |

**Build**: `lake build StableMarriage` — SUCCESS (688 jobs)

**Prover targets**: Lattice.lean 3 sorry — all INTRACTABLE by current LLM (Knuth rotation sub-cases). `doctor_optimal_eq_top` (Lattice L836) body remains `sorry`, with all upstream consumers (`gale_shapley_man_optimal`, `woman_pessimal` in GaleShapley.lean) transitively dependent. `meetSpouse_injective` body proved (PR #1522). `gale_shapley_man_optimal` body proved (PR #1521) but transitively depends on `doctor_optimal_eq_top`.

**Key proofs**:
- `gale_shapley_stable` — PR #1194
- `gale_shapley_man_optimal` — PR #1521 (GPT-5.5 prover)
- `woman_pessimal` — PR #1521
- `meetSpouse_injective` — PR #1522 (GPT-5.5 prover)
- `no_cross_match` Case A1 — PR #1406 (manual)

---

### 2. cooperative_games_lean

**Objective**: Formalize cooperative game theory (Shapley value, core).

**Toolchain**: v4.30.0-rc2 | **Dependencies**: Mathlib4

| File | sorry | Description |
|------|-------|-------------|
| `CooperativeGames/Shapley.lean` | 0 | Shapley value (uniqueness proved) |
| `CooperativeGames/Basic.lean` | 1 | `bondareva_shapley_forward.hCore` (L309) tagged `INTRACTABLE_UNTIL_BONDAREVA_HYPERPLANE_SEPARATION` |

**Build**: `lake build CooperativeGames` — SUCCESS (with `sorry` warning on Basic.lean:309)

**Status: Active proving (1 sorry)**. `bondareva_shapley_forward` reduces to extracting a Core allocation from the polytope `P \ K`; the body is sketched (P nonempty + closed + no element has coalition deficit) but requires Hahn-Banach / hyperplane separation in locally convex spaces (not yet ported to Mathlib for finite-dim R^n in this shape). Consumer theorem `bondareva_shapley` (iff form) transitively depends on this `sorry`.

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
| P1       | Lattice.lean L185 Case A2    | stable_marriage_lean   | 1     | Very Low (Knuth rotations)         |
| P2       | Lattice.lean L187 Case B     | stable_marriage_lean   | 1     | Very Low (Knuth rotations)         |
| P3       | Lattice.lean L836 doc_opt    | stable_marriage_lean   | 1     | Low (depends on no_cross_match)    |
| P4       | Basic.lean L309 hCore        | cooperative_games_lean | 1     | Very Low (Hahn-Banach separation)  |

Note: After PRs #1521-#1525 merge, Lattice.lean will have **0 sorry, 1 axiom** (`no_cross_match`). The 3 sorry listed above are on current main.

## GO/NO-GO per Project (for BG iter cycles)

| Project                | Decision | Reasoning                                                      |
|------------------------|----------|----------------------------------------------------------------|
| stable_marriage_lean   | NO-GO    | All 3 sorry INTRACTABLE (Knuth rotations). man_optimal body proved. |
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
