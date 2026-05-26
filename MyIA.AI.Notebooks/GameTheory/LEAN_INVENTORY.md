# Lean 4 Projects Inventory — GameTheory

Cross-directory inventory of all Lean 4 formalization projects under `GameTheory/`.

## Summary

| Directory | Toolchain | Production sorry | Modules | Status |
|-----------|-----------|-----------------|---------|--------|
| `stable_marriage_lean` | v4.30.0-rc2 | 3 | 6 files | Active proving |
| `conway_lean` | v4.30.0-rc2 | 0 | 7 files | COMPLETE |
| `calibration_lean` | v4.30.0-rc2 | 0 | 1 file | COMPLETE |
| `cooperative_games_lean` | v4.30.0-rc2 | 1 | 2 files | Stable |
| `social_choice_lean` | v4.30.0-rc2 | 0 | 7 files | COMPLETE |
| `social_choice_lean_peters` | v4.27.0-rc1 | 0 | 1 file | Reference only |
| **Total** | — | **4** | **24 files** | — |

Note: `_GoalExtract.lean` (2 sorry) is a prover test file, not production code. `SymbolicAI/Lean/examples/llm_assisted_proof.lean` (2 sorry) is a pedagogical example, not production.

---

## Directories

### 1. stable_marriage_lean

**Objective**: Formalize the Gale-Shapley stable marriage algorithm and its lattice-theoretic properties.

**Toolchain**: v4.30.0-rc2 | **Dependencies**: Mathlib4

| File | sorry | Description |
|------|-------|-------------|
| `StableMarriage/GaleShapley.lean` | 0 | GS algorithm, termination, stability, man_optimal, woman_pessimal |
| `StableMarriage/GSState.lean` | 0 | GS state machine, gsChooseMax |
| `StableMarriage/Lemmas.lean` | 0 | Helper lemmas (gsFinalMatching, gsAllWomenMatched, gsNoBlockingPairs) |
| `StableMarriage/Defs.lean` | 0 | Core type definitions |
| `StableMarriage/Lattice.lean` | 3 | Knuth rotation lattice (Case A2 L145, Case B L147, doctor_optimal L795) |
| `StableMarriage/_GoalExtract.lean` | 2 | Prover test harness (non-production) |

**Build**: `lake build StableMarriage` — SUCCESS (688 jobs)

**Prover targets**: Lattice.lean 3 sorry — all INTRACTABLE by current LLM (Knuth rotation sub-cases). doctor_optimal_eq_top proved conditionally (PR #1524). meetSpouse_injective proved (PR #1522). man_optimal proved (PR #1521).

**Key proofs**:
- `gale_shapley_stable` — PR #1194
- `gale_shapley_man_optimal` — PR #1521 (GPT-5.5 prover)
- `woman_pessimal` — PR #1521
- `meetSpouse_injective` — PR #1522 (GPT-5.5 prover)
- `no_cross_match` Case A1 — PR #1406 (manual)

---

### 2. conway_lean

**Objective**: Formalize Conway's mathematical games and algorithms.

**Toolchain**: v4.30.0-rc2 | **Dependencies**: Mathlib4

| File | sorry | Description |
|------|-------|-------------|
| `Conway/Doomsday.lean` | 0 | Doomsday algorithm |
| `Conway/DoomsdayLemmas.lean` | 0 | Supporting lemmas |
| `Conway/Fractran.lean` | 0 | FRACTRAN programming language |
| `Conway/LookAndSay.lean` | 0 | Look-and-say sequence |
| `Conway/LookAndSayLemmas.lean` | 0 | Supporting lemmas |
| `Conway/Nim.lean` | 0 | Nim game theory |
| `Conway/Angel.lean` | 0 | Angel problem |

**Build**: `lake build Conway` — SUCCESS (verified 24/05/2026)

**COMPLETE: 0 sorry**. Previous scan matched "sorry" in comments only, not code.

---

### 3. calibration_lean

**Objective**: Prover calibration targets for benchmarking the multi-agent prover.

**Toolchain**: v4.30.0-rc2 | **Dependencies**: Mathlib4

| File | sorry | Description |
|------|-------|-------------|
| `Calibration/Nash.lean` | 0 | Nash equilibrium calibration (all targets proved) |

**Build**: `lake build Calibration` — SUCCESS

**COMPLETE: 0 sorry**. All 4 calibration targets (C, D, E, F) proved. Previous scan matched "sorry" in doc comments only.

---

### 4. cooperative_games_lean

**Objective**: Formalize cooperative game theory (Shapley value, core).

**Toolchain**: v4.30.0-rc2 | **Dependencies**: Mathlib4

| File | sorry | Description |
|------|-------|-------------|
| `CooperativeGames/Shapley.lean` | 0 | Shapley value (uniqueness proved) |
| `CooperativeGames/Basic.lean` | 1 | Bondareva-Shapley theorem (hCore) |

**Build**: `lake build CooperativeGames` — SUCCESS

**Prover target**: 1 sorry in Basic.lean — INTRACTABLE (Bondareva-Shapley core nonemptiness requires hyperplane separation in locally convex spaces).

---

### 5. social_choice_lean

**Objective**: Port asouther4/lean-social-choice (Lean 3) to Lean 4. Arrow, Sen, Voting.

**Toolchain**: v4.30.0-rc2 | **Dependencies**: Mathlib4

| File | sorry | Description |
|------|-------|-------------|
| `SocialChoice/Arrow.lean` | 0 | Arrow's Impossibility Theorem (Geanakoplos 2005) |
| `SocialChoice/Sen.lean` | 0 | Sen's Liberal Paradox |
| `SocialChoice/Voting.lean` | 0 | Median Voter Theorem, Split Cycle, clones |
| `SocialChoice/Basic.lean` | 0 | Core definitions (PrefOrder, Profile, SWF) |
| `SocialChoice/Framework.lean` | 0 | Framework utilities |
| `SocialChoice/SortedListCounting.lean` | 0 | Sorted list counting helper |
| `SocialChoice/_SmokeTest.lean` | 0 | Build verification |

**Build**: `lake build SocialChoice` — SUCCESS | **COMPLETE: 0 sorry**

---

### 6. social_choice_lean_peters

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

| Priority | Target                 | Dir                    | sorry | Feasibility                        |
|----------|------------------------|------------------------|-------|------------------------------------|
| P1       | Basic.lean hCore       | cooperative_games_lean | 1     | Low (hyperplane separation)        |
| P2       | Lattice.lean A2 + B    | stable_marriage_lean   | 2     | Very Low (Knuth rotations)         |

---

## Related documentation

- [docs/lean/sota-2026-analysis.md](../../../docs/lean/sota-2026-analysis.md) — SOTA in automated Lean 4 proving
- [docs/lean/prover_iteration_history.md](../../../docs/lean/prover_iteration_history.md) — Prover iterations F6-F11, B3
- [docs/lean/llm-endpoints.md](../../../docs/lean/llm-endpoints.md) — LLM providers for the prover
- [docs/lean/coordinator-workflow.md](../../../docs/lean/coordinator-workflow.md) — Coordinator build + BG iter workflow
