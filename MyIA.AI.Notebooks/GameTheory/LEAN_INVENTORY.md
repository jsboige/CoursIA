# Lean 4 Projects Inventory — GameTheory

Cross-directory inventory of all Lean 4 formalization projects under `GameTheory/`.

## Summary

| Directory | Toolchain | Production sorry | Modules | Status |
|-----------|-----------|-----------------|---------|--------|
| `game_theory_lean` | v4.31.0-rc1 | 3 (Lattice) | CooperativeGames + StableMarriage | COMPLETE (EPIC #4365) |
| `cooperative_games_lean` | v4.31.0-rc1 | 0 | 3 files | COMPLETE |
| `social_choice_lean` | v4.31.0-rc1 | 0 | 7 files | COMPLETE |
| `social_choice_lean_peters` | v4.27.0-rc1 | 0 | 1 file | Reference only |
| `repeated_games_lean` | v4.31.0-rc1 | 0 (1 stretch) | 4 files | COMPLETE (Folk stretch) |
| `minimax_lean` | v4.31.0-rc1 | 0 | 2 files | COMPLETE |
| `lean_game_defs` | v4.31.0-rc1 | 0 | 6 files | COMPLETE (shared defs) |
| `lean_game_defs_ext` | v4.31.0-rc1 | 0 | 11 files | COMPLETE |
| `conway_cgt_lean` | v4.31.0-rc1 | 0 | 1 file | Reference tour |
| **Total** | — | **0** (+1 stretch) | **39 files** | — |

Note: `_GoalExtract.lean` (former prover test file) has been removed from the repo. `SymbolicAI/Lean/examples/llm_assisted_proof.lean` (2 sorry) is a pedagogical example, not production.

**Conway tribute series relocated**: `conway_lean/` (Conway hommage — Doomsday, FRACTRAN, Look-and-Say, Nim, Angel) was moved to [`SymbolicAI/Lean/conway_lean/`](../SymbolicAI/Lean/conway_lean/) since it formalizes lesser-known Conway results (not game-theoretic content per se). The prover calibration targets defined in `agent_tests/prover/config.py` follow the new path.

**Calibration relocated**: `calibration_lean/` was moved to [`SymbolicAI/Lean/calibration_lean/`](../SymbolicAI/Lean/calibration_lean/) (issue #1764) since it is a prover harness component, not game-theoretic content.

---

## Directories

### 1. game_theory_lean

**EPIC #4365 (phase 4)**: multi-module target lake. `StableMarriage` was absorbed from the now-removed `stable_marriage_lean/` (PRs #5904/#5905/#5910/#5911/#5913) and `CooperativeGames` from `cooperative_games_lean/`. The standalone `stable_marriage_lean/` checkout has been removed (content fully preserved here — byte-identical or FR-harmonized ahead copies).

**Objective**: Formalize cooperative game theory (Shapley, core) and the Gale-Shapley stable marriage algorithm with its lattice-theoretic properties.

**Toolchain**: v4.31.0-rc1 | **Dependencies**: Mathlib4

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

**Toolchain**: v4.31.0-rc1 | **Dependencies**: Mathlib4

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

**Toolchain**: v4.31.0-rc1 | **Dependencies**: Mathlib4

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

**Content**: Imports Peters' library (Gibbard-Satterthwaite, Duggan-Schwartz, 4 Condorcet impossibilities, 15+ voting rules with axiom verification). Backend Lake for the (planned, not yet created) SocialChoiceLean tour companion notebook.

**Relationship to `social_choice_lean`**: Complementary, not duplicate. `social_choice_lean` uses custom `PrefOrder` framework (our proofs). `social_choice_lean_peters` uses Peters' `LinearOrder` framework (external reference). Both kept for pedagogical completeness.

---

### 5. repeated_games_lean

**Objective**: Formalize repeated games — the iterated Prisoner's Dilemma with discounting, grim-trigger strategy, and the Folk theorem (sustainable payoffs).

**Toolchain**: v4.31.0-rc1 | **Dependencies**: Mathlib4

| File | sorry | Description |
|------|-------|-------------|
| `RepeatedGames/Stage.lean` | 0 | Stage game, Prisoner's Dilemma (PDAction), `defection_strictly_dominates`, `temptation_gt_reward` |
| `RepeatedGames/Discounting.lean` | 0 | Discount factor δ, geometric sums, `discount_threshold_rewrite` |
| `RepeatedGames/GrimTrigger.lean` | 0 | Grim strategy, **`grim_trigger_sustains_iff`** (theorem-phare, FORMAL-CERTIFIED), NE corollary |
| `RepeatedGames/Folk.lean` | 1 (stretch) | `folk_theorem_discounted` / `folk_theorem_boundary` — 1 sorry stretch (toléré, #4880) |

**Build**: `lake build RepeatedGames` — SUCCESS (2953 jobs, post-#5362) | **COMPLETE: 0 sorry on the theorem-phare; Folk stretch OPEN**

**Status**: `grim_trigger_sustains_iff` (sustains a subgame-perfect Nash iff δ ≥ threshold) is fully proved 0 sorry. The Folk theorem (`folk_theorem_discounted`) carries 1 stretch sorry, tolerated per #4880 (grim already covers the closure criterion). See [`repeated_games_lean/FORMAL_STATUS.md`](repeated_games_lean/FORMAL_STATUS.md).

---

### 6. minimax_lean

**Objective**: Formalize the two-player zero-sum game minimax setting — payoff bilinearity and continuity as the foundation for von Neumann's minimax theorem.

**Toolchain**: v4.31.0-rc1 | **Dependencies**: Mathlib4

| File | sorry | Description |
|------|-------|-------------|
| `Minimax/ZeroSum.lean` | 0 | Zero-sum payoff structure, bilinearity (`payoff_add_in_x`, `smul`), `continuous_payoff`; saddle-point existence derived from Mathlib's Sion minimax |
| `Minimax.lean` (umbrella) | 0 | Re-export |

**Build**: `lake build Minimax` — SUCCESS | **COMPLETE: 0 sorry**

**Key facts**:
- Payoff bilinearity and continuity proven 0 sorry (`payoff_add_in_x`, payoff scalar-multiplication, `continuous_payoff`).
- **Saddle-point existence** (`∃ mixed strategies, max_x min_y = min_y max_x`) is *derivable* from Mathlib's Sion minimax theorem and is documented as such — **not** left as a `sorry`. No sorry-backed milestone.

---

### 7. lean_game_defs

**Objective**: Shared game-theoretic type definitions (normal-form games, Bayesian games, combinatorial games, social choice, regret) — the foundational layer reused by the GT Lean notebooks. Self-contained (core Lean only, zero Mathlib dependency).

**Toolchain**: v4.31.0-rc1 | **Dependencies**: Lean core (Mathlib-free)

| File | sorry | Description |
|------|-------|-------------|
| `LeanGameDefs/Basic.lean` | 0 | NormalFormGame / FiniteGame core types |
| `LeanGameDefs/Nash.lean` | 0 | Nash equilibrium definitions |
| `LeanGameDefs/Bayesian.lean` | 0 | Bayesian game types |
| `LeanGameDefs/Combinatorial.lean` | 0 | Combinatorial game types |
| `LeanGameDefs/SocialChoice.lean` | 0 | Social choice primitives (`dictatorship_satisfies_pareto`, `dictatorship_satisfies_iia`) |
| `LeanGameDefs/Regret.lean` | 0 | Regret / minimax-regret definitions |

**Build**: `lake build LeanGameDefs` — SUCCESS (CI `lean-game-defs.yml`) | **COMPLETE: 0 sorry, Mathlib-free**

**Status**: Infrastructural definitions layer (2 theorems verifying dictatorship axioms). Added `lakefile.toml` + CI per ai-01 review on PR #2752 (these shared defs were previously shipped without a build harness, #2673). Backend for the GT Lean notebooks that reference these types. `lean_game_defs_ext` (next) extends it with Bayesian mechanism-design proofs.

---

### 8. lean_game_defs_ext

**Objective**: Bayesian games & mechanism design — Vickrey truthfulness, Bayesian-Nash equilibrium, auctions, reputation. Extension of `lean_game_defs` (shared definitions), Mathlib-free.

**Toolchain**: v4.31.0-rc1 | **Dependencies**: Lean core (Mathlib-free)

| File | sorry | Description |
|------|-------|-------------|
| `Bayesian/Types.lean` | 0 | Bayesian game type definitions |
| `Bayesian/Bayesian.lean` | 0 | Bayesian-Nash equilibrium framework |
| `Bayesian/Vickrey.lean` | 0 | Vickrey (second-price auction) truthfulness theorem |
| `Bayesian/Auction.lean` | 0 | Auction mechanisms |
| `Bayesian/BNE.lean` | 0 | Bayesian-Nash equilibrium refinement |
| `Bayesian/Information.lean` + `InfoGames.lean` | 0 | Information structures, info games |
| `Bayesian/Reputation.lean` | 0 | Reputation dynamics |
| `Bayesian/Max.lean` + `Sum.lean` | 0 | Max/sum helpers |
| `Bayesian/Examples.lean` | 0 | Worked examples |

**Build**: `lake build` — SUCCESS | **COMPLETE: 0 sorry, no Mathlib**

**Status**: Vickrey truthfulness (second-price auction dominant strategy = truthful bidding) proved 0 sorry, Mathlib-free. Backend for the Lean-11b BayesianGamesExt companion notebook.

---

### 9. conway_cgt_lean

**Objective**: Reference tour of combinatorial game theory (surreal numbers, partizan games, nimbers) using Mathlib's `SetTheory.Surreal` / `PGame` / `Game` / `Nimber`. Inspired by `vihdzp/combinatorial-games` and Conway's *On Numbers and Games*.

**Toolchain**: v4.31.0-rc1 | **Dependencies**: Mathlib4

| File | sorry | Description |
|------|-------|-------------|
| `CGTTour.lean` | 0 | Tour: `LinearOrder` on Surreal, PGame constructions, nimber structure |

**Build**: `lake build CGTTour` — SUCCESS | **Reference tour, 0 sorry**

**Status**: Reference / pedagogical tour, not a proving target. Demonstrates Mathlib's combinatorial-game-theory API (surreals, `PGame`, `Nimber`) rather than proving new CGT theorems. 0 sorry.

---

## Remaining Proving Targets

| Priority | Target                       | Dir                    | sorry | Feasibility                        |
|----------|------------------------------|------------------------|-------|------------------------------------|
| —        | *(none — all GameTheory lakes are 0 sorry)* | —                      | 0     | —                                  |

> **Note (G.9 correction):** the former P1 row `Basic.lean L309 hCore / 1 sorry / Very Low (Hahn-Banach)`
> was stale. Verified firsthand: `CooperativeGames/Basic.lean` has **0** standalone-sorry lines
> (`grep -nE '^\s*sorry\b'` → empty), no `hCore`/`sorry` at L309. `bondareva_shapley`
> (`Core.Nonempty ↔ Balanced`) is fully proved (#3954, compact-slice Weierstrass — no added axiom).
> Removing this stale target prevents a pointless BG-iter cycle on a sorry that no longer exists
> (cf. lean-merge-discipline §2).

## GO/NO-GO per Project (for BG iter cycles)

| Project                | Decision | Reasoning                                                      |
|------------------------|----------|----------------------------------------------------------------|
| game_theory_lean       | COMPLETE | 3 sorry (Lattice, Knuth lattice stretch). StableMarriage: former false statements refuted, honest `exists_isManOptimal` proved. Absorbed standalone `stable_marriage_lean/` (EPIC #4365). |
| cooperative_games_lean | COMPLETE | 0 sorry. Bondareva-Shapley proven (#3954) via compact-slice Weierstrass; hCore bypassed without added axiom. |
| social_choice_lean     | N/A      | COMPLETE (0 sorry). MechanismDesign added (#1469).             |
| social_choice_lean_peters | N/A   | Reference only (pinned v4.27.0-rc1).                           |

Conway calibration targets (Doomsday / FRACTRAN / Look-and-Say / Nim / Angel) live in `SymbolicAI/Lean/conway_lean/` and are still consumed by `agent_tests/prover/config.py` (#1453 prover harness co-evolution).

---

## Related documentation

- [docs/lean/sota-2026-analysis.md](../../docs/lean/sota-2026-analysis.md) — SOTA in automated Lean 4 proving
- [docs/lean/prover_iteration_history.md](../../docs/lean/prover_iteration_history.md) — Prover iterations F6-F11, B3
- [docs/lean/llm-endpoints.md](../../docs/lean/llm-endpoints.md) — LLM providers for the prover
- [docs/lean/coordinator-workflow.md](../../docs/lean/coordinator-workflow.md) — Coordinator build + BG iter workflow
