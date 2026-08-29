# Lean 4 Projects Inventory — GameTheory

Cross-directory inventory of all Lean 4 formalization projects under `GameTheory/`.

Réconcilié le 2026-08-26 contre les pins effectifs (`lean-toolchain`, `lake-manifest.json`) et le
module-set réel du disque (issue #13138). Comptes `sorry` mesurés avec l'instrument canonique
`scripts/lean/count_code_sorry.py --json` (champ `distinct_code_sorry`), jamais `grep -c sorry`.

## Summary

**Lakes actifs (8)** :

| Directory | Toolchain | Production sorry | Modules | Status |
|-----------|-----------|-----------------|---------|--------|
| `game_theory_lean` | v4.32.1 | 1 (Folk stretch, #4880) | StableMarriage + CooperativeGames + SocialChoice + RepeatedGames + Swaps (49 `.lean` FR+EN) | COMPLETE (EPIC #4365) |
| `lean_game_defs` | v4.32.1 | 0 | 12 (6 FR + 6 `_en`) | COMPLETE (shared defs) |
| `lean_game_defs_ext` | v4.32.1 | 0 | Bayesian/* 24 (12 FR + 12 `_en`) + 2 umbrellas | COMPLETE |
| `minimax_lean` | v4.32.1 | 0 | ZeroSum + Concavity + SionApplication (+ `_en`) | COMPLETE |
| `assignment_lean` | v4.32.1 | 0 | Definitions / Duality / KuhnMunkres / Optimality (+ `_en`) | COMPLETE (#12598) |
| `asymmetric_information_lean` | v4.32.1 | 0 | Lemons / Signaling / Screening / MiyazakiWilson / BayesianLink (+ `_en`) | COMPLETE (Epic #12844) |
| `social_choice_lean_peters` | v4.32.1 | 0 | PetersTour (+ `_en`) | Reference only |
| `conway_cgt_lean` | v4.31.0-rc2 | 0 | CGTTour (+ `_en`) | Reference tour |

**Tombstones (absorbés, EPIC #4365)** :

| Directory | Devenir |
|-----------|---------|
| ~~`cooperative_games_lean`~~ | **Supprimé** (rm #6587) → [`game_theory_lean/CooperativeGames/`](game_theory_lean/CooperativeGames/) |
| ~~`social_choice_lean`~~ | Absorbé (#6058, 2026-07-11) → [`game_theory_lean/SocialChoice/`](game_theory_lean/SocialChoice/) — ne subsistent que 4 markdown tombstone |
| ~~`repeated_games_lean`~~ | Absorbé (#6146) → [`game_theory_lean/RepeatedGames/`](game_theory_lean/RepeatedGames/) — coquille archive conservée (lakefile neutralisé, 0 module) |

Note: `SymbolicAI/Lean/examples/llm_assisted_proof.lean` (2 sorry) is a pedagogical example, not production. `asymmetric_information_lean` carries 2 *naive* sorry (prose/docstrings) for 0 real code sorry.

**Conway tribute series relocated**: `conway_lean/` (Conway hommage — Doomsday, FRACTRAN, Look-and-Say, Nim, Angel) was moved to [`SymbolicAI/Lean/conway_lean/`](../SymbolicAI/Lean/conway_lean/) since it formalizes lesser-known Conway results (not game-theoretic content per se). The prover calibration targets defined in `agent_tests/prover/config.py` follow the new path.

**Calibration relocated**: `calibration_lean/` was moved to [`SymbolicAI/Lean/calibration_lean/`](../SymbolicAI/Lean/calibration_lean/) (issue #1764) since it is a prover harness component, not game-theoretic content.

---

## Directories

### 1. game_theory_lean

**EPIC #4365 (phase 4)**: multi-module target lake, pôle d'absorption GT 6→2. A absorbé :
`stable_marriage_lean/` (supprimé, PRs #5904/#5905/#5910/#5911/#5913), `cooperative_games_lean/`
(rm #6587), `social_choice_lean/` (#6058), `repeated_games_lean/` (#6146). Le lake porte
également `Swaps` (grain #12222, compagnon du notebook GameTheory-03a).

**Objective**: Formalize the GameTheory curriculum — cooperative games (Shapley, core), Gale-Shapley stable marriage, social choice (Arrow, Sen, median voter), repeated games (folk theorem), swap paths on 2×2 ordinal games.

**Toolchain**: v4.32.1 | **Dependencies**: Mathlib4

| Module group | sorry | Content |
|--------------|-------|---------|
| `StableMarriage/` (5 FR + 5 `_en`) | 0 | GS algorithm, termination, stability, `exists_isManOptimal`, woman_pessimal, Knuth lattice + refutations of former false statements |
| `CooperativeGames/` (3 FR + 3 `_en`) | 0 | TU games, Core, `bondareva_shapley : Core.Nonempty ↔ Balanced`, Shapley value (Möbius decomposition), cone-separation machinery |
| `SocialChoice/` (9 FR + 8 `_en`) | 0 | Arrow (Geanakoplos 2005), Sen's Liberal Paradox, median voter / Split Cycle / clones, Vickrey truthfulness, AMD, `PrefOrder`/`Profile`/SWF core |
| `RepeatedGames/` (4 FR + 4 `_en`) | 1 (stretch) | `grim_trigger_sustains_iff` (théorème-phare, 0 sorry) ; `folk_theorem_discounted` / `folk_theorem_boundary` portent 1 sorry stretch (#4880) |
| `Swaps/` (FR-only) | 0 | `Table`, générateurs adjacents, certificat de chemin, `distance_dilemme_chicken` |

**Build**: `lake build` — SUCCESS. CI: `lean-game-theory.yml`, `lean-social-choice.yml`.

**Key proofs**:
- `gale_shapley_stable` — PR #1194 ; `exists_isManOptimal` (honest, via minimal-weight on join semilattice) ; `woman_pessimal` — PR #1521 ; `meetSpouse_injective` / `joinSpouse_injective` — PR #1522
- `no_cross_match_is_false` / `doctor_optimal_eq_top_is_false` — kernel-checked refutations of former false statements
- `bondareva_shapley` (`Core.Nonempty ↔ Balanced`) — fully proved, no added axiom (compact-slice Weierstrass, #3954)
- `grim_trigger_sustains_iff` — FORMAL-CERTIFIED, 0 sorry

---

### 2. ~~cooperative_games_lean~~ — Supprimé (rm #6587)

> **Lake standalone supprimé** (commit `522c450e9`, PR #6587). Modules `Basic` / `ConeKernel` /
> `Shapley` (+ jumeaux `_en`) absorbés byte-identique dans
> [`game_theory_lean/CooperativeGames/`](game_theory_lean/CooperativeGames/) (EPIC #4365). La
> section ci-dessous est conservée comme trace d'audit du statut de preuve (0 sorry, préservé
> dans la cible). Pour l'état courant, voir [§1. game_theory_lean](#1-game_theory_lean).

**Status at removal**: COMPLETE (0 sorry). `bondareva_shapley` fully proved — the backward
direction's attainment crux `hb_witness` closed by PR #3954 via a compact-slice Weierstrass
argument, bypassing the missing Mathlib `ProperCone.hyperplane_separation` without any added
axiom. Lineage: #3933 (cone kernel) → #3941 (bridge) → #3945 (decoding) → #3951 (`hb_strict`) →
#3954 (attainment).

---

### 3. ~~social_choice_lean~~ — Absorbé (#6058)

> **⚑ Tombstone documentaire — home canonique déplacé.** Depuis la PR #6058 (EPIC #4365
> Phase-4, 2026-07-11), les sept modules (Basic, Framework, Arrow, Sen, Voting,
> MechanismDesign, SortedListCounting) ont été absorbés byte-identique dans
> [`game_theory_lean/SocialChoice/`](game_theory_lean/SocialChoice/) (FR canonique + miroirs
> `_en.lean` Pattern A #4980). **Ce répertoire n'est plus un lake** — la coquille technique
> (`lakefile.lean`, `lean-toolchain`, `lake-manifest.json`) a été retirée ; ne subsistent que
> 4 markdown (`README`, `STATUS`, `NOTICE`, `LEAN_PREREQUISITES`) conservés comme tombstone.

**Status (historique, préservé dans le home canonique)**: COMPLETE, 0 sorry — Arrow's
Impossibility (Geanakoplos 2005), Sen's Liberal Paradox, Median Voter / Split Cycle / clones,
Vickrey truthfulness + first-price counter-example (#1469). Build repris par
`.github/workflows/lean-social-choice.yml` sur `game_theory_lean`.

---

### 4. social_choice_lean_peters

**Objective**: Reference project importing DominikPeters/SocialChoiceLean as a Lake dependency.

**Toolchain**: v4.32.1 (convergé avec le parc depuis #12134, 2026-08-21) | **Dependencies**: Mathlib4 (`520045ab`), SocialChoiceLean `94a4c650` (revs effectives du `lake-manifest.json`)

| File | sorry | Description |
|------|-------|-------------|
| `PetersTour.lean` + `PetersTour_en.lean` | 0 | Curated tour of Peters' formalized results (i18n #4980) |

**Build**: `lake build` — SUCCESS | **Reference only, not for proving**

**Content**: Imports Peters' library (Gibbard-Satterthwaite, Duggan-Schwartz, 4 Condorcet impossibilities, 15+ voting rules with axiom verification). Backend Lake for the (planned, not yet created) SocialChoiceLean tour companion notebook.

**Relationship to `social_choice_lean` (absorbé)**: Complementary, not duplicate. Notre cadre historique utilisait un `PrefOrder` custom (nos preuves, désormais dans `game_theory_lean/SocialChoice/`) ; ce lake expose le `LinearOrder` de Peters (référence externe). Both kept for pedagogical completeness.

---

### 5. ~~repeated_games_lean~~ — Absorbé (#6146)

> **⚑ Archive — home canonique déplacé.** Depuis la PR #6146 (EPIC #4365 Phase-4), les quatre
> modules sources (`Stage`, `Discounting`, `GrimTrigger`, `Folk`) ont été absorbés
> byte-identique dans [`game_theory_lean/RepeatedGames/`](game_theory_lean/RepeatedGames/).
> Ce répertoire est conservé comme **coquille archive** : `package`, `require mathlib`,
> manifest et documentation restent présents, mais la `lean_lib` est neutralisée dans le
> `lakefile.lean` (ses globs matchaient 0 fichier depuis le déménagement). Certification et
> build repris par `game_theory_lean` (`.github/workflows/lean-game-theory.yml`).

**Status (historique, préservé dans le home canonique)**: `grim_trigger_sustains_iff`
(sustains a subgame-perfect Nash iff δ ≥ threshold) fully proved, 0 sorry. The Folk theorem
(`folk_theorem_discounted`) carries 1 stretch sorry, tolerated per #4880.

---

### 6. minimax_lean

**Objective**: Formalize the two-player zero-sum game minimax setting — payoff bilinearity, concavity, and the Sion minimax application.

**Toolchain**: v4.32.1 | **Dependencies**: Mathlib4

| File | sorry | Description |
|------|-------|-------------|
| `Minimax/ZeroSum.lean` (+ `_en`) | 0 | Zero-sum payoff structure, bilinearity (`payoff_add_in_x`, `smul`), `continuous_payoff`; saddle-point existence derived from Mathlib's Sion minimax |
| `Minimax/Concavity.lean` (+ `_en`) | 0 | Concavity lemmas feeding the Sion application |
| `Minimax/SionApplication.lean` (+ `_en`) | 0 | Sion minimax application to the mixed-strategy saddle point |

**Build**: `lake build Minimax` — SUCCESS | **COMPLETE: 0 sorry**

**Key facts**: payoff bilinearity and continuity proven 0 sorry; **saddle-point existence** (`∃ mixed strategies, max_x min_y = min_y max_x`) is *derived* from Mathlib's Sion minimax theorem — documented and proved, **not** left as a `sorry`.

---

### 7. lean_game_defs

**Objective**: Shared game-theoretic type definitions (normal-form games, Bayesian games, combinatorial games, social choice, regret) — the foundational layer reused by the GT Lean notebooks. Self-contained (core Lean only, zero Mathlib dependency).

**Toolchain**: v4.32.1 | **Dependencies**: Lean core (Mathlib-free)

| File (FR + `_en` sibling) | sorry | Description |
|---------------------------|-------|-------------|
| `LeanGameDefs/Basic.lean` | 0 | NormalFormGame / FiniteGame / Game2x2 core types |
| `LeanGameDefs/Nash.lean` | 0 | Nash equilibrium, best response, strict dominance |
| `LeanGameDefs/Bayesian.lean` | 0 | Bayesian game types |
| `LeanGameDefs/Combinatorial.lean` | 0 | Combinatorial game types, minimax |
| `LeanGameDefs/SocialChoice.lean` | 0 | Social choice primitives (`dictatorship_satisfies_pareto`, `dictatorship_satisfies_iia`) |
| `LeanGameDefs/Regret.lean` | 0 | Regret / CFR definitions |

**Build**: `lake build LeanGameDefs` — SUCCESS (CI `lean-game-defs.yml` + `lean-game-defs-ext.yml`) | **COMPLETE: 0 sorry, Mathlib-free**

**Status**: Lake autonome depuis #2752 (`lakefile.toml`, `lean-toolchain` pinné v4.32.1, `lake-manifest.json`, CI dédiée). Infrastructural definitions layer (2 theorems verifying dictatorship axioms), backend for the GT Lean notebooks. `lean_game_defs_ext` (next) extends it with Bayesian mechanism-design proofs.

---

### 8. lean_game_defs_ext

**Objective**: Bayesian games & mechanism design — Vickrey truthfulness, Bayesian-Nash equilibrium, auctions, reputation, fictitious play, regret. Extension of `lean_game_defs` (shared definitions), Mathlib-free.

**Toolchain**: v4.32.1 | **Dependencies**: Lean core (Mathlib-free)

| File (FR + `_en` sibling) | sorry | Description |
|---------------------------|-------|-------------|
| `Bayesian/Types.lean` | 0 | Bayesian game type definitions |
| `Bayesian/BNE.lean` | 0 | Bayesian-Nash equilibrium framework + refinement |
| `Bayesian/Vickrey.lean` | 0 | Vickrey (second-price auction) truthfulness theorem |
| `Bayesian/Auction.lean` | 0 | Auction mechanisms |
| `Bayesian/Information.lean` + `InfoGames.lean` | 0 | Information structures, info games |
| `Bayesian/Reputation.lean` | 0 | Reputation dynamics |
| `Bayesian/FictitiousPlay.lean` + `Regret.lean` | 0 | Fictitious play, regret minimization |
| `Bayesian/Max.lean` + `Sum.lean` | 0 | Max/sum helpers |
| `Bayesian/Examples.lean` | 0 | Worked examples |

**Build**: `lake build` — SUCCESS | **COMPLETE: 0 sorry, no Mathlib**

**Status**: Vickrey truthfulness (second-price auction dominant strategy = truthful bidding) proved 0 sorry, Mathlib-free. Backend for the Lean-11b BayesianGamesExt companion notebook.

---

### 9. conway_cgt_lean

**Objective**: Reference tour of combinatorial game theory (surreal numbers, partizan games, nimbers) as formalized in [`vihdzp/combinatorial-games`](https://github.com/vihdzp/combinatorial-games), imported as a Lake dependency. Upstream is the current home of CGT in Lean after Mathlib's CGT modules (`SetTheory.Surreal`/`PGame`/`Game`/`Nimber`) were deprecated (#28063, Aug 2025) then removed (#35550, Feb 2026). Reference: Conway, *On Numbers and Games* (2001).

**Toolchain**: v4.31.0-rc2 (tracks the upstream repo) | **Dependencies**: Mathlib4 + CombinatorialGames (Apache-2.0, `3c6dcdbc`)

| File | sorry | Description |
|------|-------|-------------|
| `CGTTour.lean` + `CGTTour_en.lean` | 0 | Tour of `IGame`/`Game` (concrete pre-games + quotient), `Surreal` (simplicity theorem), `Nimber` (Sprague-Grundy), with a Mathlib-vs-upstream comparison table |

**Build**: `lake build CGTTour` — SUCCESS | **Reference tour, 0 sorry**

**Status**: Reference / pedagogical tour, not a proving target. Exhibits the upstream API via `#check` + docstrings rather than proving new CGT theorems.

---

### 10. assignment_lean

**Objective**: Correction skeleton of the Kuhn-Munkres (Hungarian) assignment algorithm — companion lake of the notebook GameTheory-27-Munkres-Assignment, hommage à James R. Munkres (1930-2026). Issue #12598 (1/3). The primal (cost matrix, perfect matching, value), the dual (potentials, feasibility, **weak duality**), the zero-gap optimality certificate, and the algorithm's structural invariants (equality graph, **output invariant**, **Hungarian tightening preserves dual feasibility**). Termination and O(n³) complexity deliberately out of scope.

**Toolchain**: v4.32.1 | **Dependencies**: Mathlib4

| File (FR + `_en` sibling) | sorry | Description |
|---------------------------|-------|-------------|
| `Assignment/Definitions.lean` | 0 | Cost matrix, perfect matching (permutation), value, optimality (`value`, `IsOptimal`) |
| `Assignment/Duality.lean` | 0 | Dual potentials `u`/`v`, dual feasibility, **weak duality** (`DualFeasible`, `dualValue`, `weak_duality`) |
| `Assignment/Optimality.lean` | 0 | Zero-gap optimality certificate + equality-edge lemma (`dualValue_eq_of_edges`, `optimality_of_zero_gap`) |
| `Assignment/KuhnMunkres.lean` | 0 | Equality graph, **output invariant**, **Hungarian tightening** preserves dual feasibility (`EqEdge`, `kuhn_munkres_correct`, `dualFeasible_tighten`) |
| `Assignment/*_en.lean` (×4) | 0 | i18n siblings (EPIC #4980) |

**Build**: `lake build Assignment Assignment_en` — SUCCESS (8665 jobs, cf PR #12614) | **COMPLETE: 0 sorry** (distinct_code_sorry = 0)

**Key theorems**: `weak_duality`, `dualValue_eq_of_edges`, `optimality_of_zero_gap`, `kuhn_munkres_correct`, `dualFeasible_tighten`.

**Status**: COMPLETE. Companion notebooks: GT-27 (Python implementation + scipy SOTA) and GT-27b (native `lean4-wsl` companion — `#check` of all 10 declarations + kernel-proved `optimal_C3` certificate, EPIC #11703 visibility).

---

### 11. asymmetric_information_lean

**Objective**: Formalize the foundational models of information asymmetry — companion of the GT-17 notebooks. Epic #12844 (first delivery, portée bornée conforme à l'audit canonique c.475).

**Toolchain**: v4.32.1 | **Dependencies**: Lean core + `lean_game_defs_ext.Bayesian` (no Mathlib dependency)

| File (FR + `_en` sibling) | sorry | Description |
|---------------------------|-------|-------------|
| `AsymmetricInformation/Lemons.lean` | 0 | Akerlof (1970) lemons market — participation-regions fixed point |
| `AsymmetricInformation/Signaling.lean` | 0 | Spence (1973) education signal |
| `AsymmetricInformation/Screening.lean` | 0 | Rothschild-Stiglitz (1976) adverse selection |
| `AsymmetricInformation/MiyazakiWilson.lean` | 0 | Wilson (1977) / Miyazaki (1977) anticipatory cross-subsidy |
| `AsymmetricInformation/BayesianLink.lean` | 0 | Non-trivial bridge to `lean_game_defs_ext.Bayesian` |

**Build**: `lake build` — SUCCESS | **COMPLETE: 0 code sorry** (2 naive hits = prose)

**Bornes explicites** (per README): no general existence/uniformity theorem for the anticipatory equilibrium (Wilson-MWS); no auxiliary clause in κ (Lemons); no cross-subsidy in RS 1976; no Mathlib `sorry`-backed milestone — proofs on Lean 4 core + `decide`/`omega`.

---

## Remaining Proving Targets

| Priority | Target | Dir | sorry | Feasibility |
|----------|--------|-----|-------|-------------|
| P3 | `folk_theorem_discounted` / `folk_theorem_boundary` (stretch toléré) | `game_theory_lean/RepeatedGames/Folk.lean` (+ `_en`) | 1 stretch (#4880) | Low — authentically hard direction (`… = u_col`), grim already covers the closure criterion |

> **Note (G.9 correction, 2026-08-26):** l'ancienne ligne P1 « Basic.lean L309 hCore / Very Low
> (Hahn-Banach) » était stale (#3954 l'a close) ; l'ancien compte « 3 (Lattice) » pour
> `game_theory_lean` était stale aussi — `StableMarriage/Lattice.lean` est à 0 sorry
> (vérifié `count_code_sorry.py` : `distinct_code_sorry = 1`, localisé à `Folk.lean:127`).
> Removing stale targets prevents a pointless BG-iter cycle on a sorry that no longer exists
> (cf. lean-merge-discipline §2).

## GO/NO-GO per Project (for BG iter cycles)

| Project | Decision | Reasoning |
|---------|----------|-----------|
| game_theory_lean | COMPLETE | 1 sorry (Folk stretch, toléré #4880). StableMarriage: former false statements refuted, honest `exists_isManOptimal` proved; Lattice closed. Absorbed `stable_marriage_lean/` + `cooperative_games_lean/` + `social_choice_lean/` + `repeated_games_lean/` (EPIC #4365). |
| ~~cooperative_games_lean~~ | **Supprimé** (rm #6587) | Absorbed byte-identique into `game_theory_lean/CooperativeGames/`. |
| ~~social_choice_lean~~ | **Absorbé** (#6058) | 7 modules → `game_theory_lean/SocialChoice/` ; tombstone docs only. |
| ~~repeated_games_lean~~ | **Absorbé** (#6146) | 4 modules → `game_theory_lean/RepeatedGames/` ; archive shell. |
| lean_game_defs / _ext | COMPLETE | 0 sorry, Mathlib-free. |
| minimax_lean | COMPLETE | 0 sorry ; Sion application proved. |
| assignment_lean | COMPLETE | 0 sorry (#12598). |
| asymmetric_information_lean | COMPLETE | 0 code sorry (Epic #12844). |
| social_choice_lean_peters | N/A | Reference only (Peters `94a4c650`, Mathlib `520045ab`, v4.32.1). |
| conway_cgt_lean | N/A | Reference tour (v4.31.0-rc2, tracks upstream). |

Conway calibration targets (Doomsday / FRACTRAN / Look-and-Say / Nim / Angel) live in `SymbolicAI/Lean/conway_lean/` and are still consumed by `agent_tests/prover/config.py` (#1453 prover harness co-evolution).

---

## Related documentation

- [docs/lean/sota-2026-analysis.md](../../docs/lean/sota-2026-analysis.md) — SOTA in automated Lean 4 proving
- [docs/lean/prover_iteration_history.md](../../docs/lean/prover_iteration_history.md) — Prover iterations F6-F11, B3
- [docs/lean/llm-endpoints.md](../../docs/lean/llm-endpoints.md) — LLM providers for the prover
- [docs/lean/coordinator-workflow.md](../../docs/lean/coordinator-workflow.md) — Coordinator build + BG iter workflow
