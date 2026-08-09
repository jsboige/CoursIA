# Conway Lean

Lean 4 formalization of Conway's mathematical games and algorithms.

## Status

- **Toolchain**: v4.31.0-rc1
- **Sorry count**: **2** (code-level, canonical FR — post-split count #9883/#9884; +1 `_en` twin = 3 counting `HashlifeMarginFragment_en.lean`). **P4: 0 sorry** (double-nine inductive step PROVEN post-split — `p4_succ_membership` sorry-free, consumed by `hashlifeResult_central_correct` via `p4_ext_bridge`) + **P5 large-n: 2 sorry** (`p5_large_n_jumpN` aggregator L1156/sorry L1159 + `hashlife_correct_margin` `HashlifeMarginFragment.lean` L136/sorry L145). Raw `grep` over-counts (~23 hits in the aggregator alone) via docstring prose; canonical code-level count via stripping docstrings `/- … -/` + `--` comments. The old counts "8 sorry / P4: 5 / P5: 3" and line numbers `L2893-3706` below date from the **pre-split monolith** (7082 lines) and are **stale** — the current aggregator is 1283 lines. See § "Honest state of the HashlifeCorrectness lock" for the post-split per-declaration breakdown. **Audit N1 (PR #5853, ai-01 2026-07-09)**: the initial frame sub-claim (`BoxAssezGrand` ∩ `n ≥ jumpSize`) is **VACUOUS on non-empty grids** (`p5_large_n_hyps_unsat`: padding 2 of `gridFrame` ∧ `lvl ≥ 3` ⇒ `n ≤ 2 ∧ js ≥ 8`) — which is why `hashlife_correct` (aggregator L1092) is proven via `p5_inductive_step` but remains *vacuous* in the large-`n` regime, and why the N-aware statement `hashlife_correctN` + the jump `p5_large_n_jumpN` (the genuine P5.2, open sorry) were introduced. **Design gate ai-01 (#3846, 2026-07-10)**: redesign `gridFrame` for `n`-dependent padding, port the `(off, mc)` state through the `evolveHashlifeFastAux` loop without intermediate re-framing, restate the "margin ≥ remaining n, preserved by jump" invariant. The proof debt (#3846) remains the BG-prover target and the coordinated architectural redesign scope.
- **Build**: `lake build Conway` -- SUCCESS (3352 jobs)
- **Dependencies**: Mathlib4
- **i18n coverage (EPIC #4980)**: **25 conway_lean modules** shipped as FR-canonical + `_en` sibling on `main` (all but `HashlifeCorrectness.lean`, the P4/P5 prover target which remains EN-only) — Phase 1: **10/10**; Phase 2: **13/14** (`ConeGeometry` included); Phase 3: **2/2**. Rollout complete (c.290-#6439 + cycles c.421-c.423 merged).

## Modules

### Phase 1 — Classic algorithms (Epic #1151, COMPLETE)

| File | `_en` | sorry | Description |
|------|-------|-------|-------------|
| `Conway/Doomsday.lean` | `Doomsday_en.lean` | 0 | Doomsday algorithm (day-of-week calculation) |
| `Conway/DoomsdayLemmas.lean` | `DoomsdayLemmas_en.lean` | 0 | Lemmas for the Doomsday algorithm |
| `Conway/Fractran.lean` | `Fractran_en.lean` | 0 | FRACTRAN programming language |
| `Conway/FractranLemmas.lean` | `FractranLemmas_en.lean` | 0 | Lemmas for FRACTRAN (step/run: halt empty, 0-run, `num/1` applicability, concrete trace `{3/2}` 2→3) |
| `Conway/LookAndSay.lean` | `LookAndSay_en.lean` | 0 | Look-and-Say sequence |
| `Conway/LookAndSayLemmas.lean` | `LookAndSayLemmas_en.lean` | 0 | Lemmas for the Look-and-Say sequence |
| `Conway/Nim.lean` | `Nim_en.lean` | 0 | Nim game theory |
| `Conway/Angel.lean` | `Angel_en.lean` | 0 | Angel problem |
| `Conway/CollatzLike.lean` | `CollatzLike_en.lean` | 0 | Collatz-like functions and undecidability (`native_decide`) |
| `Conway/MathlibMap.lean` | `MathlibMap_en.lean` | 0 | Mathlib pinned-snapshot satellite — what Mathlib provides for Conway's work |

### Phase 2 — Game of Life (Epic #1647, IN PROGRESS)

| File | `_en` | sorry | Description |
|------|-------|-------|-------------|
| `Conway/Life.lean` | `Life_en.lean` (root) | 0 | B3/S23 rules, grid operations, step/evolve, `native_decide` proofs |
| `Conway/Life/Spaceships.lean` | `Spaceships_en.lean` | 0 | LWSS/MWSS/HWSS (period 4, displacement (0,2)), 3 `native_decide` proofs |
| `Conway/Life/Oscillators.lean` | `Oscillators_en.lean` | 0 | 5 still-lifes + pulsar (p3) + pentadecathlon (p15), 7 `native_decide` |
| `Conway/Life/RLE.lean` | `RLE_en.lean` | 0 | RLE pattern parser + glider/LWSS/pulsar/Gosper gun, 8 `native_decide` proofs |
| `Conway/Life/MacroCell.lean` | `MacroCell_en.lean` | 0 | Quadtree datatype + `toGrid`/`buildFromGrid` round-trip + `wf` predicate |
| `Conway/Life/Hashlife.lean` | `Hashlife_en.lean` | 0 | `step4x4` + `hashlifeResult` recursive + `padCenter2` + `hashlifeJump` + `evolveHashlifeFast` |
| `Conway/Life/LightCone.lean` | `LightCone_en.lean` | 0 | Light-cone geometry satellite — sorry-free lemmas on `manhattan`/`lightCone` bridging `HashlifeCorrectness` |
| `Conway/Life/ConeGeometry.lean` | `ConeGeometry_en.lean` | 0 | Cone geometry — pure lattice facts (Mathlib only) |
| `Conway/Life/GridCanonical.lean` | `GridCanonical_en.lean` | 0 | `sortDedup` canonical forms, lex-sorted uniqueness, grid equality via canonical form |
| `Conway/Life/Computation.lean` | `Computation_en.lean` | 0 | Hashlife cross-validation (6 + 6 fast), eater1 still-life (1), glider composition (5) |
| `Conway/Life/HashlifeMemo.lean` | `HashlifeMemo_en.lean` | 0 | Memoized Hashlife for community pillar witnesses (OTCA 35K, UnitCell 4096, Gemini 33M) |
| `Conway/Life/HashlifeMarginDemo.lean` | `HashlifeMarginDemo_en.lean` | 0 | Runnable P5 redesign demo (#3846) — n-aware framing margin around `MacroCell`/`HashlifeCorrectness` |
| `Conway/Life/Pillars.lean` | `Pillars_en.lean` (c.417) | 0 | Community-witness theorem scaffolding (4 pillars) |
| `Conway/Life/HashlifeCorrectness.lean` | — | 2 | Bounded correctness `hashlife_correct` (proven but vacuous at large-n); P5 prover target (Epic #1453, #2162). **P4 PROVEN sorry-free post-split #9883/#9884** (0 sorry — `p4_succ_membership` sorry-free). 2 = P5 large-n (`p5_large_n_jumpN` L1159 + `hashlife_correct_margin` L145 INTRINSIC). The old P4 items `p4_nw_supercell_agree`/`p4_nw_membership_arm` and line numbers L2893-3706 date from the pre-split monolith (7082 lines) — **stale**. |

### Phase 3 — Free Will Theorem (Epic #1651, COMPLETE)

| File | `_en` | sorry | Description |
|------|-------|-------|-------------|
| `Conway/KochenSpecker.lean` | `KochenSpecker_en.lean` | 0 | KS 18-vec Cabello proof (parity argument) |
| `Conway/FreeWillTheorem.lean` | `FreeWillTheorem_en.lean` | 0 | Conway-Kochen FWT (SPIN + TWIN + MIN) |

## Key Results

### Classic algorithms (Phase 1)

- Doomsday algorithm correctness
- FRACTRAN computation formalization
- Look-and-Say sequence properties
- Nim game strategy
- Angel problem formalization
- Collatz-like undecidability (`native_decide` on finite instances)

### Game of Life (Phase 2)

- **Grid/List encoding**: `Grid = List (Int x Int)` with Bool predicates, `native_decide` proofs
- **RLE parser**: Complete Run Length Encoded format parser with proven correctness
  - 4 parse-success theorems, 2 round-trip equalities, 2 cell-count theorems
  - Gosper Glider Gun (36 live cells, period 30) parsed and verified
- **Spaceships**: LWSS, MWSS, HWSS with period-4 displacement proofs
- **Oscillators**: Blinker (p2), toad (p2), beacon (p2), pulsar (p3), pentadecathlon (p15)
- **MacroCell well-formedness**: `MacroCell.wf` predicate (PR #2795), grid-side constructors produce wf cells
- **Grid canonical forms**: `sortDedup` outputs are lex-sorted and unique (PR #2797)
- **Hashlife**: Quadtree MacroCell + recursive hashlife algorithm with exponential speedup
  - `step4x4`: level-2 base case (B3/S23 direct)
  - `hashlifeResult`: recursive level-k to level-(k-1), `2^(k-2)` generations
  - `padCenter2`: proper centered padding (+2 levels, single copy)
  - `hashlifeJump` + `evolveHashlifeFast`: exponential-speedup API
  - Cross-validated against list-based reference on 12 patterns (6 + 6 fast path)
  - Eater 1 (fishhook) still-life proved by `native_decide`
  - Multi-period glider composition theorems
- **Memoized Hashlife**: Community pillar witnesses (OTCA 35K gen, UnitCell 4096 gen, Gemini 33M gen)
- **HashlifeCorrectness**: bounded correctness `hashlife_correct`, decomposed P1-P5
  - **P1-P3 proven** (base case `k=0` via `2^16 native_decide`, PR #2810)
  - **P4 inductive step — PROVEN sorry-free post-split #9883/#9884** (0 sorry): the scaffolding decomposes the inductive step into sub-lemmas all sorry-free in `Foundation.lean` — `p4_double_nine_shape` (structural existence of the nine quadrants of a double-nine cell), `p4_wave1_ih` and `p4_wave2_ih` (propagation of `centralCorrect` via the induction hypothesis over the two waves), `p4_ext_bridge` (reduction to the pointwise-membership biconditional), `p4_succ_membership` (the membership iff itself, sorry-free). Also sorry-free are the additive ingredients closed in cycles 145-160: `evolve_add` (S1), `evolve_half_step` (half-step `2^k`, #4555), `centralCorrect_mem_shift` (G2 offset-generalized gate, #4812) and `evolve_cone_agree` (radius-doubling locality composition gate, #4892). The P4.4 placeholder `p4_half_steps_compose` (`: True`) was **deleted** (N2-bis): its pure-evolve composition is exactly `evolve_add` + `evolve_half_step` (closed). The aggregator consumes it all: `hashlifeResult_central_correct` applies `p4_ext_bridge c (k+1) (p4_succ_membership …)` at its `k → k+1` case.
  - **P5 large-n — 2 residual sorry** (P4 gate fallen → attackable): `p5_small_n_fallback` **PROVEN** (PR #2984); `evolve_dead_of_cone_dead` (P5.2 contrapositive, #4574) **proven sorry-free**; `p5_inductive_step` (P5.3 glue) **PROVEN** by c.310 PR #5998 via vacuous-arm split; `p5_large_n_jump` (P5.2, aggregator L993) and `hashlife_correctN` (N-steps `BoxAssezGrandN`, aggregator L1181) **proven sorry-free** post-split. Remaining are 2 `sorry` theorems: `p5_large_n_jumpN` (aggregator L1156, sorry L1159 — the genuine jump `evolveHashlifeFast n g = evolve n g` on the non-vacuous N-aware frame, P5.2) + `hashlife_correct_margin` (`HashlifeMarginFragment.lean` L136, sorry L145 — INTRINSIC, bounded assembly via `supportInMargin` + the `p4_nw_overlap_wall` chain). Base case `n=0` proven (`hashlife_correct_base_zero` #2898, `evolveHashlifeFastAux_zero_n` #2901).

### Kochen-Specker + Free Will Theorem (Phase 3, PROVED)

The `KochenSpecker.lean` module formalizes the 18-vector proof by Cabello,
Estebaranz and Garcia-Alcaine (1996). It is the combinatorial kernel of the
Conway-Kochen Free Will Theorem (2006/2009, Epic #1651).

The `FreeWillTheorem.lean` module proves the full Free Will Theorem from
three physically motivated axioms (SPIN, TWIN, MIN), reducing to the
Kochen-Specker contradiction.

**Hall of Fame**:
- Kochen & Specker (1967) — original 117-vector proof
- Cabello, Estebaranz, Garcia-Alcaine (1996) — 18-vector tight proof
- Conway & Kochen (2006) — 33-vector proof + Free Will Theorem
- Peres (1991), Mermin (1993) — simplifications and pedagogy

## Conclusion

This workspace formalizes in Lean 4 three facets of John Conway's work, from classical algorithms (Phase 1) to the universal computation of the Game of Life (Phase 2) up to the quantum foundation (Phase 3, Free Will Theorem). The through-line is **formal certification**: every result is a proven theorem, not a simulation.

### What this formalism demonstrates

- **Classical algorithms** (Doomsday, FRACTRAN, Look-and-Say, Nim, Angel, Collatz) are proven on their finite instances via `native_decide` or by direct combinatorial arguments (`decide`, `omega`, parity for Kochen-Specker). Zero `sorry`.
- **The Game of Life as a computational engine**: B3/S23 rules, spaceships (LWSS/MWSS/HWSS), oscillators (blinker, pulsar p3, pentadecathlon p15), and the Hashlife method with exponential speedup. Cross-validation on 12 patterns + eater1 + glider compositions confirms that the fast implementation `evolveHashlifeFast` agrees with the `evolve` reference on all tested cases.
- **The Free Will Theorem** (Conway-Kochen 2006/2009) is proven from the three physically motivated axioms SPIN + TWIN + MIN, reducing to the 18-vector Kochen-Specker contradiction (Cabello et al. 1996). Phase 3 COMPLETE, sorry-free.

### Honest state of the HashlifeCorrectness lock

The central theorem `hashlife_correct` (bounded by the padding hypothesis `BoxAssezGrand`) is **proven** (aggregator L1092, via `exact p5_inductive_step n g h`), but its hypothesis `BoxAssezGrand g n` is structurally *capped* at `n ≤ 2` on non-empty grids (`p5_large_n_hyps_unsat`): it is therefore **vacuous in the large-`n` regime** where the Hashlife jump is actually exercised. The foundation is solid — base case `k=0` proven (`2^16 native_decide`), base case `n=0` proven, P1/P2/P3 (padding, light-cone, locality) proven, `p5_small_n_fallback` proven, `p5_inductive_step` (P5.3 glue) proven by c.310 PR #5998 via vacuous-arm split, **the P4 inductive step PROVEN sorry-free post-split** (`p4_double_nine_shape`, `p4_wave1_ih`, `p4_wave2_ih`, `p4_ext_bridge` sorry-free in `Foundation.lean`; `p4_succ_membership` sorry-free, consumed by `hashlifeResult_central_correct` via `p4_ext_bridge`), as well as the additive ingredients closed in cycles 145-160 (`evolve_add`, `evolve_half_step`, `centralCorrect_mem_shift`, `evolve_cone_agree`) and the P5.2 contrapositive (`evolve_dead_of_cone_dead`) — but the **large-`n` P5.2 jump** remains **research-level**. **Per-declaration breakdown of the 2 residual sorry** (code-level, post-split #9883/#9884; the old P4 items `p4_nw_supercell_agree`/`p4_nw_membership_arm` and line numbers `L2893-3706` date from the pre-split monolith and no longer exist):

- **P4 — double-nine inductive step**: **0 sorry (PROVEN post-split)**. The scaffolding (`p4_double_nine_shape` structural, `p4_wave1_ih`/`p4_wave2_ih` IH application, `p4_ext_bridge` reduction to the biconditional, `p4_succ_membership` membership iff) is entirely sorry-free in `Foundation.lean` + the aggregator. The `p4_half_steps_compose` placeholder (P4.4) was deleted (pure-evolve composition already closed via `evolve_add`+`evolve_half_step`).
- **P5 large-n** (2 sorry, P4 gate now fallen → attackable): `p5_large_n_jumpN` (aggregator L1156, sorry L1159, P5.2 — the genuine jump `evolveHashlifeFast n g = evolve n g` on the N-aware frame `BoxAssezGrandN`, non-vacuous at `n ≥ 8`) + `hashlife_correct_margin` (`HashlifeMarginFragment.lean` L136, sorry L145, INTRINSIC — the bounded P4/P5 assembly via `supportInMargin`, open research heart). `hashlife_correctN` (aggregator L1181) and `p5_large_n_jump` (aggregator L993) are **proven sorry-free** post-split (the former covers the `n ≤ 2` case, the latter is the legacy fixed-frame statement).

**Concrete next step**: attack `p5_large_n_jumpN` (P5.2) — the Hashlife jump `2^(k-2)` certified by `hashlifeResult_central_correct` (P4 closed) + `window_cheb_cone_in_domain` (`ConeGeometry`). With the P4 gate fallen, this is the live BG-prover target (`agent_tests/prover/`); the multi-wave light-cone composition resists current tactical automation. `hashlife_correct_margin` (INTRINSIC) additionally requires the offset-matching chain `p4_nw_overlap_wall` (`Walls/NW.lean`).

*The `hashlife_correct` correction pyramid: the proven foundation (base cases, P1-P3,
`p5_small_n_fallback`) carries the theorem, and the P4 double-nine inductive step is
now **proven sorry-free post-split** (#9883/#9884); the residual research-level target
is the large-`n` P5.2 jump (`p5_large_n_jumpN`), and `hashlife_correct` itself is proven
but vacuous in the large-`n` regime (its `BoxAssezGrand g n` hypothesis is capped at `n ≤ 2`):*

```mermaid
flowchart TD
    BASE["Base cases  <b>proven</b><br/>k=0 (2¹⁶ native_decide) · n=0"]
    P1["P1 — Padding<br/>box_assez_grand · natCeilLog2  <b>✓</b>"]
    P2["P2 — Light-cone<br/>step_light_cone  <b>✓</b>"]
    P3["P3 — Locality<br/>aliveNext_local · step_local  <b>✓</b>"]
    P5S["P5 small-n<br/>p5_small_n_fallback  <b>✓</b> (#2984)"]
    P4["P4 — Double-nine inductive step  <b>✓ PROVEN (post-split #9883/#9884)</b><br/>0 sorry · p4_double_nine_shape + p4_wave1_ih + p4_wave2_ih + p4_ext_bridge + p4_succ_membership all sorry-free<br/><i>consumed by hashlifeResult_central_correct via p4_ext_bridge; audit N1 PR #5853 VACUOUS; design gate #3846 discharged</i>"]
    P5["P5 — Large-n jump  <b>⚠ research-level (P4 gate fallen → attackable)</b><br/>2 sorry · p5_large_n_jumpN [L1159] + hashlife_correct_margin [L145, INTRINSIC]<br/><i>p5_small_n_fallback + evolve_dead_of_cone_dead + p5_inductive_step (c.310 #5998) + p5_large_n_jump + hashlife_correctN all proven</i>"]
    GOAL["hashlife_correct  <b>proven (vacuous at large-n)</b> · p5_large_n_jumpN = live target"]

    BASE --> P1 --> P2 --> P3 --> GOAL
    P5S -.-> GOAL
    P4 -.->|"P4 closed"| P5 -.->|"BG-prover lock"| GOAL
```

### Methodological lessons

- **`List (Int × Int)` + `Bool` predicates + `native_decide`** is the encoding that passes for grids; the `Finset` encoding is blocked by `Quot.lift`/`Eq.rec`.
- **The "intractable" concept often hides a false statement**: the same intuition as for the Lattice breakthrough (7→0) applies — the certified counter-example `p4_unrestricted_counterexample` shows that an unrestricted statement form is false, pointing toward the correct `MacroCell.wf` hypothesis.
- **The sorry-free additive ingredients** (level/wf preservation, `box_assez_grand` arithmetic) accumulated behind the P4 lock and are **deployed** — the P4 inductive step is now proven post-split, and they feed `hashlifeResult_central_correct`. The same dynamic now applies behind the P5.2 large-`n` jump.

### Next steps

1. **BG-prover on P5.2**: attack `p5_large_n_jumpN` (large-`n` jump `evolveHashlifeFast n g = evolve n g` on `BoxAssezGrandN`) via the multi-agent harness (`agent_tests/prover/`), leaning on `hashlifeResult_central_correct` (P4 now closed) + `window_cheb_cone_in_domain`. With the P4 gate fallen, this is the live research-level target.
2. **INTRINSIC margin lock**: `hashlife_correct_margin` (`HashlifeMarginFragment.lean` L145) additionally requires the offset-matching chain `p4_nw_overlap_wall` (`Walls/NW.lean`) — separate research heart, bounded P4/P5 assembly via `supportInMargin`.
3. **Witness extension**: add additional HashlifeMemo patterns (community pillars) to strengthen the `native_decide` foundation.

## Notes

- Part of the GameTheory Lean series
- Companion notebook: `Lean-16b-Conway-Game-of-Life-Lean.ipynb`
- Cross-link: Epic #1647 Conway Phase 2 (Life-as-Computation)
- Cross-link: Epic #1651 Conway Phase 3 (Free Will Theorem)
- Cross-link: Epic #2162 Conway depth (HashlifeCorrectness P4/P5)

## Conway.Life Design

- **List(Int x Int) + Bool predicates + `native_decide`** = works reliably
- **Finset(Int x Int) + decide/native_decide** = BLOCKED (Quot.lift, Eq.rec)
- Pulsar (48 cells) and pentadecathlon (p15) are borderline but pass `native_decide`
- Hashlife: partial def (no termination proof) with recursive MacroCell decomposition
- `evolveHashlifeFast`: exponential speedup via `padCenter2` + `hashlifeResult`, validated by `native_decide`
- MacroCell round-trip verified by `#eval` and `native_decide` theorem
- HashlifeMemo: memoization layer for pillar witnesses, `9^k` worst case reduced to tractable

## References

Foundational sources for the results formalized across the three phases. Each entry maps to a module of this workspace.

- **Conway, J. H.** *On Numbers and Games* (ONAG). Academic Press, 1976; 2nd ed., A K Peters, 2001. — Conway's broader framework for combinatorial games (context for the games below).
- **Bouton, C. L.** "Nim, A Game with a Complete Mathematical Theory." *Annals of Mathematics*, 2nd ser., 3(1-4) (1901-1902): 35-39. — Foundational analysis of Nim (`Nim.lean`).
- **Conway, J. H.** "The Weird and Wonderful Chemistry of Audioactive Decay." *Eureka* 46 (1986): 5-16. — The Look-and-Say sequence (`LookAndSay.lean`).
- **Conway, J. H.** "FRACTRAN: A Simple Universal Programming Language for Arithmetic." In *Open Problems in Communication and Computation* (Cover & Gopinath, eds.), Springer, 1987. — FRACTRAN (`Fractran.lean`).
- **Conway, J. H.** "The Angel Problem." In *Games of No Chance*, MSRI Publications 29, Cambridge University Press, 1996. — The Angel vs Devil problem (`Angel.lean`).
- Conway's **Doomsday** algorithm for day-of-week computation — the calendar anchor method formalized in `Doomsday.lean`.
- The **Collatz** (3n+1) conjecture, Lothar Collatz (1937) — bounded instances handled via `native_decide` (`CollatzLike.lean`).
- **Gardner, M.** "The Fantastic Combinations of John Conway's New Solitaire Game 'Life'." *Scientific American* 223(4) (October 1970): 120-123. — First public presentation of the Game of Life (`Life.lean`).
- **Rokicki, T.** "An Algorithm for Compressing Space and Time." *Dr. Dobb's Journal* (2006). — The Hashlife algorithm (`Life/Hashlife.lean`).
- **Rendell, P.** "A Universal Turing Machine in Conway's Game of Life." In *Collision-Based Computing* (Adamatzky, ed.), Springer, 2002. — Life as universal computation (`Life/Computation.lean`).
- **Kochen, S.; Specker, E. P.** "The Problem of Hidden Variables in Quantum Mechanics." *Journal of Mathematics and Mechanics* 17(1) (1967): 59-81. — The original 117-vector theorem (`KochenSpecker.lean`).
- **Cabello, A.; Estebaranz, J. M.; Garcia-Alcaine, G.** "Bell-Kochen-Specker Theorem: A Proof with 18 Vectors." *Physics Letters A* 212 (1996). — The 18-vector tight proof formalized in `KochenSpecker.lean`.
- **Conway, J. H.; Kochen, S.** "The Free Will Theorem." *Foundations of Physics* 36(10) (2006): 1443-1473. — FWT from the SPIN, TWIN, and MIN axioms (`FreeWillTheorem.lean`).
- **Conway, J. H.; Kochen, S.** "The Strong Free Will Theorem." *Notices of the American Mathematical Society* 56(2) (2009): 226-232.
- **Peres, A.** "Two Simple Proofs of the Kochen-Specker Theorem." *Journal of Physics A* 24(4) (1991): L175-L178.
- **Mermin, N. D.** "Hidden Variables and the Two Theorems of John Bell." *Reviews of Modern Physics* 65(3) (1993): 803-815.
