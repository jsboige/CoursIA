# knot_lean — Knot Theory in Lean 4

Scaffolding for the formalization of knot theory results in Lean 4, with
strategic commented sorries (paper references + Mathlib prerequisites).

Epic #2874 (Phase 5 in progress). Toolchain `v4.31.0-rc1`.

## Sorry-state (verified 2026-07-06, re-confirmed 2026-07-12, 16 real — 14 + 2 from the PARTIAL backward transfer #3124, `num` proven)

Two counts, depending on the filter:

| File | real sorries | sorry (prose, CI) |
|------|-------------|-------------------|
| `Knots/Basic.lean` | 0 | 1 |
| `Knots/Reidemeister.lean` | 1 | 2 |
| `Knots/Invariant.lean` | 5 | 6 |
| `Knots/Conway.lean` | 8 | 11 |
| `Knots/Lidman.lean` | 2 | 4 |
| `Knots/MathlibPrerequisites.lean` | 0 | 2 |
| **Total** | **16** | **26** |

- **real sorries** (`exact sorry`, `:= sorry`, `:= by sorry`) = what's actually
  missing as a proof. **16** total — 14 stable + **2 from the PARTIAL backward
  transfer `tricolorable_backward` (#3124)**: sub-goals `fox`/`col` left in
  sorry after decomposition (`num` PROVEN by `wf` parity, cf. § Phase 5;
  core `hcolPres` proven). A Lidman scaffolding sorry (diagram L39) was
  eliminated by **#4899** (PD-code 11n102 from KnotInfo, MERGED 2026-07-02):
  Lidman goes from 3 to 2 real sorries.
- **`Reidemeister.lean` at 1 real sorry** (recounted firsthand 2026-07-06:
  stable at 1 since June — single `exact sorry` at L549; the previous
  version of the README overcounted at 2).
- **prose sorries** (any line containing `sorry`, CI filter `prose-header`) =
  **26** currently. The CI `lean-knot.yml` gate is set to
  `sorry-baseline: "28"` (prose-header mode): margin of 2 after #3163
  (`num`) and #4899 (Lidman), the baseline having not yet been tightened.
  This count includes occurrences in diagnostic comments (e.g. the comment
  on `KnotDiagram.wf` in `Basic.lean`).

The CI `.github/workflows/lean-knot.yml` gate is on the **prose-header
baseline 28** (history: bump 25→28 in #3124 for the backward transfer
decomposition, lowered to 27 after the `num` proof #3163, then re-bumped
to 28 by the GF(3) follow-up #3003): any PR adding a real sorry raises
both counts and fails CI, unless justified in the PR body.

## Results by real status (verified against the code)

### Proven (axioms `[propext, Quot.sound]` only, no `sorryAx`)

- [x] `trefoil_tricolorable` — the trefoil is 3-colorable (`Invariant.lean`)
- [x] `unknot_not_tricolorable` — the unknot is NOT 3-colorable
  (`Invariant.lean`)
- [x] `trefoil_crossing_number` — trefoil crossing number = 3
  (`Invariant.lean`, under the provisional definition
  `crossingNumberOfDiagram`)
- [x] `Reidemeister1.symm` / `Reidemeister2.symm` / `Reidemeister3.symm`,
  `reidemeister_equiv_symm`, `reidemeister_equiv_equivalence` — symmetry of
  the moves and reflexive-transitive closure (`Reidemeister.lean`)
- [x] `tricolorable_invariant_fails_under_pr1_model` — **certified
  counter-example** refuting `tricolorable_invariant` under the PR1 model
  (diagnostic, cf. § Phase 5)
- [x] `trefoil_wf`, `unknot_wf`, `figureEight_wf` — the 3 named diagrams
  satisfy the PD parity of `KnotDiagram.wf`
- [x] `Reidemeister1Connected.tricolorable_forward` (#3000, MERGED) —
  **forward** transfer of 3-colorability d₁→d₂ under the connected R1
  model (`Invariant.lean` L478, complete proof without sorry via
  `hcolF1` / `hcolF2b` / `hcolF2c`)
- [~] `Reidemeister1Connected.tricolorable_backward` (#3124, MERGED,
  **PARTIAL**) — **backward** transfer d₂→d₁: `hcolPres` (color
  preservation on preserved labels, constructive core) **PROVEN**;
  `num` PROVEN #3163 (by `wf` parity); `fox` #3154 + `col` #3168
  partially proven (one sub-case each closed); **2 residuals §9.1**
  remain in sorry (modified crossing `Y` + all-distinct kink)

### Scaffolding (sorry, formal target)

- [ ] `tricolorable_invariant` — 3-colorability is invariant under
  Reidemeister (under **Path B** the model IS classical Fox: statement
  healthy and non-trivial — will distinguish trefoil/unknot/figure-8
  once closed. GATED on the 2 residuals §9.1 of the backward transfer,
  cf. § Path B / § Phase 5)
- [ ] `trefoil_not_unknot` — corollary: the trefoil is not the unknot
  (depends on `tricolorable_invariant`)
- [ ] `unknottingNumber` — definition + computation (requires
  minimization over equivalence classes, Phase 4+)
- [ ] Conway (11n34): `conway_not_smoothly_slice` (Piccirillo 2018/
  Annals 2020), `conway_topologically_slice` (Freedman 1982), mutation
  Kinoshita-Terasaka — 8 sorries, permanent scaffolding
- [ ] Lidman 11n102: unknotting number = 2 (Heegaard-Floer) — 2 sorries,
  scaffolding (the L39 diagram sorry was eliminated by #4899, PD-code
  11n102 from KnotInfo)
- [ ] `reidemeister_theorem` — Reidemeister equivalence ↔ ambient isotopy
  (PL topology of 3-manifolds, beyond current Mathlib scope) — 2
  sorries, permanent

### Verdict by sorry (G.1 audit, 2026-06-23)

Re-verification firsthand against the code (`Reidemeister.lean` +
`Invariant.lean`), per real sorry of the 5 open sheets of
`Invariant.lean`. Classify each sheet into **PROVEABLE** / **REFUTED** /
**RESEARCH-HOLD** / **INFRASTRUCTURE** — the real formal state, coupled
to the proofs:

| Line | Theorem | Verdict | Unblocker |
|------|---------|---------|-----------|
| L238 | `tricolorable_invariant` | **OPEN (`sorry`)** | No longer refuted after the Stage 2 rewire (#3999): `ReidemeisterStep.r1` is rewired toward the symmetric closure of the geometrically connected move `Reidemeister1Connected`. The free-ρ counter-example `tricolorable_invariant_fails_under_pr1_model` (L342, witness `(d₁={⟨1,2,1,2⟩,2}, d₂={⟨1,2,1,2⟩,⟨3,4,3,4⟩,4})`) lives on the RAW move `Reidemeister1` and is no longer `ReidemeisterEquiv`-reachable (`pr1_counterexample_excluded_under_connected` L508). Coord decision (C) **executed** (trio #3997/#3999/#4003 merged). Still OPEN on the FORWARD transfer across a connected R1 curl (the 2 fresh edges inherit `color a`). |
| L944 | `trefoil_not_unknot` | **OPEN (`sorry`)** | No longer "refuted by proxy". The natural route (`tricolorable_invariant` + `trefoil_tricolorable` + `unknot_not_tricolorable`) is gated on the forward transfer of L238. The two component pieces are proven under the true Fox condition (Path B) — lands as soon as L238 lands. |
| L1006 | `Knot.unknottingNumber` | **INFRASTRUCTURE (NP-hard)** | Minimization over equivalence classes; gated on a non-trivial `ReidemeisterEquiv` (fork L238). Permanent scaffolding. |
| L1581 | `fox` all-distinct §9.1 | **OPEN (`sorry`)** | Fox inheritance of the modified crossing `Y'` under all-distinct kink. #3003 (Path B, arc-equality constraint) **SHIPPED**; the residual is the genuinely hard **classical backward transfer** (BG-prover ai-01, original research target #2874). Sub-case **all-equal PROVEN** in the body of `tricolorable_backward` (L1373). |
| L1731 | `col` all-distinct §9.1 | **OPEN (`sorry`)** | Lift ≥ 2 colors: the naïve restriction `col₁` can be **monochrome** if all the chromatic variation of `col₂` lives on the fresh edges `{n+1, n+2}` (pathology of the disjoint kink). #3003 (Path B) **SHIPPED**; residual = classical backward transfer (BG-prover #2874). Sub-case **all-equal PROVEN** (by contradiction via `h2col₂`, in `tricolorable_backward` L1373). |

**Conclusion of the audit (post-trio #3997/#3999/#4003, post-Path B #3003).**
`tricolorable_invariant` (L238) and `trefoil_not_unknot` (L944) are
**no longer refuted** — the connected rewire excluded the free-ρ
witness, they are OPEN on the FORWARD transfer. The two residuals §9.1
(L1581 fox / L1731 col) remain the **irreducible research-level core**:
all-distinct classical backward transfer (BG-prover ai-01, target
#2874), the arc-equality #3003 having been shipped. The `Knot.unknottingNumber`
(L1006) = NP-hard infrastructure. The R1 backward transfer is on the
other hand **complete on its all-equal sub-case** (`fox`+`col` PROVEN)
and on `num` (by `wf` parity, #3163) — only the all-distinct modes of
the kink remain open.

## Path B: classical Fox model restored (2026-06-23, #3003)

**Decision: Path B implemented.** The 3-colorability model previously
colored EDGES (`Fin numEdges`) independently, without arc-equality
constraint — classical Fox forces the over-strand of a crossing to share
a color (continuity on the arc). This permissive model diverged from
classical Fox: it admitted parasitic tricolorations (notably the
**figure-8**, classically NOT 3-colorable, witness `(0,0,0,1,0,0,1,2)`)
and made a "universal lemma" of colorability TRUE for the model but
FALSE classically — which would have made `tricolorable_invariant`
trivial (distinguishing only the unknot).

**Path B (mandated 2026-06-23).** `triColorConditionAt` (`Invariant.lean`)
now carries the conjunction of **arc-equality** `c₂ = c₄` (both ends of
the over-strand of a crossing carry the same color), in addition to the
Fox rule (all equal OR all distinct) on the three meeting strands. This
IS the classical Fox invariant (Fox 1962): a constant coloring on arcs,
with the all-equal-or-all-distinct rule at each crossing.

- **Non-regression verified**: `trefoil_tricolorable` re-proven with the
  arc-respecting witness `(0,1,1,2,2,0)` (`decide`); the **figure-8** is
  now correctly REJECTED (its former permissive witness no longer
  validates the arc conjunction).
- **GF(3) cross-linearity** (`triColorFoxCondition_iff_sum_mod_three`,
  `Invariant.lean`, cycle-6): the Fox condition at a crossing is
  equivalent to `toNat(c₁)+toNat(c₂)+toNat(c₃) ≡ 0 (mod 3)` — a
  per-crossing computational fact, arc-independent. Kept as scaffolding.
  NB: this does NOT lift into a universal lemma of colorability (cf.
  next point).
- **Universal lemma WITHDRAWN** (`tricolorability_of_two_crossings`):
  it is FALSE under Path B — the figure-8 is well-formed with 4
  crossings and is NOT Fox-tricolorable. The rank-nullity shortcut is
  therefore unavailable; the "Withdrawn" section of `Invariant.lean`
  documents the withdrawal and the counter-example.

**Consequence for `tricolorable_invariant`.** Under Path B, the
invariant is no longer trivial: once the 2 §9.1 residual sub-goals of
the backward transfer are closed, the forward + backward composition
gives an R1 bi-implication under the connected model, and the invariant
GENUINELY distinguishes the trefoil (tricolorable) from the unknot
(not) and the figure-8 (not) — instead of isolating only the unknot.
The 2 §9.1 residuals remain open (Fox inheritance of the modified
crossing under all-distinct kink); this is the GENUINELY hard classical
transfer, as anticipated by the fork above (Path B chosen, Path A
discarded).

## Phase 5 — Re-modeling the Reidemeister moves

**Marquee theorem**: `tricolorable_invariant` (3-colorability is an
invariant). Resists since several cycles. The key lesson (pattern
"intractable = false statement", cf. `conway_lean` P4 /
`feedback-lean-false-statement-counterexample`): before proving,
verify that the statement is *true* under the current model.

**History (certified, by proven counter-examples):**

1. **Phase 3 model** (existential symmetric `∃ c, surgery`) — refuted
   by `tricolorable_invariant_fails_under_current_model` (#2915):
   malformed witness `⟨7,8,9,10⟩` (labels outside `[1, numEdges]`).
2. **PR1 (#2929)** — re-modeling: `KnotDiagram.wf` (PD parity, Bool) on
   both diagrams + edge renaming `ρ : Fin(min) ↪ Fin(max)`
   swap-invariant. Excludes the malformed witness. **BUT** refuted again
   by `tricolorable_invariant_fails_under_pr1_model` (#2938): `wf`
   forces an R1 twist to use only the 2 fresh edges, and `ρ` is a free
   injection not bound to the labels of the new crossing `c` → the
   twist can CREATE 3-colorability ex nihilo (witness
   `d₁={[⟨1,2,1,2⟩],2}` non-tricolorable ↔
   `d₂={[⟨1,2,1,2⟩,⟨3,4,3,4⟩],4}` tricolorable, connected by an R1
   twist).
3. PR1.5 (#2956, MERGED) — ρ-determined. Strengthen the move
   constructors so that `ρ` *DETERMINES* the labels of `c`: an R1 curl
   on arc `a` attaches the new crossing `⟨a, a, n+1, n+2⟩`. PR1.5b
   (#2966, MERGED) delivered the exclusion proof
   `pr1_counterexample_excluded_under_rho_determined` (gate 1: the
   re-model excludes the #2938 witness, proven).

**Structural flaw discovered (2026-06-14, G.1).** The append+`wf` model
is *too weak*: a parity argument (airtight, + 3 empirical probes) shows
that ANY append surgery `d₂ = d₁ ++ [c]` with `d₁.wf ∧ d₂.wf` forces
`c` to reference only the fresh labels `{n+1, n+2}` (otherwise a label
of `d₁` would exceed 2×) → `c = ⟨n+1,n+1,n+2,n+2⟩` = a **disjoint
kink** (a separate unknot component, 0 edge shared with `d₁`).
Consequences:

1. `Reidemeister1` (free-ρ, #2929) admits ONLY disjoint kinks — NO
   connected R1 representable. The #2938 witness is precisely a
   disjoint kink.
2. `Reidemeister1'` (#2956) forces `c = ⟨a,a,n+1,n+2⟩` → arc `a`
   appears 4× → **`d₂.wf` unsatisfiable → the def is VACUOUS**. The
   exclusion proof #2966 is trivially true (the premise is never
   satisfied).
3. R2: same (2-crossings disjoint components). Only **R3** (preserves
   `numEdges`, relabels a crossing) is connected under this model.
4. `ReidemeisterEquiv` ≈ refl + disjoint R1/R2 kinks + connected R3.
   Too weak to untie a trefoil. `tricolorable_invariant` is FALSE (a
   disjoint kink changes 3-colorability = #2938).

**Option C — connected fix, PR1.5c (#2980, MERGED 2026-06-14).** The
correct connected surgery is NON-append: modify an endpoint crossing
`Y` of the arc `a` (rename one slot `a`→`b = n+1`) AND append
`C = ⟨a, b, c, c⟩` with `c = n+2` (kink monogon, appears 2× in `C`
only). Parity preserved: `a` = X+C (2×), `b` = Y+C (2×), `c` = C+C
(2×). `def Reidemeister1Connected` (`Reidemeister.lean`) implements
this surgery; `reidemeister1Connected_satisfiable` proves a concrete
witness `wf = true` on both sides
(`d₁={[⟨1,2,3,4⟩,⟨1,2,3,4⟩],4}` →
`d₂={[⟨1,2,3,4⟩,⟨5,2,3,4⟩,⟨1,5,6,6⟩],6}`). **ADDITIVE**: does not
modify the merged moves (#2929/#2956 coexist). Option C **MERGED**
(#2980): feasibility proven (non-empty witness, `wf = true` on both
sides).

**R3 connected — PR1.5d (#3088, MERGED 2026-06-15).** R3 is the only
connected move under the append+wf model (point 3 above). Formalized
additively as `Reidemeister3Determined` (`Reidemeister.lean`): an R3
slide where the relabeled crossing `c` is constrained by slot-permutation
of the original (`c.isSlotPermOf` = decidable `List.Perm` on `Nat`),
4 strands preserved and `wf`. `.implies_reidemeister3` refines into
`Reidemeister3` (embedding); `reidemeister3Determined_satisfiable`
proves a non-empty witness (`⟨1,2,3,4⟩`→`⟨1,3,2,4⟩`, swap e2/e3).
0 sorry added (pure scaffolding, R1/R2/R3 merged unchanged).

**Transfer lemma R1 connected — forward #3000 PROVEN + backward #3124 PARTIAL (MERGED).**
The **forward** transfer `tricolorable_forward` (#3000) is **proven**:
under the connected R1 model (Option C, `Reidemeister1Connected`), a
tricoloration of `d₁` propagates to `d₂`. The **backward** transfer
`tricolorable_backward` (#3124) is **partial**: `hcolPres` (color
preservation on preserved labels `l ∈ [1, n]`, pure arithmetic
`(l-1) % numEdges` closed by `rfl`) is proven — this is the constructive
core on which the Fox inheritance of unchanged crossings rests.
**Two §9.1 sub-goals remain in `sorry`** after decomposition (user
instruction 2026-06-15: "decompose, prove the tractable, deliver with
sub-sorry residuals on which ai-01 will advise"). On the 3 sub-goals
initially open (`fox`/`num`/`col`), `num` is **proven** and
`fox`/`col` are **partially proven** (one sub-case each closed):

1. `num` — **PROVEN (#3163)**. `d₁.numEdges ≥ 2` by `wf` parity:
   `_hproper` provides a crossing distinct `j ≠ i` ⟹
   `crossings.length ≥ 2` ⟹ `edges.length = 4 × length ≥ 8` ⟹ by
   contradiction (`numEdges = 1`) clauses (a)+(b) of `wf` force all
   edges to `1` (count `count 1 = length ≥ 8`), contradicting clause
   (b) `count 1 = 2`.
2. `fox` — **partially proven (#3154)**: the **unchanged** crossings
   inherit via `hcolPres` (mirror of the forward `h_inherit`).
   **Residual §9.1**: the **modified crossing `Y`** (replaced by `Y'`
   in `d₂`) requires the construction of color symmetry under `col₁`
   (research-level, §9.4–§9.6, `Invariant.lean` L1210).
3. `col` — **partially proven (#3168)**: the **all-equal** kink mode
   is closed (the 2 distinct colors of `col₂` embed into
   `Fin d₁.numEdges`). **Residual §9.1**: the **all-distinct** kink
   mode carries a fresh color outside the range of `d₁`, the naïve
   restriction `col₁` can be monochrome — the lift `≥ 2` colors
   requires the color-symmetry / proper-arc construction (#3003,
   `Invariant.lean` L1354).

These **2 §9.1 residuals** sit under the **CI baseline 28** (history:
bump 25→28 in #3124, lowered to 27 after the `num` proof #3163,
re-bumped to 28 by the GF(3) follow-up #3003); the current real count
is **26** after #4899 (margin of 2).

The marquee `tricolorable_invariant` remains gated on the **completion
of the 2 §9.1 backward residuals** (then forward + backward composition
= connected R1 bi-implication). The complete **R2/R3 transfer**
(non-trivial wf-satisfiability + RTC lift) remains research-level
multi-PR. Strategic decision (C) deep connected surgery vs (X) accept
#2938 and reframe, open.

Reference: Fox (1962), *A quick trip through knot theory*; Adams,
*The Knot Book*.

## Structure

| File | Contents | real sorries |
|------|----------|-------------|
| `Knots/Basic.lean` | Definitions (Knot, Link, PD-code, named knots), `KnotDiagram.wf` | 0 |
| `Knots/Reidemeister.lean` | R1/R2/R3 moves (Phase 5 model), `ReidemeisterEquiv`, symmetries | 1 |
| `Knots/Invariant.lean` | 3-colorability (Fox), crossing number, unknotting number, PR1 counter-example, R1 forward transfer (#3000) + backward PARTIAL (#3124) | 5 |
| `Knots/Conway.lean` | Conway knot (11n34), Piccirillo, smooth/topological dichotomy | 8 |
| `Knots/Lidman.lean` | 11n102, unknotting number = 2 | 2 |
| `Knots/MathlibPrerequisites.lean` | Index of missing Mathlib prerequisites by tier | 0 |

## External dependencies

| Repository | Role | Status |
|------------|------|--------|
| [shua/leanknot](https://github.com/shua/leanknot) (branch `lean4`) | Bricks/walls, tangles, braids | Candidate Lake dependency (toolchain alignment in progress) |
| [vihdzp/combinatorial-games](https://github.com/vihdzp/combinatorial-games) | Conway surreal numbers, nimbers | Already in `conway_cgt_lean/` |
| [prathamesh-t/Tangle-Isabelle](https://github.com/prathamesh-t/Tangle-Isabelle) | Tangles in Isabelle/HOL | Design reference |
| [Mathlib](https://github.com/leanprover-community/mathlib4) | Polynomials, categories, partial topology | Lake dependency |

## Pedagogical notebook

`Lean-17-Knots-a-Conway-and-Proofs.ipynb` (in `SymbolicAI/Lean/`):
- Python visualizations of knots (trefoil, Conway, Kinoshita-Terasaka)
- History of the Piccirillo proof (PhD student, 1 week, 50 years of waiting)
- Lidman's result as a "short but deep proof" case study
- Perspective on Lean formalization (why it's far, what's missing)

## References

- **Piccirillo (2018/2020)**: *The Conway knot is not slice*, Annals of Mathematics 191(2). [arXiv:1808.02923](https://arxiv.org/abs/1808.02923)
- **Lidman (2026)**: *The unknotting number of 11n102 is 2*. [arXiv:2606.12431](https://arxiv.org/abs/2606.12431)
- **Reidemeister (1927)**: *Elementare Begründung der Knotentheorie*
- **Fox (1962)**: *A quick trip through knot theory*
- **Adams**: *The Knot Book* (PD-code conventions for R1 curls)
- **Conway (1970)**: *An enumeration of knots and links*
- **Freedman (1982)**: *The topology of four-dimensional manifolds*, J. Differential Geom.
- **Doll & Hoste (1991)**: *A tabulation of oriented links* (PD-code parity)
- **Prathamesh (2015)**: *Formalising Knot Theory in Isabelle/HOL*, LNCS 9250
- **Lean AI Leaderboard**: [Conway knot not smoothly slice](https://lean-lang.org/eval/problems/conway_knot_not_smoothly_slice/)

## See also

- **Epic #2874** — This Epic (Phase 5)
- **#1647** Conway Phase 2 (combinatorial games, GoL)
- **#1646** Grothendieck Phase 1
- **`conway_cgt_lean/`** — Tour of `vihdzp/combinatorial-games` results
- **`social_choice_lean/`** — Scaffolding pattern with resolved sorries (Arrow, Sen)
- **`conway_lean/`** — Conway's Game of Life in Lean (cf. `MacroCell.wf`, pattern
  of the Phase 5 `KnotDiagram.wf` re-modeling)

## Conclusion

`knot_lean` formalizes in Lean 4 classical and modern results of knot
theory — Fox 3-colorability, crossing number, Conway knot (11n34),
Lidman 11n102 — on the minimal axiomatic `[propext, Quot.sound]` (no
`sorryAx`). Epic #2874 (Phase 5) is at the 3-colorability invariant
transfer under the connected model of Reidemeister moves.

### What is acquired

The **local invariants** are solid: trefoil 3-colorability and unknot
non-colorability, trefoil crossing number, symmetries and
reflexive-transitive closure of the moves, and the parity
well-formedness `KnotDiagram.wf` of named diagrams. The **forward
transfer** of 3-colorability under connected R1 (`#3000`) is **proven**
without sorry, and the **backward transfer** (`#3124`) is **partially**
established: the constructive core `hcolPres` and the sub-goal `num`
(by `wf` parity, `#3163`) are closed, as well as one sub-case each of
`fox` (`#3154`) and `col` (`#3168`).

### The lock

The marquee `tricolorable_invariant` remains **gated** on two
§9.1 residual sub-goals of the backward: the symmetry of colors on the
modified crossing `Y` (`fox`) and the all-distinct lift outside the
source diagram range (`col`). Their completion would compose forward +
backward into a connected R1 bi-implication (**16 real sorries** in
total). The "distant" results — Conway non-slice (Piccirillo), Lidman's
unknotting number, Reidemeister theorem ↔ ambient isotopy — remain
**permanent scaffolding**: they exceed the current scope of Mathlib
(PL topology of 3-manifolds, Heegaard-Floer).

### Methodological lessons

The Phase 5 trajectory illustrates the pattern "*intractable* = false
statement" (cf. `conway_lean` P4): before proving, **verify by
certified counter-example** that the statement is true under the
current model. Three successive re-modelings (Phase 3 → PR1 `wf`+ρ →
PR1.5 ρ-determined) were each **refuted by a proven witness** (`#2915`,
`#2938`) before the parity analysis (2026-06-14) revealed that the
append+`wf` model is *structurally too weak* (it admits only disjoint
kinks). The **connected surgery** (Option C, `#2980`; R3 determined,
`#3088`) corrects this flaw. Finally, the **backward decomposition**
(`#3124`) — proving the tractable, delivering with documented residual
sub-sorries — isolated precisely the two research-level constructions
that remain.

### Next steps

1. Close the **2 §9.1 residuals** (`fox`, `col`) → connected R1
   bi-implication.
2. Complete **R2/R3 transfer** (non-trivial wf-satisfiability + RTC
   lift) — research-level multi-PR.
3. Open strategic decision: **(C)** push the deep connected surgery,
   or **(X)** accept `#2938` and reframe the invariant.
4. Distant scaffolding: wait for the evolution of Mathlib (3-manifolds,
   Heegaard-Floer) for Conway and Lidman.
