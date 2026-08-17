# knot_lean — Knot Theory in Lean 4

Scaffolding for the formalization of knot theory results in Lean 4, with
strategic commented sorries (paper references + Mathlib prerequisites).

Epic #2874 (Phase 5 in progress). Toolchain `v4.32.0`.

## Sorry-state (verified 2026-08-17 against `origin/main`, **14 real**)

Two counts, depending on the filter:

| File | real sorries | sorry (prose, CI) |
|------|-------------|-------------------|
| `Knots/Basic.lean` | 0 | 3 |
| `Knots/Reidemeister.lean` | 2 | 2 |
| `Knots/Invariant.lean` | **2** | 15 |
| `Knots/Conway.lean` | 8 | 11 |
| `Knots/Lidman.lean` | 2 | 4 |
| `Knots/MathlibPrerequisites.lean` | 0 | 2 |
| **Total** | **14** | **37** |

- **real sorries** (`exact sorry`, `:= sorry`, `:= by sorry`) = what's actually
  missing as a proof. **14** total, all stable: 2 in `Invariant.lean`
  (`tricolorable_invariant` L350 + `Knot.unknottingNumber` L2143), 2
  `reidemeister_theorem` (PL topology), 8 Conway, 2 Lidman. The **2 §9.1
  backward-transfer residuals `fox`/`col` were DISCHARGED by #11227**: the
  kink all-distinct mode is **vacuous** — the R1 kink `C = ⟨a,b,c,c⟩` has
  `e₃ = e₄ = c`, and the Path B over-strand continuity `c₂ = c₄` forces
  `col₂(b) = col₂(c) = col₃`, contradicting the Fox all-distinct requirement
  `c₂ ≠ c₃` → `absurd` closes both residuals in one line each. The
  **R1-connected bi-implication is COMPLETE** (forward #3000 + backward
  #3124/#11227).
- **Historic decrease 17 → 16 → 14**: #8766 discharged `trefoil_not_unknot`
  (composition), #9966 raised back to 17 (the `tricolorable_forward_r1`
  wrapper wall), the wall was then discharged (16), and #11227 closed
  fox/col (14). #11276 added, sorry-free, the **PROVEN**
  `tricolorable_forward_r2_up` transfer plus the named walls
  `r2_append_only_wall` (L1151) and `r3_determined_wall` (L1293) that bound
  the master iff.
- **`Reidemeister.lean` at 2 real sorries** (recounted firsthand 2026-07-15
  with the CI real-mode awk: `sorry -- ambient_isotopic k₁ k₂` at L554 *and*
  `exact sorry` at L558; the word-bounded `\bsorry\b` count includes the
  line where only the `-- ...` suffix is stripped, so the bare `sorry` at
  L554 still counts as a real-mode sorry. The previous README recount
  (2026-07-06) predated the CI prose-header→real switch of 2026-07-11 and
  undercounted by 1).
- **prose sorries** (any line containing `sorry`) = **37** currently (the
  R2/R3 wall documentation prose added mentions). The CI `lean-knot.yml`
  switched to **`real` mode** (`sorry-baseline: "14"`) — the real mode
  strips `--` line comments and `/- -/` block comments, then counts the
  word-bounded `\bsorry\b` — it is now the sole official CI mode for
  knot_lean. The 37 count is preserved as a raw/any-line indicator. This
  count includes occurrences in diagnostic comments (e.g. the comment on
  `KnotDiagram.wf` in `Basic.lean`).

The CI `.github/workflows/lean-knot.yml` gate is on the **real-mode baseline
14** (history: prose-header 25→28 in #3124 for
the backward transfer decomposition, lowered to 27 after the `num` proof
#3163, re-bumped to 28 by the GF(3) follow-up #3003; then prose-header→real
switch to baseline 17 on 2026-07-11 when the raw count diverged from the
real count; 16 after #8766, re-17 by #9966, 16 at the wall discharge, 14
after #11227): any PR adding a real sorry raises the real count and fails
CI, unless justified in the PR body.

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
- [x] `Reidemeister1Connected.tricolorable_backward` (#3124, MERGED,
  then **COMPLETED by #11227**) — **backward** transfer d₂→d₁
  **COMPLETE**: `hcolPres` (color preservation on preserved labels,
  constructive core) + `num` (#3163, `wf` parity) + the **2 §9.1
  residuals `fox`/`col` DISCHARGED by #11227** — the all-distinct kink
  mode is vacuous (over-strand continuity `c₂ = c₄` of the kink
  `⟨a,b,c,c⟩` forces `col₂(b) = col₂(c) = col₃`, contradicting Fox
  all-distinct; `absurd` closes each in one line). With #3000, the
  **R1-connected bi-implication is PROVEN**.
- [x] `trefoil_not_unknot` (#8766, MERGED) — corollary: the trefoil is
  not the unknot, **PROVEN** by composition of `tricolorable_invariant`
  (sorry-bearing) + `trefoil_tricolorable` + `unknot_not_tricolorable` —
  no independent sorry of its own.
- [x] `tricolorable_forward_r2_up` (#11276, MERGED) — **forward**
  transfer of 3-colorability across the **append-only** R2 (current
  model): **PROVEN sorry-free**. The same PR delivers the **named walls**
  `r2_append_only_wall` (L1151: the FREE R2 model is append-only with a
  floating bigon — the descending arm of the master iff is FALSE under
  this model, formal witness) and `r3_determined_wall` (L1293), which
  **bound the master iff**: any remaining proof of
  `tricolorable_invariant` must go through a connected R2/R3
  re-modelling (track on #2874).

### Scaffolding (sorry, formal target)

- [ ] `tricolorable_invariant` — 3-colorability is invariant under
  Reidemeister (under **Path B** the model IS classical Fox: statement
  healthy and non-trivial — will distinguish trefoil/unknot/figure-8
  once closed. GATED on the connected R2/R3 re-modelling — the R1 leg is
  fully proven, and `r2_append_only_wall` shows the iff is FALSE under
  the current free append-only R2; see #2874)
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

### Verdict by sorry (G.1 audit, updated 2026-08-17)

Re-verification firsthand against the code (`Reidemeister.lean` +
`Invariant.lean`), per real sorry of the 2 open sheets of
`Invariant.lean` (down from 5: #8766 discharged `trefoil_not_unknot`,
#11227 discharged the `fox`/`col` §9.1 residuals). Classify each sheet
into **PROVEABLE** / **REFUTED** / **RESEARCH-HOLD** / **INFRASTRUCTURE**
— the real formal state, coupled to the proofs:

| Line | Theorem | Verdict | Unblocker |
|------|---------|---------|-----------|
| L341-350 | `tricolorable_invariant` | **OPEN (`sorry`)** | The R1 leg is closed on both sides (#3000 + #3124/#11227). The named wall `r2_append_only_wall` (#11276, L1151) shows the iff is FALSE under the FREE append-only R2 model: the free `ReidemeisterStep.r2` constructor relates `emptyDiagram` (not tricolorable) to `twoTwinCrossings` (tricolorable) — closure requires the **connected R2/R3 re-modelling** (`ReidemeisterEquivConnected` proposal on #2874; exhaustive validation R2 #11467, `Reidemeister2Connected` statement #11469, transfer #11477, R3 validation #11486 — in review). |
| L2143 | `Knot.unknottingNumber` | **INFRASTRUCTURE (NP-hard)** | Minimization over equivalence classes; gated on a non-trivial `ReidemeisterEquiv` re-statement. Permanent scaffolding. |
| L1581 | `fox` all-distinct §9.1 | **PROVEN (#11227)** | The all-distinct kink mode is **vacuous**: the R1 kink `C = ⟨a,b,c,c⟩` has `e₃ = e₄ = c`, the Path B over-strand continuity `c₂ = c₄` forces `col₂(b) = col₂(c) = col₃`, contradicting Fox all-distinct `c₂ ≠ c₃` → `absurd` closes the residual. The connected R1 backward is COMPLETE. |
| L1731 | `col` all-distinct §9.1 | **PROVEN (#11227)** | Same vacuity argument (one line). The anticipated colour-symmetry / proper-arc construction (#3003) is no longer needed — the case never occurs under Path B. |

**Conclusion of the audit (post-#11227, post-#11276).**
The **R1-connected bi-implication is PROVEN** (forward #3000 + backward
#3124 completed by #11227). `tricolorable_invariant` (L341) remains the
**only** OPEN sorry of `Invariant.lean` on the invariant side (with
`Knot.unknottingNumber`, NP-hard infrastructure, L2143). The forward
R2-up is PROVEN (#11276) and the named walls
`r2_append_only_wall`/`r3_determined_wall` **bound the master iff under
the current model**: the descending arm is FALSE under the FREE
append-only R2 (the floating bigon manufactures counter-examples), so
any closure of the marquee goes through the **connected R2/R3
re-modelling** proposed on #2874 (active track: exhaustive validation R2
#11467 / `Reidemeister2Connected` statement #11469 / transfer #11477 /
R3 validation #11486, in review). `trefoil_not_unknot` remains PROVEN by
composition (#8766).

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

**Transfer lemma R1 connected — forward #3000 + backward #3124, COMPLETE (the 2 residuals closed by #11227).**
The **forward** transfer `tricolorable_forward` (#3000) is **proven**:
under the connected R1 model (Option C, `Reidemeister1Connected`), a
tricoloration of `d₁` propagates to `d₂`. The **backward** transfer
`tricolorable_backward` (#3124) is now **complete**: `hcolPres` (color
preservation on preserved labels `l ∈ [1, n]`, pure arithmetic
`(l-1) % numEdges` closed by `rfl`) is proven, and the **2 §9.1
sub-goals** delivered as residual sorries (user instruction 2026-06-15:
"decompose, prove the tractable, deliver with sub-sorry residuals")
have been **discharged by #11227**:

1. `num` — **PROVEN (#3163)**. `d₁.numEdges ≥ 2` by `wf` parity:
   `_hproper` provides a crossing distinct `j ≠ i` ⟹
   `crossings.length ≥ 2` ⟹ `edges.length = 4 × length ≥ 8` ⟹ by
   contradiction (`numEdges = 1`) clauses (a)+(b) of `wf` force all
   edges to `1` (count `count 1 = length ≥ 8`), contradicting clause
   (b) `count 1 = 2`.
2. `fox` — closed in two steps: unchanged crossings inherit via
   `hcolPres` (#3154), then the residual on the modified crossing `Y`
   **discharged by #11227** — the all-distinct kink mode is
   **vacuous** (over-strand continuity `c₂ = c₄` of the kink
   `C = ⟨a,b,c,c⟩` forces `col₂(b) = col₂(c) = col₃`, contradicting
   Fox all-distinct; `absurd` in one line).
3. `col` — closed in two steps: all-equal kink mode (#3168), then the
   all-distinct mode **discharged by #11227** via the same vacuity
   argument — the anticipated color-symmetry / proper-arc construction
   (#3003) is no longer needed: the case never occurs under Path B.

**Consequence: connected R1 bi-implication PROVEN** (forward +
backward composed). The CI baseline moved from 17 to **14** (real-mode;
prose-header history: bump 25→28 in #3124, lowered to 27 after the
`num` proof #3163, re-bumped to 28 by #3003; real-mode switch on
2026-07-11).

**The R2 wall and the forward R2-up (#11276).** The same cycle
delivered, without any sorry: `tricolorable_forward_r2_up` (forward
transfer across the current model's append-only R2, PROVEN), and the
**named walls** `r2_append_only_wall` (L1151: the FREE R2 model is
append-only with a floating bigon — the descending arm of the master
iff is FALSE under this model) and `r3_determined_wall` (L1293).
These walls **bound the master iff**: the marquee
`tricolorable_invariant` CANNOT be closed under the free append-only
R2 model — its closure goes through connected R2/R3 re-modelling
(`Reidemeister2Connected`/`Reidemeister3Connected`, statement and
exhaustive-validation plan on #2874).

Reference: Fox (1962), *A quick trip through knot theory*; Adams,
*The Knot Book*.

## Structure

| File | Contents | real sorries |
|------|----------|-------------|
| `Knots/Basic.lean` | Definitions (Knot, Link, PD-code, named knots), `KnotDiagram.wf` | 0 |
| `Knots/Reidemeister.lean` | R1/R2/R3 moves (Phase 5 model), `ReidemeisterEquiv`, symmetries | 2 |
| `Knots/Invariant.lean` | 3-colorability (Fox), crossing number, unknotting number, PR1 counter-example, connected R1 bi-implication (#3000 + #3124/#11227), R2-up transfer + named walls (#11276) | 2 |
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
- **`game_theory_lean/SocialChoice/`** — Scaffolding pattern with resolved sorries (Arrow, Sen, Voting)
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
without sorry, and the **backward transfer** (`#3124` completed by
`#11227`) is **established**: the constructive core `hcolPres`, the
sub-goal `num` (`wf` parity, `#3163`) and the 2 residuals `fox`/`col`
(vacuous all-distinct mode, `#11227`) are closed — the **connected R1
bi-implication is PROVEN**. The **corollary `trefoil_not_unknot`**
(#8766) is **proven** by composing the (sorry-bearing) invariant with
the two component lemmas. The **forward R2-up transfer**
(`tricolorable_forward_r2_up`, #11276) is **proven without sorry**,
framed by the named walls `r2_append_only_wall`/`r3_determined_wall`
(**14 real sorries** in total, CI baseline after #11227).

The **Reidemeister corridor #8696** (5 PRs MERGED, c.8162-c.8169)
additionally clarified the structure of the 6 move-surgery sites in
`Reidemeister.lean`: direct proofs by `⟨rfl, rfl⟩` after the field-eqs
refactor — a readability gain, **zero impact** on the sorry count (the
corridor did not target the closure of the gated PL theorems).

### The lock

The marquee `tricolorable_invariant` remains **gated**, but the lock
has changed nature: it is no longer the §9.1 residuals (closed,
#11227), it is the **R2 model itself**. The wall
`r2_append_only_wall` (#11276) proves that the free
`ReidemeisterStep.r2` constructor (append-only) relates
`emptyDiagram` (not tricolorable) to `twoTwinCrossings`
(tricolorable) — the descending arm of the master iff is **FALSE
under the current model**. Closure requires the **connected R2/R3
re-modelling** (`Reidemeister2Connected` / `Reidemeister3Connected` /
`ReidemeisterEquivConnected`, proposal on #2874 with an
exhaustive-validation plan BEFORE proof — protocol applied
successfully in R1 and delivered in R2/R3: scripts #11467/#11486).
The "distant" results — Conway non-slice (Piccirillo), Lidman's
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
`#3088`) corrects this flaw. The **backward decomposition** (`#3124`)
— proving the tractable, delivering with documented residual
sub-sorries — paid off twice: the residuals were closed by a
**vacuity** argument (#11227: the all-distinct kink mode never occurs
under Path B — the anticipated research-level construction was
unneeded), and the "brute-force exhaustive validation BEFORE the Lean
statement" pattern (R1: 2526 diagrams/24 monogon failures; R2:
#11467; R3: #11486) became the track's standard protocol.

### Next steps

1. Deliver the connected **R2/R3** re-modelling:
   `Reidemeister2Connected` (statement #11469, transfer #11477, in
   review), `Reidemeister3Connected` (exhaustive validation #11486: a
   Sat-equal bijection found on the triangle σ1σ2σ1↔σ2σ1σ2 — the
   statement follows), then `ReidemeisterEquivConnected` (RTC) and the
   master `tricolorable_invariant_connected`.
2. The formal counter-example of the R2 wall
   (`not_tricolorable_invariant_current`, #11453, in review)
   documents why the current master CANNOT be closed as-is.
3. Distant scaffolding: wait for the evolution of Mathlib
   (3-manifolds, Heegaard-Floer) for Conway and Lidman.
