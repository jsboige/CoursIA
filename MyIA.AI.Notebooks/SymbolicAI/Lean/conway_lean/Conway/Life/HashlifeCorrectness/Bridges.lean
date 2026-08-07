/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Conway.Life.HashlifeCorrectness.Bridges

Sub-module of `Conway.Life.HashlifeCorrectness`. Phase 3b multi-agent
prover targets (Epic #1453). Scope: /-! ## P3. Padding correctness
was byte-identically displaced from the original monolith at PR A of
#9863 (po-2023, dispatch ai-01 2026-08-07T12:20:37Z).

Proof bodies are unchanged — only framing (imports, namespace opens,
this docstring) is added. The 38 allow-axioms names referenced by the
audit job in `.github/workflows/lean-conway.yml` depend only on the
`Conway.Life.*` namespace prefix, NOT on intermediate namespaces or
file paths — so the allow-list stays byte-identical across the split.
-/

import Conway.Life
import Conway.Life.GridCanonical
import Conway.Life.MacroCell
import Conway.Life.Hashlife
import Conway.Life.ConeGeometry

namespace Conway
namespace Life

open MacroCell
/-! ## P3. Padding correctness

`padCenter2 c` places `c` (assuming `c.level ≥ 1`) inside a level-`(k+2)`
MacroCell. Each application of `padToLevelPlus1` shifts every cell of
the original input by `+2^(k-1)` (the input lands in the SE position of
the SW sub-quadrant for `nw`, NE/SW/SE wrap analogously). Composing twice,
`padCenter2` shifts every cell of `c` by `+2^(k-1) + 2^k = 3·2^(k-1)`.

To recover `c.toCellsAux 0 0` from `(padCenter2 c).toCellsAux _ _`,
the calling offset must therefore be `-3·2^(k-1)` on both axes. -/

/-- (helper) Empty `MacroCell`s contribute no live cells to the enumeration.
    By induction on the level: at level 0 we have `deadLeaf = leaf false`,
    which `toCellsAux` maps to `[]`; at level `n+1` the four sub-quadrants
    each enumerate to `[]` by the IH, and the concatenation is `[]`. -/
private theorem emptyOfLevel_toCellsAux_eq_nil (n : Nat) (r0 c0 : Int) :
    (MacroCell.emptyOfLevel n).toCellsAux r0 c0 = [] := by
  induction n generalizing r0 c0 with
  | zero => rfl
  | succ n ih =>
    simp only [MacroCell.emptyOfLevel, MacroCell.toCellsAux, ih,
               List.append_nil, List.nil_append]

/-- (helper) `(emptyOfLevel n).level = n` — induction over `n`. -/
private theorem emptyOfLevel_level (n : Nat) : (MacroCell.emptyOfLevel n).level = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show 1 + (MacroCell.emptyOfLevel n).level = n + 1
    rw [ih]; omega

/-- (helper) `padToLevelPlus1` applied to a node-typed `MacroCell` of level
    `1+nw.level` shifts every enumerated cell by `+2^(nw.level)` on both axes.

    By definition of `padToLevelPlus1`, the input `node nw ne sw se` becomes
    `node Q1 Q2 Q3 Q4` where each Qi is a `node` placing the original cell in
    one quadrant (NW for nw, NE for ne, etc.) and `emptyOfLevel nw.level` in
    the others. Empty cells contribute `[]` via `emptyOfLevel_toCellsAux_eq_nil`,
    so only the original cells survive — shifted by `2^nw.level` per axis
    (the inner-quadrant offset). -/
private theorem padToLevelPlus1_toCellsAux_node
    (nw ne sw se : MacroCell) (r0 c0 : Int) :
    (padToLevelPlus1 (MacroCell.node nw ne sw se)).toCellsAux r0 c0
      = (MacroCell.node nw ne sw se).toCellsAux
          (r0 + ((2 ^ nw.level : Nat) : Int))
          (c0 + ((2 ^ nw.level : Nat) : Int)) := by
  have h2s : ((2 ^ (1 + nw.level) : Nat) : Int)
           = ((2 ^ nw.level : Nat) : Int) + ((2 ^ nw.level : Nat) : Int) := by
    push_cast
    rw [Nat.add_comm 1 nw.level, pow_succ]
    ring
  simp only [padToLevelPlus1, MacroCell.toCellsAux, MacroCell.level,
             emptyOfLevel_level, emptyOfLevel_toCellsAux_eq_nil,
             List.nil_append, List.append_nil, h2s, ← Int.add_assoc]

/-- The cells of `padCenter2 c` viewed from the corrected center offset
    equal the cells of `c` viewed from origin. The negative offset
    `-(3·2^(k-1))` exactly cancels the cumulative shift introduced by
    the two `padToLevelPlus1` applications.

    **Statement correction (#2197)**: the previous version used
    `center_off = (2^k, 2^k)`, which is incorrect — it would only cancel
    a shift of `-2^k`, but the actual shift introduced by `padCenter2`
    is `+3·2^(k-1)`. Verified empirically below on the 2×2 block witness
    (`padCenter2_correct_block_level1`).

    **Proof**: case-split on `c`. The leaf case contradicts `hk : 1 ≤ c.level`
    (leaves have level 0). For the node case, apply `padToLevelPlus1_toCellsAux_node`
    twice (the level after one application becomes `1 + nw.level + 1`, so the second
    shift is `2^(1 + nw.level) = 2 · 2^nw.level`). The cumulative shift is
    `2^nw.level + 2·2^nw.level = 3·2^nw.level = 3·2^(c.level - 1)`, which the
    `center_off = -(3·2^(c.level - 1))` exactly cancels. -/
theorem padCenter2_correct (c : MacroCell) (hk : 1 ≤ c.level) :
    let k := c.level
    let padded := padCenter2 c
    let center_off : Int := -(3 * 2 ^ (k - 1) : Int)
    padded.toCellsAux center_off center_off = c.toCellsAux 0 0 := by
  match c, hk with
  | MacroCell.leaf _, hk =>
    -- Leaf level is 0; contradiction with 1 ≤ c.level.
    simp [MacroCell.level] at hk
  | MacroCell.node nw ne sw se, _ =>
    -- c.level = 1 + nw.level, so c.level - 1 = nw.level.
    -- padCenter2 c = padToLevelPlus1 (padToLevelPlus1 c).
    -- After 1st application: shift +2^nw.level. Result level = 2 + nw.level, and its
    -- inner nw is (node e e e nw), with level 1 + nw.level.
    -- After 2nd application: shift +2^(1+nw.level) = 2 · 2^nw.level. Cumulative: 3·2^nw.level.
    simp only [MacroCell.level, padCenter2, Nat.add_sub_cancel_left]
    -- Expose the INNER padToLevelPlus1 as a node literal via rfl (4-way pad form).
    -- This only rewrites the inner occurrence (the outer is padToLevelPlus1 of
    -- a padToLevelPlus1 application, not of a node literal).
    have hinner : padToLevelPlus1 (MacroCell.node nw ne sw se) =
        MacroCell.node
          (MacroCell.node (MacroCell.emptyOfLevel nw.level) (MacroCell.emptyOfLevel nw.level)
                          (MacroCell.emptyOfLevel nw.level) nw)
          (MacroCell.node (MacroCell.emptyOfLevel nw.level) (MacroCell.emptyOfLevel nw.level)
                          ne (MacroCell.emptyOfLevel nw.level))
          (MacroCell.node (MacroCell.emptyOfLevel nw.level) sw
                          (MacroCell.emptyOfLevel nw.level) (MacroCell.emptyOfLevel nw.level))
          (MacroCell.node se (MacroCell.emptyOfLevel nw.level)
                          (MacroCell.emptyOfLevel nw.level) (MacroCell.emptyOfLevel nw.level)) := rfl
    rw [hinner]
    -- Now the outer padToLevelPlus1 is applied to a node literal. Apply shift lemma.
    rw [padToLevelPlus1_toCellsAux_node]
    -- After shift: (node Q1 Q2 Q3 Q4).tCA (c_off + 2^Q1.level) (...) where Q1.level = 1 + nw.level.
    -- Reduce 2^(1+nw.level) = 2^nw.level + 2^nw.level (Int).
    have hpow_succ : ((2 ^ (1 + nw.level) : Nat) : Int)
                   = ((2 ^ nw.level : Nat) : Int) + ((2 ^ nw.level : Nat) : Int) := by
      push_cast
      rw [Nat.add_comm 1 nw.level, pow_succ]
      ring
    -- Unfold the outer toCellsAux + strip empty cells via empty lemmas.
    simp only [MacroCell.toCellsAux, MacroCell.level, emptyOfLevel_level,
               emptyOfLevel_toCellsAux_eq_nil, List.nil_append, List.append_nil, hpow_succ]
    -- Both sides are now 4-way ++ of nw/ne/sw/se applied to Int offsets.
    -- LHS offsets reduce via push_cast + ring to match RHS (-3s + 2s + s = 0; -3s + 2s + 2s = s).
    congr 1
    · congr 1
      · congr 1 <;> push_cast <;> ring_nf
      · congr 1 <;> push_cast <;> ring_nf
    · congr 1 <;> push_cast <;> ring_nf

/-- WITNESS for P3 on a 2×2 block (level 1, shift = 3·2^0 = 3).

    Empirically proven via `native_decide`: the corrected statement
    holds on the level-1 all-alive 2×2 block. This certifies that the
    constant `-(3·2^(k-1))` is correct (vs. the previous `2^k`).

    Future work: extend to general `c.level ≥ 1` by structural argument
    (P3 main theorem above). -/
theorem padCenter2_correct_block_level1 :
    let c : MacroCell :=
      MacroCell.node MacroCell.aliveLeaf MacroCell.aliveLeaf
                     MacroCell.aliveLeaf MacroCell.aliveLeaf
    (padCenter2 c).toCellsAux (-3 : Int) (-3 : Int) = c.toCellsAux 0 0 := by
  native_decide

/-! ### N2 step 3 bridge: `padCenter2` margin ≥ Chebyshev jump reach

The geometric precondition for `p5_large_n_jump`: the `padCenter2`
margin `(3·2^(k-1))` strictly contains the Hashlife jump reach
(`2^k`) for any level-`k ≥ 1` MacroCell. Proving this eliminates the
last geometric question before `p5_large_n_jump` can be assembled:

    a level-`k` MacroCell has side `2^k`; padded by 2 levels it has
    side `2^(k+2) = 4·2^k`; the per-side margin is `(4·2^k - 2^k)/2
    = 3·2^(k-1)`. The Hashlife jump size is `jumpSize k = 2^k`, and
    by `evolve_reach_chebyshev` (lightCone.lean L270-298, N2 step 2),
    any cell alive after `2^k` generations lies within Chebyshev
    distance `2^k` of an initial cell. Since `2^k ≤ 3·2^(k-1)` for
    `k ≥ 1`, the Chebyshev reach fits inside the margin with a factor
    of 3/2 to spare.

This is the **pure-arithmetic half** of the light-cone ↔ padding
bridge. It is independently provable (no coordinate hypotheses, no
`MacroCell` arguments), so it can be wired into `p5_large_n_jump`
once the P4 inductive step (`p4_succ_membership`) closes.

Sorry-free, additive, no existing sorries modified (§D anti-regression
safe). EPIC #3846 (N2 step 3, research-Long dedicated session). -/

/-- **Pad-margin ≥ jump-reach** (pure arithmetic, sorry-free).
    For a level-`k ≥ 1` MacroCell, the per-side `padCenter2` margin
    `3·2^(k-1)` is strictly larger than the Hashlife jump size `2^k`
    — i.e. the margin contains the Chebyshev reach of the jump.
    Equivalently, the side length `4·2^k` of the padded cell exceeds
    the jump reach `2·2^k` (Chebyshev radius `2^k` doubled) by a
    factor of 2.

    Proof: distribute `3 = 1 + 2`, reduce goal to
    `2^k ≤ 2^(k-1) + 2·2^(k-1)`, then rewrite
    `2·2^(k-1) = 2^((k-1)+1) = 2^k` via `pow_succ'` and the
    `(k-1)+1 = k` linear fact (the only piece `omega` closes here;
    the actual power rewrite is not linear, hence explicit). Finally
    `Nat.add_comm` puts the goal in the form `2^k ≤ 2^k + 2^(k-1)`,
    closed by `Nat.le_add_right`. -/
theorem padCenter2_margin_ge_jumpReach (k : Nat) (hk : 1 ≤ k) :
    (2 : Nat)^k ≤ (3 : Nat) * (2 : Nat)^(k - 1) := by
  have hk_eq : (k - 1) + 1 = k := by omega
  rw [show (3 : Nat) = 1 + 2 from rfl, Nat.add_mul, Nat.one_mul]
  have h2k : (2 : Nat) * (2 : Nat)^(k - 1) = (2 : Nat)^k := by
    rw [← pow_succ', hk_eq]
  rw [h2k, Nat.add_comm]
  exact Nat.le_add_right _ _

/-- **Strict margin headroom** (consequence of the above).
    The margin exceeds the reach by exactly `2^(k-1)` cells per side —
    a 50% headroom over the tight Chebyshev-`2^k` ball. -/
theorem padCenter2_margin_strictly_gt_jumpReach (k : Nat) (hk : 1 ≤ k) :
    (2 : Nat)^k < (3 : Nat) * (2 : Nat)^(k - 1) := by
  have hk_eq : (k - 1) + 1 = k := by omega
  rw [show (3 : Nat) = (1 : Nat) + 2 from rfl, Nat.add_mul, Nat.one_mul]
  have h2k : (2 : Nat) * (2 : Nat)^(k - 1) = (2 : Nat)^k := by
    rw [← pow_succ', hk_eq]
  rw [h2k, Nat.add_comm]
  apply Nat.lt_add_of_pos_right
  exact Nat.two_pow_pos (k - 1)

/-! ## Well-formedness of MacroCells

`MacroCell.level` only walks the `nw` spine, so `c.level = k + 2` does
**not** constrain the `ne`/`sw`/`se` subtrees. `hashlifeResultAux` sends
such malformed cells to its defensive arm (`emptyOfLevel (c.level - 1)`),
while `toGrid`/`evolve` still see the live cells of the misplaced
subtrees — so the unrestricted P4 statement is **false**
(`p4_unrestricted_counterexample` below).

`wf` formalizes the convention stated on the `MacroCell` type ("all
required, by convention but not enforced by the type, to have the same
level"). It is the missing hypothesis of P4. Candidate for promotion to
`Conway.Life.MacroCell` once the P4/P5 proofs land. -/

/-- Well-formed `MacroCell`: every `node` has four well-formed subtrees
    of equal level. Boolean-valued so concrete instances are decidable
    by `decide`/`native_decide`. -/
def MacroCell.wf : MacroCell → Bool
  | .leaf _ => true
  | .node nw ne sw se =>
    nw.wf && ne.wf && sw.wf && se.wf
      && (ne.level == nw.level) && (sw.level == nw.level)
      && (se.level == nw.level)

/-- Separate well-formedness predicate (c.142). An `inductive`, hence OPAQUE
    to defeq — unlike `MacroCell.wf` (a transparent `Bool` def), `cellWf (node …)`
    does NOT whnf-reduce during defeq. This is the unblock for the level/wf
    preservation lemma of `hashlifeResultAux`: its `.wf` conjunct diverges on
    whnf for nested hRA results (any defeq on `(node <hRA terms>).wf` evaluates
    the transparent `wf`, recursing into `hashlifeResultAux`; c.140/c.141, 8M
    heartbeats, 5 formulations). Reformulated over the opaque `cellWf`, the
    conjunct closes by constructor application + `omega` (treating `.level` as
    atoms, as the level conjunct already did). -/
inductive cellWf : MacroCell → Prop
  | leaf (b : Bool) : cellWf (.leaf b)
  | node {nw ne sw se : MacroCell}
      (hnw : cellWf nw) (hne : cellWf ne) (hsw : cellWf sw) (hse : cellWf se)
      (hne_lvl : nw.level = ne.level) (hsw_lvl : nw.level = sw.level)
      (hse_lvl : nw.level = se.level) :
      cellWf (.node nw ne sw se)

/-- Bridge between the opaque `cellWf` predicate and the transparent `MacroCell.wf`
    (c.142). Both directions, by structural induction on `c` (clean context, no
    hRA terms — so no whnf divergence). Lets the preservation lemma consume
    `.wf = true` facts (from `p4_double_nine_shape`, `wf_hashlifeResult_of_level_two`)
    and produce `cellWf`, and lets downstream code convert back. -/
theorem cellWf_of_wf (c : MacroCell) : c.wf = true → cellWf c := by
  induction c with
  | leaf b => intro _; exact cellWf.leaf b
  | node nw ne sw se hnw hne hsw hse =>
    intro h
    have hne_eq : nw.level = ne.level := by simp_all [MacroCell.wf, beq_iff_eq]
    have hsw_eq : nw.level = sw.level := by simp_all [MacroCell.wf, beq_iff_eq]
    have hse_eq : nw.level = se.level := by simp_all [MacroCell.wf, beq_iff_eq]
    have hw_nw : nw.wf = true := by simp_all [MacroCell.wf]
    have hw_ne : ne.wf = true := by simp_all [MacroCell.wf]
    have hw_sw : sw.wf = true := by simp_all [MacroCell.wf]
    have hw_se : se.wf = true := by simp_all [MacroCell.wf]
    exact cellWf.node (hnw hw_nw) (hne hw_ne) (hsw hw_sw) (hse hw_se)
                   hne_eq hsw_eq hse_eq

theorem wf_of_cellWf {c : MacroCell} (h : cellWf c) : c.wf = true := by
  induction h with
  | leaf b => simp [MacroCell.wf]
  | node _ _ _ _ hne_lvl hsw_lvl hse_lvl ihnw ihne ihsw ihse =>
    simp only [MacroCell.wf, ihnw, ihne, ihsw, ihse, ← hne_lvl, ← hsw_lvl, ← hse_lvl,
               beq_self_eq_true, Bool.true_and, Bool.and_true]

/-- A malformed level-2 cell: `nw` is a level-1 node but `ne`/`sw`/`se`
    are bare leaves. `level` only inspects `nw`, so
    `malformedLevel2.level = 2` satisfies the unrestricted P4 hypothesis
    with `k = 0`. Live cells (via `toCellsAux`, which offsets `ne`/`sw`
    by `2^nw.level = 2`): `(1,1)`, `(0,2)`, `(2,0)`. -/
private def malformedLevel2 : MacroCell :=
  .node (.node (leaf false) (leaf false) (leaf false) (leaf true))
        (leaf true) (leaf true) (leaf false)

example : malformedLevel2.level = 2 := rfl
example : malformedLevel2.wf = false := rfl

end Life
end Conway
