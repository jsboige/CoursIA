/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Conway.Life.HashlifeCorrectness.Decomposition

Sub-module of `Conway.Life.HashlifeCorrectness`. Phase 3b multi-agent
prover targets (Epic #1453). Scope: /-! ## P4. Hashlife central result (decompose-compose)
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
/-! ## P4. Hashlife central result (decompose-compose)

On a level-`k` MacroCell `c` with adequate padding, `hashlifeResult c`
equals `step^[2^(k-2)]` applied to the centered sub-region.

This is the heart of Hashlife: the recursive quadtree decomposition followed
by memoized recomposition gives the same answer as the flat iteration.

**Statement correction (#2215 followup)**: the previous version used `off =
(0, 0)` for both input and output. This is incorrect: `hashlifeResultAux
(k+2) c` produces a level-`(k+1)` cell representing the centered `2^(k+1) ×
2^(k+1)` region of the level-`(k+2)` input. The center starts at position
`(2^k, 2^k)` in the input's coordinate system. So `result.toGrid (2^k,
2^k)` covers `[2^k, 2^k + 2^(k+1)) × [2^k, 2^k + 2^(k+1))`, which is
exactly the centered region.

**Statement correction (2026-06-11)**: added the `c.wf = true` hypothesis.
Without it the statement is **false**: `c.level = k + 2` only constrains
the `nw` spine, and on malformed cells `hashlifeResultAux` answers
`emptyOfLevel (c.level - 1)` while `evolve` still sees the misplaced live
cells. Certified counterexample: `p4_unrestricted_counterexample`. The
corrected statement is proven in the base case `k = 0` for **all**
well-formed cells (`hashlifeResult_central_correct_base`, 2^16 instances)
and witnessed in the recursive arms at `k = 1` and `k = 2`. -/

/-- Restrict a Grid to the centered region `[lo, lo + size) × [lo, lo + size)`. -/
def restrictGridTo (g : Grid) (lo : Int) (size : Nat) : Grid :=
  g.filter fun p =>
    lo ≤ p.1 && p.1 < lo + (size : Int) &&
    lo ≤ p.2 && p.2 < lo + (size : Int)

/-- **The unrestricted P4 statement is false.** On `malformedLevel2`
    (which satisfies `c.level = 0 + 2`), `hashlifeResultAux` takes its
    defensive malformed arm and returns the empty level-1 cell (LHS
    `= []`), while the reference evolution keeps cell `(1,1)` alive —
    it has exactly two diagonal neighbours, `(0,2)` and `(2,0)`, coming
    from the misplaced leaf subtrees (RHS `= [(1,1)]`). Hence the
    `c.wf` hypothesis in `hashlifeResult_central_correct` is necessary. -/
theorem p4_unrestricted_counterexample :
    ¬ ((hashlifeResultAux (0 + 2) malformedLevel2).toGrid
          ((2 ^ 0 : Nat), (2 ^ 0 : Nat))
        = restrictGridTo (evolve (2 ^ 0) (malformedLevel2.toGrid (0, 0)))
            (2 ^ 0 : Int) (2 ^ (0 + 1))) := by
  native_decide

/-! ## Canonical-form bridge: P4 list equality ⇔ pointwise membership

Both sides of the P4 statement are **canonical** grids
(`Conway.Life.GridCanonical`): the LHS is a `toGrid` (a `sortDedup` image),
the RHS a `filter` of `evolve (2^k)` with `2^k ≥ 1` (a `step` image). By
rigidity of canonical grids (`Canonical.ext`), proving the list equality is
equivalent to proving membership pointwise — which is where the light-cone
(P2) and double-nine decomposition arguments actually live. -/

/-- `toGrid` images are canonical grids. -/
theorem canonical_toGrid (offset : Int × Int) (c : MacroCell) :
    Canonical (c.toGrid offset) := by
  unfold MacroCell.toGrid
  exact canonical_sortDedup _

/-- Membership in a `toGrid` image, unfolded to the raw cell emission. -/
theorem mem_toGrid {c : MacroCell} {offset : Int × Int} {p : Int × Int} :
    p ∈ c.toGrid offset ↔ p ∈ c.toCellsAux offset.1 offset.2 := by
  unfold MacroCell.toGrid
  exact mem_sortDedup

/-- **Offset-shift for `toGrid` membership** (P4.4 offset-matching ingredient).
    Membership of `p` in `c.toGrid (r0, c0)` is equivalent to membership of the
    translated point `(p.1 - r0, p.2 - c0)` in `c.toGrid (0, 0)` — i.e. the cell
    content is the same grid, just viewed at a different origin. This is the
    shift ingredient the P4.4 offset-matching assembly needs to relate each
    quadrant membership `p ∈ out_*.toGrid (off, off)` (after `mem_toGrid_node`
    decomposes the result node into its four children at offsets `(2^k, 2^k)`,
    `(2^k, 2^k + 2^out_nw.level)`, …) to the centered form that
    `centralCorrect_mem` + the ih characterize. -/
theorem mem_toGrid_shift {c : MacroCell} {r0 c0 : Int} {p : Int × Int} :
    p ∈ c.toGrid (r0, c0) ↔ (p.1 - r0, p.2 - c0) ∈ c.toGrid (0, 0) := by
  rw [mem_toGrid, mem_toGrid]
  exact mem_toCellsAux_shift

/-- **Offset-to-offset translation for `toGrid` membership** (P4.4 offset-matching
    ingredient). Membership of `p` in `c.toGrid (a, b)` is equivalent to
    membership of the point translated by `(a'-a, b'-b)` in `c.toGrid (a', b')` —
    i.e. re-anchoring the same cell's grid at a different origin.

    This is the double-shift ingredient the P4.4 offset-matching assembly needs:
    after `mem_toGrid_node` decomposes the result node, each quadrant sits at its
    own offset (e.g. NW at `(2^k, 2^k)`), but `centralCorrect_mem` (G2)
    characterizes the quadrant at offset `(2^(k-1), 2^(k-1))` (its `2^j` centering
    with `j = k-1`). `toGrid_shift_between` bridges those two offsets directly,
    without re-centering through `(0,0)` twice. -/
theorem toGrid_shift_between {c : MacroCell} {a b a' b' : Int} {p : Int × Int} :
    p ∈ c.toGrid (a, b) ↔ (p.1 - a + a', p.2 - b + b') ∈ c.toGrid (a', b') := by
  rw [mem_toGrid_shift]
  constructor
  · intro h
    rw [mem_toGrid_shift]
    have he : (p.1 - a + a' - a', p.2 - b + b' - b') = (p.1 - a, p.2 - b) := by ext <;> ring
    rw [he]; exact h
  · intro h
    rw [mem_toGrid_shift] at h
    have he : (p.1 - a, p.2 - b) = (p.1 - a + a' - a', p.2 - b + b' - b') := by ext <;> ring
    rw [he]; exact h

/-- **G3 infrastructure (toGrid node-decomposition).** Membership in a `node`
    cell's grid decomposes into membership in the four children's grids, with
    the standard quadtree offset shifts (row increases downward, column
    rightward): `nw` at `(r0,c0)`, `ne` at `(r0, c0+half)`, `sw` at
    `(r0+half, c0)`, `se` at `(r0+half, c0+half)`, where `half = 2^nw.level`.

    Pure structural fact — no `hashlifeResultAux`. This is the sorry-free G3
    piece of `p4_succ_membership`: once established, the LHS
    `p ∈ (hashlifeResultAux (k+2) c).toGrid (2^k, 2^k)` (which is a
    `node out_nw out_ne out_sw out_se`) decomposes into the four
    `out_*.toGrid ...` memberships, each characterizable via
    `centralCorrect_mem` + the induction hypothesis `centralCorrect q_* (k-1)`. -/
theorem mem_toGrid_node {nw ne sw se : MacroCell} {r0 c0 : Int} {p : Int × Int} :
    p ∈ (node nw ne sw se).toGrid (r0, c0) ↔
      p ∈ nw.toGrid (r0, c0) ∨
      p ∈ ne.toGrid (r0, c0 + (2 ^ nw.level : Int)) ∨
      p ∈ sw.toGrid (r0 + (2 ^ nw.level : Int), c0) ∨
      p ∈ se.toGrid (r0 + (2 ^ nw.level : Int), c0 + (2 ^ nw.level : Int)) := by
  repeat rw [mem_toGrid]
  simp only [toCellsAux, List.mem_append]
  tauto

/-- **G3 LHS-unlock infrastructure.** The single-step iota reduction of
    `hashlifeResultAux` at the well-formed (`fuel + 1`, 16-grandchild node) arm.

    `hashlifeResultAux`'s definition uses a pattern alias `c@(node ...)`, whose
    alias fvar blocks `simp`/`unfold` syntactic rewriting (cf. the
    `HashlifeMemo` comment). This lemma restates the well-formed arm with
    explicit patterns and zeta-expanded `let`s, so it IS available for
    rewriting from this module. It is true by `rfl` (iota + zeta reduction).

    **Why this is the LHS-unlock for `p4_succ_membership`**: the goal's LHS is
    `p ∈ (hashlifeResultAux (k+2) c).toGrid (2^k, 2^k)`. With `k+2 = (k+1)+1`
    and `c` destructured via `p4_double_nine_shape`, this lemma rewrites the
    `hRA` application to the explicit `node out_nw out_ne out_sw out_se` (else
    branch, level ≥ 3), exposing the `node _ _ _ _` constructor that
    `mem_toGrid_node` needs. It is the missing link between the LHS and the
    G3 toGrid decomposition. -/
theorem hashlifeResultAux_succ_node (fuel : Nat)
    (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 : MacroCell) :
    hashlifeResultAux (fuel + 1)
      (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
            (node c1 c2 c3 c4) (node d1 d2 d3 d4)) =
    if (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
             (node c1 c2 c3 c4) (node d1 d2 d3 d4)).level == 2 then
      step4x4 (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
                    (node c1 c2 c3 c4) (node d1 d2 d3 d4))
    else
      node
        (hashlifeResultAux fuel (node
          (hashlifeResultAux fuel (node a1 a2 a3 a4))
          (hashlifeResultAux fuel (node a2 b1 a4 b3))
          (hashlifeResultAux fuel (node a3 a4 c1 c2))
          (hashlifeResultAux fuel (node a4 b3 c2 d1))))
        (hashlifeResultAux fuel (node
          (hashlifeResultAux fuel (node a2 b1 a4 b3))
          (hashlifeResultAux fuel (node b1 b2 b3 b4))
          (hashlifeResultAux fuel (node a4 b3 c2 d1))
          (hashlifeResultAux fuel (node b3 b4 d1 d2))))
        (hashlifeResultAux fuel (node
          (hashlifeResultAux fuel (node a3 a4 c1 c2))
          (hashlifeResultAux fuel (node a4 b3 c2 d1))
          (hashlifeResultAux fuel (node c1 c2 c3 c4))
          (hashlifeResultAux fuel (node c2 d1 c4 d3))))
        (hashlifeResultAux fuel (node
          (hashlifeResultAux fuel (node a4 b3 c2 d1))
          (hashlifeResultAux fuel (node b3 b4 d1 d2))
          (hashlifeResultAux fuel (node c2 d1 c4 d3))
          (hashlifeResultAux fuel (node d1 d2 d3 d4)))) := rfl

/-- Membership in a restricted grid: in the grid and inside the window. -/
theorem mem_restrictGridTo {g : Grid} {lo : Int} {size : Nat} {p : Int × Int} :
    p ∈ restrictGridTo g lo size ↔
      p ∈ g ∧ lo ≤ p.1 ∧ p.1 < lo + (size : Int) ∧
        lo ≤ p.2 ∧ p.2 < lo + (size : Int) := by
  simp [restrictGridTo, List.mem_filter, and_assoc]

/-- **Four-quadrant window partition** (P4.4 offset-matching ingredient, G1).
    A square window `[a, a + 2s)²` (with `0 ≤ s`) is exactly the disjoint union
    of its four half-side quadrants: NW `[a, a+s)²`, NE `[a, a+s) × [a+s, a+2s)`,
    SW `[a+s, a+2s) × [a, a+s)`, SE `[a+s, a+2s)²`. Pure linear arithmetic — no
    `hashlifeResultAux`, no whnf.

    This is the G1 ingredient the `p4_succ_membership` offset-matching assembly
    consumes: the RHS window bounds `[2^k, 2^k + 2^(k+1))² = [2^k, 3·2^k)²`
    (from `mem_restrictGridTo`, with `lo = 2^k`, `size = 2^(k+1)`) factor as
    `[a, a+2s)²` with `a = 2^k`, `s = 2^k`; the four quadrants of the result node
    (each level `k`, side `2^k = s`) tile exactly these four sub-windows. The
    disjunction `Or` on the LHS (from `mem_toGrid_node`) thus partitions the
    window bound on the RHS. -/
theorem quad_partition_bounds (a s : Int) (hs : 0 ≤ s) (p : Int × Int) :
    (a ≤ p.1 ∧ p.1 < a + 2*s ∧ a ≤ p.2 ∧ p.2 < a + 2*s) ↔
      (a ≤ p.1 ∧ p.1 < a + s ∧ a ≤ p.2 ∧ p.2 < a + s) ∨
      (a ≤ p.1 ∧ p.1 < a + s ∧ a + s ≤ p.2 ∧ p.2 < a + 2*s) ∨
      (a + s ≤ p.1 ∧ p.1 < a + 2*s ∧ a ≤ p.2 ∧ p.2 < a + s) ∨
      (a + s ≤ p.1 ∧ p.1 < a + 2*s ∧ a + s ≤ p.2 ∧ p.2 < a + 2*s) := by
  omega

/-- **The P4 ext bridge**: pointwise membership suffices for the P4 goal.
    Reduces the list-equality statement of `hashlifeResult_central_correct`
    to a per-cell biconditional. -/
theorem p4_ext_bridge (c : MacroCell) (k : Nat)
    (h : ∀ p, p ∈ (hashlifeResultAux (k + 2) c).toGrid ((2^k : Nat), (2^k : Nat)) ↔
        p ∈ restrictGridTo (evolve (2^k) (c.toGrid (0, 0))) (2^k : Int) (2^(k+1))) :
    (hashlifeResultAux (k + 2) c).toGrid ((2^k : Nat), (2^k : Nat)) =
      restrictGridTo (evolve (2^k) (c.toGrid (0, 0))) (2^k : Int) (2^(k+1)) := by
  apply Canonical.ext (canonical_toGrid _ _) _ h
  unfold restrictGridTo
  exact (canonical_evolve_of_pos (Nat.two_pow_pos k) _).filter _

/-! ## P4 base case, proven in general

The base case `k = 0` of the (corrected) P4 statement, proven for **all**
well-formed level-2 cells — not just the witnesses above. The shape
lemmas reduce a well-formed level-2 cell to its 16 leaf booleans; the
exhaustive lemma then checks all `2^16` configurations by
`native_decide`. This certifies that the corrected statement is
*provable* (at least in the base case), not merely satisfiable. -/

/-- A level-0 cell is a leaf (regardless of well-formedness). -/
private theorem shape_of_level_zero :
    ∀ c : MacroCell, c.level = 0 → ∃ b, c = leaf b
  | leaf b, _ => ⟨b, rfl⟩
  | node _ _ _ _, h => by exfalso; simp only [MacroCell.level] at h; omega

/-- A level-`(n+1)` cell is a node whose `nw` has level `n`. -/
private theorem shape_of_level_succ :
    ∀ (c : MacroCell) (n : Nat), c.level = n + 1 →
      ∃ nw ne sw se, c = node nw ne sw se ∧ nw.level = n
  | leaf _, _, h => by exfalso; simp only [MacroCell.level] at h; omega
  | node nw ne sw se, n, h =>
    ⟨nw, ne, sw, se, rfl, by simp only [MacroCell.level] at h; omega⟩

/-- Unpack the well-formedness of a node: four well-formed subtrees of
    equal level. -/
private theorem wf_node_elim {nw ne sw se : MacroCell}
    (h : (node nw ne sw se).wf = true) :
    nw.wf = true ∧ ne.wf = true ∧ sw.wf = true ∧ se.wf = true
      ∧ ne.level = nw.level ∧ sw.level = nw.level ∧ se.level = nw.level := by
  simp only [MacroCell.wf, Bool.and_eq_true, beq_iff_eq] at h
  tauto

/-- Combine a node's `level` and `wf` hypotheses to extract the **absolute**
    level (not merely equality) and well-formedness of all four quadrants.
    `wf_node_elim` yields only relative level equality (`ne.level = nw.level`
    etc.); this lemma closes the gap by folding in `(node nw ne sw se).level
    = n + 1` to pin each quadrant's level to `n`. This is the depth-1
    ingredient of the P4 double-nine decomposition (`p4_double_nine_shape`),
    which needs every depth-2 sub-component of a well-formed level-`(k+2)`
    cell to carry a known level `k`. Reusable wherever a well-formed node's
    quadrant levels must be pinned to an absolute value rather than a spine
    offset. -/
private theorem wf_node_quad_level {nw ne sw se : MacroCell} {n : Nat}
    (hlevel : (node nw ne sw se).level = n + 1)
    (hwf : (node nw ne sw se).wf = true) :
    nw.level = n ∧ ne.level = n ∧ sw.level = n ∧ se.level = n ∧
      nw.wf = true ∧ ne.wf = true ∧ sw.wf = true ∧ se.wf = true := by
  obtain ⟨hnw, hne, hsw, hse, hne_eq, hsw_eq, hse_eq⟩ := wf_node_elim hwf
  simp only [MacroCell.level] at hlevel
  refine ⟨?_, ?_, ?_, ?_, hnw, hne, hsw, hse⟩
  all_goals omega

/-- Constructor counterpart to `wf_node_quad_level` (#3012): where that lemma
    *projects* a node's four quadrants, this one *builds* a well-formed node from
    four equal-level well-formed cells, concluding both `level = n + 1` and
    `wf = true`. The second depth-1 ingredient of `p4_double_nine_shape` (P4.1):
    every double-nine sub-cell `n_i` is a `node` of four grandchildren of `c`,
    so once the grandchildren are pinned (by `wf_node_depth2_grandchildren`
    below), this helper closes each sub-cell's `level = k + 1 ∧ wf = true`. -/
private theorem node_wf_level_of_four {g1 g2 g3 g4 : MacroCell} {n : Nat}
    (h1 : g1.level = n) (h2 : g2.level = n) (h3 : g3.level = n) (h4 : g4.level = n)
    (hw1 : g1.wf = true) (hw2 : g2.wf = true) (hw3 : g3.wf = true) (hw4 : g4.wf = true) :
    (node g1 g2 g3 g4).level = n + 1 ∧ (node g1 g2 g3 g4).wf = true := by
  refine ⟨?_, ?_⟩
  · show 1 + g1.level = n + 1
    rw [h1]; omega
  · show (g1.wf && g2.wf && g3.wf && g4.wf
            && (g2.level == g1.level) && (g3.level == g1.level) && (g4.level == g1.level)) = true
    rw [hw1, hw2, hw3, hw4, h1, h2, h3, h4]
    simp only [Bool.true_and, Bool.and_true, beq_self_eq_true]

/-- Depth-2 lift of `wf_node_quad_level` (#3012): a well-formed level-`(n + 2)`
    node has all sixteen depth-2 grandchildren at level `n` and well-formed.
    Applying `wf_node_quad_level` to the outer node pins its four quadrants to
    level `n + 1`; applying it once more to each quadrant pins the sixteen
    grandchildren to level `n`. This is the structural fact
    `p4_double_nine_shape` (P4.1) needs: the nine double-nine sub-cells are
    `node`s of four grandchildren each (see the `n1`..`n9` pattern in
    `Hashlife.lean`'s `hashlifeResultAux`), so combined with
    `node_wf_level_of_four` this discharges every sub-cell's
    `level = k + 1 ∧ wf = true`, leaving only the tiling-union half of P4.1. -/
private theorem wf_node_depth2_grandchildren
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (n : Nat)
    (hlevel : (node (node nw_nw nw_ne nw_sw nw_se)
                    (node ne_nw ne_ne ne_sw ne_se)
                    (node sw_nw sw_ne sw_sw sw_se)
                    (node se_nw se_ne se_sw se_se)).level = n + 2)
    (hwf : (node (node nw_nw nw_ne nw_sw nw_se)
                 (node ne_nw ne_ne ne_sw ne_se)
                 (node sw_nw sw_ne sw_sw sw_se)
                 (node se_nw se_ne se_sw se_se)).wf = true) :
    nw_nw.level = n ∧ nw_nw.wf = true ∧
    nw_ne.level = n ∧ nw_ne.wf = true ∧
    nw_sw.level = n ∧ nw_sw.wf = true ∧
    nw_se.level = n ∧ nw_se.wf = true ∧
    ne_nw.level = n ∧ ne_nw.wf = true ∧
    ne_ne.level = n ∧ ne_ne.wf = true ∧
    ne_sw.level = n ∧ ne_sw.wf = true ∧
    ne_se.level = n ∧ ne_se.wf = true ∧
    sw_nw.level = n ∧ sw_nw.wf = true ∧
    sw_ne.level = n ∧ sw_ne.wf = true ∧
    sw_sw.level = n ∧ sw_sw.wf = true ∧
    sw_se.level = n ∧ sw_se.wf = true ∧
    se_nw.level = n ∧ se_nw.wf = true ∧
    se_ne.level = n ∧ se_ne.wf = true ∧
    se_sw.level = n ∧ se_sw.wf = true ∧
    se_se.level = n ∧ se_se.wf = true := by
  have ho := wf_node_quad_level hlevel hwf
  obtain ⟨q1l, q2l, q3l, q4l, q1w, q2w, q3w, q4w⟩ := ho
  have hnw := wf_node_quad_level (n := n) q1l q1w
  obtain ⟨a1, a2, a3, a4, b1, b2, b3, b4⟩ := hnw
  have hne := wf_node_quad_level (n := n) q2l q2w
  obtain ⟨c1, c2, c3, c4, d1, d2, d3, d4⟩ := hne
  have hsw := wf_node_quad_level (n := n) q3l q3w
  obtain ⟨e1, e2, e3, e4, f1, f2, f3, f4⟩ := hsw
  have hse := wf_node_quad_level (n := n) q4l q4w
  obtain ⟨g1, g2, g3, g4, h1', h2', h3', h4'⟩ := hse
  exact ⟨a1, b1, a2, b2, a3, b3, a4, b4,
         c1, d1, c2, d2, c3, d3, c4, d4,
         e1, f1, e2, f2, e3, f3, e4, f4,
         g1, h1', g2, h2', g3, h3', g4, h4'⟩

/-! ## P3/P4 structural input: empty + padding level/wf preservation

`emptyOfLevel`, `padToLevelPlus1`, `padCenter2`, and `centerInLevelPlus2`
build larger well-formed cells from smaller ones, used by P3 (frame
correctness) and P4 (centering before the Hashlife result). The level and
well-formedness of these results are structural inputs to both pillars:
P3's frame lemma and P4's centering both presuppose the padded cell is
well-formed at the expected level. The `emptyOfLevel_wf` and
`padToLevelPlus1` level+wf facts below are the foundational steps;
`padCenter2`/`centerInLevelPlus2` lift by composition. -/

/-- `(emptyOfLevel n)` is well-formed — induction over `n`. The base case
    `n = 0` is `deadLeaf.wf = true` (a leaf). The successor case: four
    equal-level wf subtrees (each `emptyOfLevel n`, wf by IH, same level by
    `emptyOfLevel_level`), so the node's `wf` conjunction holds. -/
private theorem emptyOfLevel_wf (n : Nat) : (MacroCell.emptyOfLevel n).wf = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (MacroCell.node (MacroCell.emptyOfLevel n) (MacroCell.emptyOfLevel n)
              (MacroCell.emptyOfLevel n) (MacroCell.emptyOfLevel n)).wf = true
    simp only [MacroCell.wf, Bool.and_eq_true, beq_iff_eq, ih, emptyOfLevel_level]
    trivial

/-- `padToLevelPlus1 (node nw ne sw se)` has level `1 + nw.level + 1`: its
    `nw` sub-cell `(node e e e nw)` has level `1 + e.level = 1 + nw.level`
    (since `e = emptyOfLevel nw.level`), so the outer node has level
    `1 + (1 + nw.level)`. -/
private theorem level_padToLevelPlus1 {nw ne sw se : MacroCell} :
    (padToLevelPlus1 (node nw ne sw se)).level = 1 + nw.level + 1 := by
  simp only [padToLevelPlus1, MacroCell.level, emptyOfLevel_level]
  omega

/-- `padToLevelPlus1` preserves well-formedness: from a well-formed node it
    produces a well-formed node one level higher. Each of the four sub-cells
    `(node e e e nw)` etc. is well-formed (three wf equal-level empties plus
    one original subtree) at the same level `1 + nw.level`, so the outer
    node's `wf` conjunction holds. -/
private theorem wf_padToLevelPlus1 {nw ne sw se : MacroCell}
    (h : (node nw ne sw se).wf = true) :
    (padToLevelPlus1 (node nw ne sw se)).wf = true := by
  obtain ⟨hwa, hwb, hwd, hwe, hla, hlb, hld⟩ := wf_node_elim h
  -- emptyOfLevel nw.level : wf, level = nw.level
  have he_wf : (MacroCell.emptyOfLevel nw.level).wf = true := emptyOfLevel_wf nw.level
  have he_lvl : (MacroCell.emptyOfLevel nw.level).level = nw.level := emptyOfLevel_level nw.level
  -- The 4 outer sub-cells are all (node e e e nw) etc. Each has level 1+nw.level
  -- and is wf (3 empties + 1 original, all wf, all equal-level). Build wf directly.
  show (MacroCell.node
          (MacroCell.node (MacroCell.emptyOfLevel nw.level) (MacroCell.emptyOfLevel nw.level)
                          (MacroCell.emptyOfLevel nw.level) nw)
          (MacroCell.node (MacroCell.emptyOfLevel nw.level) (MacroCell.emptyOfLevel nw.level)
                          ne (MacroCell.emptyOfLevel nw.level))
          (MacroCell.node (MacroCell.emptyOfLevel nw.level) sw
                          (MacroCell.emptyOfLevel nw.level) (MacroCell.emptyOfLevel nw.level))
          (MacroCell.node se (MacroCell.emptyOfLevel nw.level)
                          (MacroCell.emptyOfLevel nw.level) (MacroCell.emptyOfLevel nw.level))).wf = true
  simp only [MacroCell.wf, Bool.and_eq_true, beq_iff_eq]
  -- each inner node's wf: 3 empties (wf, same level) + 1 original (wf by hwa/etc.)
  -- and inner level equality (1 + nw.level everywhere)
  simp only [MacroCell.wf, Bool.and_eq_true, beq_iff_eq, he_wf, hwa, hwb, hwd, hwe,
             MacroCell.level, he_lvl, hla, hlb, hld]
  decide

/-- `padToLevelPlus1` preserves well-formedness in either arm: a leaf passes
    through unchanged (`MacroCell.wf (.leaf _) = true`), and a node is padded
    into a wf node by `wf_padToLevelPlus1`. General (non-destructured) form so
    it composes, closing the gap that the destructured `{nw ne sw se}` form
    leaves for the leaf case. -/
private theorem wf_padToLevelPlus1_gen (c : MacroCell) (h : c.wf = true) :
    (padToLevelPlus1 c).wf = true := by
  cases c with
  | leaf _ => simp only [padToLevelPlus1, MacroCell.wf]
  | node nw ne sw se => exact wf_padToLevelPlus1 h

/-- **`padCenter2` preserves well-formedness** — the composition of the two
    `padToLevelPlus1` steps. `padCenter2` is definitionally
    `padToLevelPlus1 (padToLevelPlus1 c)` (Hashlife.lean); this lemma delivers
    the wf lift-by-composition advertised alongside `padToLevelPlus1` /
    `centerInLevelPlus2`. P5.2 structural input: `hashlifeJump c =
    hashlifeResult (padCenter2 c)` feeds `hashlifeResult_central_correct`,
    whose hypothesis `c.wf = true` requires `(padCenter2 c).wf = true` on the
    padded input. -/
theorem wf_padCenter2 (c : MacroCell) (h : c.wf = true) :
    (padCenter2 c).wf = true := by
  show (padToLevelPlus1 (padToLevelPlus1 c)).wf = true
  exact wf_padToLevelPlus1_gen _ (wf_padToLevelPlus1_gen c h)

/-- **`padCenter2` lifts the level by 2** (level companion of
    `wf_padCenter2`). On a node `c` (hence `1 ≤ c.level`), composing
    `padToLevelPlus1` twice raises the level by exactly 2: inner pad
    yields `c.level + 1`, outer pad of the resulting node yields
    `c.level + 2`. Mirrors the destructured `level_padToLevelPlus1`
    (L974) but in the consumer-friendly form `(hk : 1 ≤ c.level)`, same
    shape as `padCenter2_correct` (L636) so they chain. Closes the
    level-side of the `padCenter2` lift advertised alongside
    `wf_padCenter2`. -/
theorem level_padCenter2 (c : MacroCell) (hk : 1 ≤ c.level) :
    (padCenter2 c).level = c.level + 2 := by
  cases c with
  | leaf b =>
    -- leaves have level 0, contradicting 1 ≤ c.level
    simp only [MacroCell.level] at hk
    omega
  | node nw ne sw se =>
    show (padToLevelPlus1 (padToLevelPlus1
            (MacroCell.node nw ne sw se))).level
          = (MacroCell.node nw ne sw se).level + 2
    simp only [padToLevelPlus1, MacroCell.level, emptyOfLevel_level]
    omega

/-! ## P4 structural input: centerInLevelPlus2 level + wf

`centerInLevelPlus2 c` embeds `c` (any level `n`) in a level-`(n+2)` cell,
one copy of `c` per quadrant, the rest all-dead padding of level `n`. This
is the centering helper P4 calls before running `hashlifeResult` on the
padded cell. Its level and well-formedness are P4 structural inputs: the
level-`(n+2)` shape is what makes `box_assez_grand` + the centered
`toGrid (2^k, 2^k)` window meaningful, and the well-formedness is the
missing hypothesis of P4 (the algorithm's well-formed arm). -/

/-- `centerInLevelPlus2 c` has level `c.level + 2`: its `nw` sub-cell
    `(node e e e c)` has level `1 + e.level = 1 + c.level` (with
    `e = emptyOfLevel c.level`), so the outer node has level
    `1 + (1 + c.level)`. -/
theorem level_centerInLevelPlus2 (c : MacroCell) :
    (centerInLevelPlus2 c).level = c.level + 2 := by
  show (MacroCell.node
          (MacroCell.node (MacroCell.emptyOfLevel c.level) (MacroCell.emptyOfLevel c.level)
                          (MacroCell.emptyOfLevel c.level) c)
          (MacroCell.node (MacroCell.emptyOfLevel c.level) (MacroCell.emptyOfLevel c.level)
                          c (MacroCell.emptyOfLevel c.level))
          (MacroCell.node (MacroCell.emptyOfLevel c.level) c
                          (MacroCell.emptyOfLevel c.level) (MacroCell.emptyOfLevel c.level))
          (MacroCell.node c (MacroCell.emptyOfLevel c.level)
                          (MacroCell.emptyOfLevel c.level) (MacroCell.emptyOfLevel c.level))).level
        = c.level + 2
  simp only [MacroCell.level, emptyOfLevel_level]
  omega

/-- `centerInLevelPlus2` preserves well-formedness: from a well-formed `c`
    it produces a well-formed level-`(c.level+2)` cell. Each quadrant is
    `(node e e e c)` (or a rotation) — three wf equal-level empties plus
    `c` (wf, same level `c.level`), so all four quadrants are wf at the same
    level `1 + c.level`, and the outer node's `wf` conjunction holds. -/
theorem wf_centerInLevelPlus2 (c : MacroCell) (h : c.wf = true) :
    (centerInLevelPlus2 c).wf = true := by
  show (MacroCell.node
          (MacroCell.node (MacroCell.emptyOfLevel c.level) (MacroCell.emptyOfLevel c.level)
                          (MacroCell.emptyOfLevel c.level) c)
          (MacroCell.node (MacroCell.emptyOfLevel c.level) (MacroCell.emptyOfLevel c.level)
                          c (MacroCell.emptyOfLevel c.level))
          (MacroCell.node (MacroCell.emptyOfLevel c.level) c
                          (MacroCell.emptyOfLevel c.level) (MacroCell.emptyOfLevel c.level))
          (MacroCell.node c (MacroCell.emptyOfLevel c.level)
                          (MacroCell.emptyOfLevel c.level) (MacroCell.emptyOfLevel c.level))).wf
        = true
  simp only [MacroCell.wf, Bool.and_eq_true, beq_iff_eq]
  simp only [MacroCell.wf, Bool.and_eq_true, beq_iff_eq,
             emptyOfLevel_wf, h, MacroCell.level, emptyOfLevel_level]
  decide

/-! ## P4 structural input: step4x4 shape

`step4x4` is the Hashlife base case (level-2 input -> one generation). It
always returns a level-1 cell, unconditionally: in the `level == 2` arm it
returns `node (leaf _) (leaf _) (leaf _) (leaf _)`, and in the `else` arm it
returns `emptyOfLevel 1`. This level-1 shape is a structural input to the
`hashlifeResult` level-preservation invariant (the level-2 base of
`level_hashlifeResult_of_level_two`). The well-formedness is unconditional
too: four equal-level (level-0) leaves form a wf node, and `emptyOfLevel 1` is
wf (a node of four level-0 empty leaves). -/

private theorem level_step4x4 (c : MacroCell) : (step4x4 c).level = 1 := by
  by_cases h : c.level == 2
  · simp only [step4x4, if_pos h, MacroCell.level]
  · simp only [step4x4, if_neg h, emptyOfLevel_level]

private theorem wf_step4x4 (c : MacroCell) : (step4x4 c).wf = true := by
  by_cases h : c.level == 2
  · -- level-2 arm: node (leaf _) (leaf _) (leaf _) (leaf _). Four leaves are
    -- all wf (= true) and all level 0, so the wf conjunction is trivially true.
    simp only [step4x4, if_pos h, MacroCell.wf, MacroCell.level]
    decide
  · simp only [step4x4, if_neg h]
    exact emptyOfLevel_wf 1

/-! ## P4 structural input: level preservation (level-2 base)

`hashlifeResult` on a well-formed level-`k` cell is documented to return a
level-`(k-1)` cell (the centered `2^(k-1) × 2^(k-1)` region after `2^(k-2)`
generations). This level shape is a structural input to the P4
central-correctness assembly: both `result.toGrid (2^k, 2^k)` and the
`restrictGridTo` window presuppose the result is level-`(k+1)` (in the
level-`(k+2)` input's coordinates). The general statement
`(hashlifeResult c).level = c.level - 1` requires a strong-induction on the
double-nine recursion; the level-2 base case below is closed directly by
shape reduction to 16 leaves + definitional evaluation of `hashlifeResultAux`
(the `level == 2` arm yields `step4x4`, a `node` of four leaves → level 1). -/

/-- **Level-2 base of level-preservation**: a well-formed level-2
    `MacroCell` maps under `hashlifeResult` to a level-1 cell. -/
theorem level_hashlifeResult_of_level_two (c : MacroCell)
    (hwf : c.wf = true) (hk : c.level = 2) :
    (hashlifeResult c).level = 1 := by
  obtain ⟨a, b, d, e, rfl, ha⟩ := shape_of_level_succ c 1 hk
  obtain ⟨hwa, hwb, hwd, hwe, hlb, hld, hle⟩ := wf_node_elim hwf
  rw [ha] at hlb hld hle
  obtain ⟨a1, a2, a3, a4, rfl, ha1⟩ := shape_of_level_succ a 0 ha
  obtain ⟨b1, b2, b3, b4, rfl, hb1⟩ := shape_of_level_succ b 0 hlb
  obtain ⟨d1, d2, d3, d4, rfl, hd1⟩ := shape_of_level_succ d 0 hld
  obtain ⟨e1, e2, e3, e4, rfl, he1⟩ := shape_of_level_succ e 0 hle
  obtain ⟨_, _, _, _, hla2, hla3, hla4⟩ := wf_node_elim hwa
  obtain ⟨_, _, _, _, hlb2, hlb3, hlb4⟩ := wf_node_elim hwb
  obtain ⟨_, _, _, _, hld2, hld3, hld4⟩ := wf_node_elim hwd
  obtain ⟨_, _, _, _, hle2, hle3, hle4⟩ := wf_node_elim hwe
  rw [ha1] at hla2 hla3 hla4
  rw [hb1] at hlb2 hlb3 hlb4
  rw [hd1] at hld2 hld3 hld4
  rw [he1] at hle2 hle3 hle4
  obtain ⟨v1, rfl⟩ := shape_of_level_zero a1 ha1
  obtain ⟨v2, rfl⟩ := shape_of_level_zero a2 hla2
  obtain ⟨v3, rfl⟩ := shape_of_level_zero a3 hla3
  obtain ⟨v4, rfl⟩ := shape_of_level_zero a4 hla4
  obtain ⟨v5, rfl⟩ := shape_of_level_zero b1 hb1
  obtain ⟨v6, rfl⟩ := shape_of_level_zero b2 hlb2
  obtain ⟨v7, rfl⟩ := shape_of_level_zero b3 hlb3
  obtain ⟨v8, rfl⟩ := shape_of_level_zero b4 hlb4
  obtain ⟨v9, rfl⟩ := shape_of_level_zero d1 hd1
  obtain ⟨v10, rfl⟩ := shape_of_level_zero d2 hld2
  obtain ⟨v11, rfl⟩ := shape_of_level_zero d3 hld3
  obtain ⟨v12, rfl⟩ := shape_of_level_zero d4 hld4
  obtain ⟨v13, rfl⟩ := shape_of_level_zero e1 he1
  obtain ⟨v14, rfl⟩ := shape_of_level_zero e2 hle2
  obtain ⟨v15, rfl⟩ := shape_of_level_zero e3 hle3
  obtain ⟨v16, rfl⟩ := shape_of_level_zero e4 hle4
  -- c is now a concrete level-2 node of 16 leaves; `hashlifeResult` =
  -- `hashlifeResultAux 2 c`, the `level == 2` arm yields `step4x4 c` =
  -- `node (leaf _) (leaf _) (leaf _) (leaf _)` of level 1, by computation.
  rfl

/-- **Level-2 base of well-formedness preservation**: a well-formed level-2
    `MacroCell` maps under `hashlifeResult` to a well-formed cell. This is the
    wf sibling of `level_hashlifeResult_of_level_two`: the same 16-leaf shape
    reduction lands on `step4x4 c` (a `node` of four level-0 leaves), whose
    `.wf = true` is unconditional (`wf_step4x4`). P4 structural input: the
    wave-1 results `r_i` of the double-nine recursion must be wf so that the
    wave-2 `hashlifeResultAux` recursion does not hit its defensive
    `deadLeaf` arm (Hashlife.lean fuel-exhausted fallback). -/
theorem wf_hashlifeResult_of_level_two (c : MacroCell)
    (hwf : c.wf = true) (hk : c.level = 2) :
    (hashlifeResult c).wf = true := by
  obtain ⟨a, b, d, e, rfl, ha⟩ := shape_of_level_succ c 1 hk
  obtain ⟨hwa, hwb, hwd, hwe, hlb, hld, hle⟩ := wf_node_elim hwf
  rw [ha] at hlb hld hle
  obtain ⟨a1, a2, a3, a4, rfl, ha1⟩ := shape_of_level_succ a 0 ha
  obtain ⟨b1, b2, b3, b4, rfl, hb1⟩ := shape_of_level_succ b 0 hlb
  obtain ⟨d1, d2, d3, d4, rfl, hd1⟩ := shape_of_level_succ d 0 hld
  obtain ⟨e1, e2, e3, e4, rfl, he1⟩ := shape_of_level_succ e 0 hle
  obtain ⟨_, _, _, _, hla2, hla3, hla4⟩ := wf_node_elim hwa
  obtain ⟨_, _, _, _, hlb2, hlb3, hlb4⟩ := wf_node_elim hwb
  obtain ⟨_, _, _, _, hld2, hld3, hld4⟩ := wf_node_elim hwd
  obtain ⟨_, _, _, _, hle2, hle3, hle4⟩ := wf_node_elim hwe
  rw [ha1] at hla2 hla3 hla4
  rw [hb1] at hlb2 hlb3 hlb4
  rw [hd1] at hld2 hld3 hld4
  rw [he1] at hle2 hle3 hle4
  obtain ⟨v1, rfl⟩ := shape_of_level_zero a1 ha1
  obtain ⟨v2, rfl⟩ := shape_of_level_zero a2 hla2
  obtain ⟨v3, rfl⟩ := shape_of_level_zero a3 hla3
  obtain ⟨v4, rfl⟩ := shape_of_level_zero a4 hla4
  obtain ⟨v5, rfl⟩ := shape_of_level_zero b1 hb1
  obtain ⟨v6, rfl⟩ := shape_of_level_zero b2 hlb2
  obtain ⟨v7, rfl⟩ := shape_of_level_zero b3 hlb3
  obtain ⟨v8, rfl⟩ := shape_of_level_zero b4 hlb4
  obtain ⟨v9, rfl⟩ := shape_of_level_zero d1 hd1
  obtain ⟨v10, rfl⟩ := shape_of_level_zero d2 hld2
  obtain ⟨v11, rfl⟩ := shape_of_level_zero d3 hld3
  obtain ⟨v12, rfl⟩ := shape_of_level_zero d4 hld4
  obtain ⟨v13, rfl⟩ := shape_of_level_zero e1 he1
  obtain ⟨v14, rfl⟩ := shape_of_level_zero e2 hle2
  obtain ⟨v15, rfl⟩ := shape_of_level_zero e3 hle3
  obtain ⟨v16, rfl⟩ := shape_of_level_zero e4 hle4
  -- c is now a concrete level-2 node of 16 leaves; `hashlifeResult` =
  -- `hashlifeResultAux 2 c`, the `level == 2` arm yields `step4x4 c` =
  -- `node (leaf _) (leaf _) (leaf _) (leaf _)` of four wf level-0 leaves,
  -- whose `.wf` is `true` by reduction: wf inspects only levels (each leaf
  -- is level 0) and leaf-wf (each `true`), value-independent like the level
  -- sibling above (no GoL evaluation needed). Closes by `rfl`, mirroring
  -- `level_hashlifeResult_of_level_two`.
  rfl

/-- Exhaustive check of the P4 base case over the 16 leaf booleans of a
    (fully explicit) level-2 cell: `2^16` instances by `native_decide`. -/
private theorem p4_base_exhaustive :
    ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 : Bool,
      (hashlifeResultAux 2
          (node (node (leaf v1) (leaf v2) (leaf v3) (leaf v4))
                (node (leaf v5) (leaf v6) (leaf v7) (leaf v8))
                (node (leaf v9) (leaf v10) (leaf v11) (leaf v12))
                (node (leaf v13) (leaf v14) (leaf v15) (leaf v16)))).toGrid
        ((1 : Int), (1 : Int))
      = restrictGridTo
          (evolve 1
            ((node (node (leaf v1) (leaf v2) (leaf v3) (leaf v4))
                   (node (leaf v5) (leaf v6) (leaf v7) (leaf v8))
                   (node (leaf v9) (leaf v10) (leaf v11) (leaf v12))
                   (node (leaf v13) (leaf v14) (leaf v15) (leaf v16))).toGrid
              (0, 0)))
          1 2 := by
  native_decide

/-- **P4 base case (k = 0), in general**: the corrected statement holds
    for every well-formed level-2 cell. -/
theorem hashlifeResult_central_correct_base (c : MacroCell)
    (hwf : c.wf = true) (hk : c.level = 2) :
    (hashlifeResultAux 2 c).toGrid ((1 : Int), (1 : Int))
    = restrictGridTo (evolve 1 (c.toGrid (0, 0))) 1 2 := by
  obtain ⟨a, b, d, e, rfl, ha⟩ := shape_of_level_succ c 1 hk
  obtain ⟨hwa, hwb, hwd, hwe, hlb, hld, hle⟩ := wf_node_elim hwf
  rw [ha] at hlb hld hle
  obtain ⟨a1, a2, a3, a4, rfl, ha1⟩ := shape_of_level_succ a 0 ha
  obtain ⟨b1, b2, b3, b4, rfl, hb1⟩ := shape_of_level_succ b 0 hlb
  obtain ⟨d1, d2, d3, d4, rfl, hd1⟩ := shape_of_level_succ d 0 hld
  obtain ⟨e1, e2, e3, e4, rfl, he1⟩ := shape_of_level_succ e 0 hle
  obtain ⟨_, _, _, _, hla2, hla3, hla4⟩ := wf_node_elim hwa
  obtain ⟨_, _, _, _, hlb2, hlb3, hlb4⟩ := wf_node_elim hwb
  obtain ⟨_, _, _, _, hld2, hld3, hld4⟩ := wf_node_elim hwd
  obtain ⟨_, _, _, _, hle2, hle3, hle4⟩ := wf_node_elim hwe
  rw [ha1] at hla2 hla3 hla4
  rw [hb1] at hlb2 hlb3 hlb4
  rw [hd1] at hld2 hld3 hld4
  rw [he1] at hle2 hle3 hle4
  obtain ⟨v1, rfl⟩ := shape_of_level_zero a1 ha1
  obtain ⟨v2, rfl⟩ := shape_of_level_zero a2 hla2
  obtain ⟨v3, rfl⟩ := shape_of_level_zero a3 hla3
  obtain ⟨v4, rfl⟩ := shape_of_level_zero a4 hla4
  obtain ⟨v5, rfl⟩ := shape_of_level_zero b1 hb1
  obtain ⟨v6, rfl⟩ := shape_of_level_zero b2 hlb2
  obtain ⟨v7, rfl⟩ := shape_of_level_zero b3 hlb3
  obtain ⟨v8, rfl⟩ := shape_of_level_zero b4 hlb4
  obtain ⟨v9, rfl⟩ := shape_of_level_zero d1 hd1
  obtain ⟨v10, rfl⟩ := shape_of_level_zero d2 hld2
  obtain ⟨v11, rfl⟩ := shape_of_level_zero d3 hld3
  obtain ⟨v12, rfl⟩ := shape_of_level_zero d4 hld4
  obtain ⟨v13, rfl⟩ := shape_of_level_zero e1 he1
  obtain ⟨v14, rfl⟩ := shape_of_level_zero e2 hle2
  obtain ⟨v15, rfl⟩ := shape_of_level_zero e3 hle3
  obtain ⟨v16, rfl⟩ := shape_of_level_zero e4 hle4
  exact p4_base_exhaustive v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
    v15 v16

/-! ## P4 inductive step — scaffolding for the double-nine decomposition

The sorry at `p4_ext_bridge c (k+1) (fun p => by sorry)` is the **research-level
verrou** of the whole module. It demands the pointwise membership biconditional:

    ∀ p, p ∈ (hashlifeResultAux (k+2) c).toGrid (2^k, 2^k)
         ↔ p ∈ restrictGridTo (evolve (2^k) (c.toGrid (0,0))) (2^k) (2^(k+1))

`p4_ext_bridge` (proven) reduces list-equality to this biconditional, so once
the biconditional is discharged, `hashlifeResult_central_correct` closes by
induction. The function `p4_succ_membership` below is the **single named
entry point** that gathers the four sub-lemmas; each sub-lemma is an
independent, difficulty-ranked prover target (grignotable one-per-session).

### Proof plan (the double-nine, two half-steps)

`hashlifeResultAux (k+3) c` on a well-formed level-`(k+2)` cell `c` unfolds
(via the structural-recursion pattern at `Hashlife.lean`) to:

  **Wave 1** — nine overlapping level-`(k+1)` sub-cells `n1..n9`, each recursed
  to a level-`k` result `r1..r9` that is `2^(k-1)` generations ahead (by IH).
  **Wave 2** — four overlapping level-`(k+1)` super-cells `q_nw..q_se` (built
  from the `r_i`), each recursed to a level-`k` result `out_*` that is another
  `2^(k-1)` generations ahead. The two half-steps compose to `2^k` generations,
  matching `evolve (2^k)` — this is the light-cone argument (P2) applied twice.

### Sub-lemmas (difficulty-ranked, each `grignotable` independently)

| Lemma | Difficulty | What it proves |
|-------|-----------|----------------|
| `p4_double_nine_shape`     | P4.1 (structural) | The 9 sub-cells `n_i` tile `c` and each has level `k+1` + is wf |
| `p4_wave1_ih`              | P4.2 (IH application) | Each `r_i = hashlifeResultAux (k+1) n_i` matches `evolve 2^(k-1)` on the `n_i` window (by IH at level `k`) |
| `p4_wave2_ih`              | P4.3 (IH application) | Each `out_* = hashlifeResultAux (k+1) q_*` matches `evolve 2^(k-1)` on the `q_*` window (by IH at level `k`) |
| ~~`p4_half_steps_compose`~~ | P4.4 (compositional) — **SUBSUMED** | The pure `evolve` half-step composition is `evolve_add` (L2353) + `evolve_half_step` (L2370), both proven sorry-free; the wave-assembly obligation is carried by the residual `sorry` of `p4_succ_membership`. The standalone `: True` placeholder theorem was deleted (N2-bis) as a vacuous dup of an already-closed obligation |

Once all four are proven, `p4_succ_membership` glues them. The ordering
P4.1 → P4.2 → P4.3 → P4.4 reflects dependency: P4.2/P4.3 need P4.1's shape
facts, P4.4 needs P4.2/P4.3. Each is **self-contained**: a session can
eliminate one without re-deriving the others.

See `agent_tests/prover/RUNBOOK.md` for the iteration protocol. -/

/-- **P4.1** (structural half, PROVEN): a well-formed level-`(k+2)` MacroCell
    decomposes into sixteen depth-2 grandchildren `nw_nw..se_se`, each of level
    `k` and well-formed. This is exactly the shape precondition
    `hashlifeResultAux`'s double-nine pattern match relies on: the nine sub-cells
    `n1..n9` of `Hashlife.lean` are each `node`s of four such grandchildren, so
    combined with `node_wf_level_of_four` this discharges every `n_i`'s
    `level = k + 1 ∧ wf = true`.

    The signature `(c : MacroCell)` is preserved so the `p4_succ_membership`
    glue (L1490) typechecks unchanged; the conclusion is the depth-2 existential
    decomposition plus the sixteen `level = k ∧ wf = true` facts, which is
    precisely `wf_node_depth2_grandchildren`'s output. The **geometric half**
    of P4.1 — that the `n_i` union tiles `c`'s live region (a statement on
    `toGrid`/`restrictGridTo` overlap, not just shape) — is genuinely
    non-structural and stays open (research-level, queueable behind the
    `step_light_cone` P2 machinery). -/
theorem p4_double_nine_shape
    (c : MacroCell) (k : Nat) (hwf : c.wf = true) (hk : c.level = k + 2) :
    ∃ nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
       sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell,
      c = node (node nw_nw nw_ne nw_sw nw_se)
               (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se)
               (node se_nw se_ne se_sw se_se) ∧
      nw_nw.level = k ∧ nw_nw.wf = true ∧
      nw_ne.level = k ∧ nw_ne.wf = true ∧
      nw_sw.level = k ∧ nw_sw.wf = true ∧
      nw_se.level = k ∧ nw_se.wf = true ∧
      ne_nw.level = k ∧ ne_nw.wf = true ∧
      ne_ne.level = k ∧ ne_ne.wf = true ∧
      ne_sw.level = k ∧ ne_sw.wf = true ∧
      ne_se.level = k ∧ ne_se.wf = true ∧
      sw_nw.level = k ∧ sw_nw.wf = true ∧
      sw_ne.level = k ∧ sw_ne.wf = true ∧
      sw_sw.level = k ∧ sw_sw.wf = true ∧
      sw_se.level = k ∧ sw_se.wf = true ∧
      se_nw.level = k ∧ se_nw.wf = true ∧
      se_ne.level = k ∧ se_ne.wf = true ∧
      se_sw.level = k ∧ se_sw.wf = true ∧
      se_se.level = k ∧ se_se.wf = true := by
  -- depth-1: c = node nw ne sw se with nw.level = k + 1
  obtain ⟨nw, ne, sw, se, rfl, hnw_lvl⟩ := shape_of_level_succ c (k + 1) hk
  obtain ⟨hnw, hne, hsw, hse, hne_eq, hsw_eq, hse_eq⟩ := wf_node_elim hwf
  -- siblings share nw's level
  have hne_lvl : ne.level = k + 1 := hne_eq ▸ hnw_lvl
  have hsw_lvl : sw.level = k + 1 := hsw_eq ▸ hnw_lvl
  have hse_lvl : se.level = k + 1 := hse_eq ▸ hnw_lvl
  -- depth-2: each quadrant is a node of four grandchildren
  obtain ⟨nw_nw, nw_ne, nw_sw, nw_se, rfl, _⟩ := shape_of_level_succ nw k hnw_lvl
  obtain ⟨ne_nw, ne_ne, ne_sw, ne_se, rfl, _⟩ := shape_of_level_succ ne k hne_lvl
  obtain ⟨sw_nw, sw_ne, sw_sw, sw_se, rfl, _⟩ := shape_of_level_succ sw k hsw_lvl
  obtain ⟨se_nw, se_ne, se_sw, se_se, rfl, _⟩ := shape_of_level_succ se k hse_lvl
  refine ⟨nw_nw, nw_ne, nw_sw, nw_se, ne_nw, ne_ne, ne_sw, ne_se,
          sw_nw, sw_ne, sw_sw, sw_se, se_nw, se_ne, se_sw, se_se, rfl, ?_⟩
  exact wf_node_depth2_grandchildren
    nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
    sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se k hk hwf

/-- Clean-context level helper (c.142). Computes the level of the double-nine
    outer node from its 16 grandchildren (level `n-2`) as a single arithmetic
    fact, so the pos arm of the preservation step helper does not whnf
    `(node …).level`'s type in the 32-fact context. -/
private theorem node16_level (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell) (n : Nat)
    (hn2 : 2 ≤ n) (h : nw_nw.level = n - 2) :
    (node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
          (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).level = n := by
  show 1 + (1 + nw_nw.level) = n
  omega

/-- **P4.4 assembly grain (c.156).** In a CLEAN context (the 16 grandchildren as
    opaque binders + one level hypothesis), the `hashlifeResultAux_succ_node`
    if-condition `(node16).level == 2` is false for `k ≥ 1` (the node level is
    `k + 2 ≥ 3`). Proven standalone because stating/rewriting `(node16).level`
    INLINE inside `p4_succ_membership`'s rich context (post `_h1`/`_h2`/`_h3`
    obtain of 16 gc's) whnf-diverges (the c.142 pathology). Applying this helper
    there keeps the level term inferred, never re-elaborated — the opaque-binder
    pattern of c.139/c.143. -/
private theorem node16_level_ne_two (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (hnw : nw_nw.level = k) :
    ¬ ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
             (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).level == 2) := by
  -- Mirror the working pos-arm discharge at L1810-1815: `beq_iff_eq` converts the
  -- `==` (Nat.beq) to `=`, then omega finds k+2 = 2 contradicts k >= 1.
  intro heq
  have hnode := node16_level nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
               sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se (k + 2) (by omega) (by omega)
  rw [hnode] at heq
  have hn2 : k + 2 = 2 := by simpa [beq_iff_eq] using heq
  omega

/-- Apply the level/`cellWf` IH to a `node` of four level-`(n-2)` `cellWf` cells
    (c.142 workhorse), for BOTH wave layers of the preservation lemma: wave-1
    (the nine `n_i`, each a `node` of four grandchildren) and wave-2 (the four
    `q_*`, each a `node` of four wave-1 results `r_i`). Clean context (four
    cells as opaque binders) avoids the whnf divergence an inline `ih`
    application hits in the step helper's rich context (c.139 pattern). -/
private theorem cellWf_quad (n : Nat) (hn3 : 3 ≤ n)
    (ih : ∀ (m : Nat), m < n → ∀ (c' : MacroCell), cellWf c' → c'.level = m → 2 ≤ m →
            ((hashlifeResultAux m c').level = m - 1 ∧ cellWf (hashlifeResultAux m c')))
    (g1 g2 g3 g4 : MacroCell)
    (hg1 : g1.level = n - 2) (hg2 : g2.level = n - 2)
    (hg3 : g3.level = n - 2) (hg4 : g4.level = n - 2)
    (hw1 : cellWf g1) (hw2 : cellWf g2) (hw3 : cellWf g3) (hw4 : cellWf g4) :
    ((hashlifeResultAux (n - 1) (node g1 g2 g3 g4)).level = n - 2 ∧
     cellWf (hashlifeResultAux (n - 1) (node g1 g2 g3 g4))) := by
  have hqwf : cellWf (node g1 g2 g3 g4) :=
    cellWf.node hw1 hw2 hw3 hw4 (by omega) (by omega) (by omega)
  have hqlvl : (node g1 g2 g3 g4).level = n - 1 := by show 1 + g1.level = n - 1; omega
  exact ih (n - 1) (by omega) (node g1 g2 g3 g4) hqwf hqlvl (by omega)

/-- Clean-context conjunct-closer (c.142, c.139 pattern). Closes the level AND
    `cellWf` conjuncts of a `node` of four wave-2 results `out_*`, with the four
    cells as OPAQUE binders. Inside, `out_nw.level` etc. are atoms to `omega`
    (no whnf), so the level conjunct closes; `cellWf.node` constructor closes the
    `cellWf` conjunct syntactically. This isolation is required because closing
    these conjuncts INLINE in the step helper (where `out_*` are spelled-out
    `hashlifeResultAux` terms) makes `omega`/`rw` `whnf`-normalize
    `(hashlifeResultAux (n-1) q_*)`.level` recursively → divergent (c.142 Exp1-3). -/
private theorem node_level_cellWf_conjuncts (n : Nat) (hn3 : 3 ≤ n)
    (out_nw out_ne out_sw out_se : MacroCell)
    (hnw : out_nw.level = n - 2) (hne : out_ne.level = n - 2)
    (hsw : out_sw.level = n - 2) (hse : out_se.level = n - 2)
    (hw_nw : cellWf out_nw) (hw_ne : cellWf out_ne)
    (hw_sw : cellWf out_sw) (hw_se : cellWf out_se) :
    (node out_nw out_ne out_sw out_se).level = n - 1 ∧
    cellWf (node out_nw out_ne out_sw out_se) := by
  refine ⟨?_, ?_⟩
  · show 1 + out_nw.level = n - 1; omega
  · exact cellWf.node hw_nw hw_ne hw_sw hw_se (by omega) (by omega) (by omega)

/-- Step helper for `hashlifeResultAux_level_cellWf` (c.142). Unfolds the
    double-nine recursive arm of `hashlifeResultAux` in the clean-probe context,
    builds the wave-1 results `r_i` and wave-2 results `out_*` via `cellWf_quad`,
    and closes both conjuncts. The `cellWf` conclusion (opaque to defeq) is what
    makes the wf conjunct closeable — the transparent `.wf` version diverges on
    whnf for the nested `hashlifeResultAux` results (c.140, 8M heartbeats). -/
private theorem hashlifeResultAux_level_cellWf_step (n : Nat) (hn3 : 3 ≤ n)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (hgrands : nw_nw.level = n - 2 ∧ nw_nw.wf = true ∧
               nw_ne.level = n - 2 ∧ nw_ne.wf = true ∧
               nw_sw.level = n - 2 ∧ nw_sw.wf = true ∧
               nw_se.level = n - 2 ∧ nw_se.wf = true ∧
               ne_nw.level = n - 2 ∧ ne_nw.wf = true ∧
               ne_ne.level = n - 2 ∧ ne_ne.wf = true ∧
               ne_sw.level = n - 2 ∧ ne_sw.wf = true ∧
               ne_se.level = n - 2 ∧ ne_se.wf = true ∧
               sw_nw.level = n - 2 ∧ sw_nw.wf = true ∧
               sw_ne.level = n - 2 ∧ sw_ne.wf = true ∧
               sw_sw.level = n - 2 ∧ sw_sw.wf = true ∧
               sw_se.level = n - 2 ∧ sw_se.wf = true ∧
               se_nw.level = n - 2 ∧ se_nw.wf = true ∧
               se_ne.level = n - 2 ∧ se_ne.wf = true ∧
               se_sw.level = n - 2 ∧ se_sw.wf = true ∧
               se_se.level = n - 2 ∧ se_se.wf = true)
    (ih : ∀ (m : Nat), m < n → ∀ (c' : MacroCell), cellWf c' → c'.level = m → 2 ≤ m →
            ((hashlifeResultAux m c').level = m - 1 ∧ cellWf (hashlifeResultAux m c'))) :
    ((hashlifeResultAux n
        (node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
              (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se))).level = n - 1 ∧
     cellWf (hashlifeResultAux n
        (node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
              (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)))) := by
  obtain ⟨hnw_nw_l, hnw_nw_w, hnw_ne_l, hnw_ne_w, hnw_sw_l, hnw_sw_w, hnw_se_l, hnw_se_w,
          hne_nw_l, hne_nw_w, hne_ne_l, hne_ne_w, hne_sw_l, hne_sw_w, hne_se_l, hne_se_w,
          hsw_nw_l, hsw_nw_w, hsw_ne_l, hsw_ne_w, hsw_sw_l, hsw_sw_w, hsw_se_l, hsw_se_w,
          hse_nw_l, hse_nw_w, hse_ne_l, hse_ne_w, hse_sw_l, hse_sw_w, hse_se_l, hse_se_w⟩ := hgrands
  rw [show n = (n - 1) + 1 from by omega]
  by_cases heq : (node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
                     (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).level == 2
  · -- pos arm: node level == 2, but 16 grandchildren level (n-2) give node level n ≥ 3.
    have hnode := node16_level nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
                 sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se n (by omega) hnw_nw_l
    rw [hnode] at heq
    have hn2 : n = 2 := by simpa [beq_iff_eq] using heq
    exfalso; omega
  · -- neg arm: the recursive double-nine body.
    simp only [MacroCell.level] at heq
    have hr1 := cellWf_quad n hn3 ih nw_nw nw_ne nw_sw nw_se
                   hnw_nw_l hnw_ne_l hnw_sw_l hnw_se_l
                   (cellWf_of_wf _ hnw_nw_w) (cellWf_of_wf _ hnw_ne_w)
                   (cellWf_of_wf _ hnw_sw_w) (cellWf_of_wf _ hnw_se_w)
    have hr2 := cellWf_quad n hn3 ih nw_ne ne_nw nw_se ne_sw
                   hnw_ne_l hne_nw_l hnw_se_l hne_sw_l
                   (cellWf_of_wf _ hnw_ne_w) (cellWf_of_wf _ hne_nw_w)
                   (cellWf_of_wf _ hnw_se_w) (cellWf_of_wf _ hne_sw_w)
    have hr3 := cellWf_quad n hn3 ih ne_nw ne_ne ne_sw ne_se
                   hne_nw_l hne_ne_l hne_sw_l hne_se_l
                   (cellWf_of_wf _ hne_nw_w) (cellWf_of_wf _ hne_ne_w)
                   (cellWf_of_wf _ hne_sw_w) (cellWf_of_wf _ hne_se_w)
    have hr4 := cellWf_quad n hn3 ih nw_sw nw_se sw_nw sw_ne
                   hnw_sw_l hnw_se_l hsw_nw_l hsw_ne_l
                   (cellWf_of_wf _ hnw_sw_w) (cellWf_of_wf _ hnw_se_w)
                   (cellWf_of_wf _ hsw_nw_w) (cellWf_of_wf _ hsw_ne_w)
    have hr5 := cellWf_quad n hn3 ih nw_se ne_sw sw_ne se_nw
                   hnw_se_l hne_sw_l hsw_ne_l hse_nw_l
                   (cellWf_of_wf _ hnw_se_w) (cellWf_of_wf _ hne_sw_w)
                   (cellWf_of_wf _ hsw_ne_w) (cellWf_of_wf _ hse_nw_w)
    have hr6 := cellWf_quad n hn3 ih ne_sw ne_se se_nw se_ne
                   hne_sw_l hne_se_l hse_nw_l hse_ne_l
                   (cellWf_of_wf _ hne_sw_w) (cellWf_of_wf _ hne_se_w)
                   (cellWf_of_wf _ hse_nw_w) (cellWf_of_wf _ hse_ne_w)
    have hr7 := cellWf_quad n hn3 ih sw_nw sw_ne sw_sw sw_se
                   hsw_nw_l hsw_ne_l hsw_sw_l hsw_se_l
                   (cellWf_of_wf _ hsw_nw_w) (cellWf_of_wf _ hsw_ne_w)
                   (cellWf_of_wf _ hsw_sw_w) (cellWf_of_wf _ hsw_se_w)
    have hr8 := cellWf_quad n hn3 ih sw_ne se_nw sw_se se_sw
                   hsw_ne_l hse_nw_l hsw_se_l hse_sw_l
                   (cellWf_of_wf _ hsw_ne_w) (cellWf_of_wf _ hse_nw_w)
                   (cellWf_of_wf _ hsw_se_w) (cellWf_of_wf _ hse_sw_w)
    have hr9 := cellWf_quad n hn3 ih se_nw se_ne se_sw se_se
                   hse_nw_l hse_ne_l hse_sw_l hse_se_l
                   (cellWf_of_wf _ hse_nw_w) (cellWf_of_wf _ hse_ne_w)
                   (cellWf_of_wf _ hse_sw_w) (cellWf_of_wf _ hse_se_w)
    -- Wave 2: q_* = node of four r_i; out_* = hRA (n-1) q_*.
    have honw := cellWf_quad n hn3 ih (hashlifeResultAux (n - 1) (node nw_nw nw_ne nw_sw nw_se))
                           (hashlifeResultAux (n - 1) (node nw_ne ne_nw nw_se ne_sw))
                           (hashlifeResultAux (n - 1) (node nw_sw nw_se sw_nw sw_ne))
                           (hashlifeResultAux (n - 1) (node nw_se ne_sw sw_ne se_nw))
                           hr1.1 hr2.1 hr4.1 hr5.1 hr1.2 hr2.2 hr4.2 hr5.2
    have hone := cellWf_quad n hn3 ih (hashlifeResultAux (n - 1) (node nw_ne ne_nw nw_se ne_sw))
                           (hashlifeResultAux (n - 1) (node ne_nw ne_ne ne_sw ne_se))
                           (hashlifeResultAux (n - 1) (node nw_se ne_sw sw_ne se_nw))
                           (hashlifeResultAux (n - 1) (node ne_sw ne_se se_nw se_ne))
                           hr2.1 hr3.1 hr5.1 hr6.1 hr2.2 hr3.2 hr5.2 hr6.2
    have hosw := cellWf_quad n hn3 ih (hashlifeResultAux (n - 1) (node nw_sw nw_se sw_nw sw_ne))
                           (hashlifeResultAux (n - 1) (node nw_se ne_sw sw_ne se_nw))
                           (hashlifeResultAux (n - 1) (node sw_nw sw_ne sw_sw sw_se))
                           (hashlifeResultAux (n - 1) (node sw_ne se_nw sw_se se_sw))
                           hr4.1 hr5.1 hr7.1 hr8.1 hr4.2 hr5.2 hr7.2 hr8.2
    have hose := cellWf_quad n hn3 ih (hashlifeResultAux (n - 1) (node nw_se ne_sw sw_ne se_nw))
                           (hashlifeResultAux (n - 1) (node ne_sw ne_se se_nw se_ne))
                           (hashlifeResultAux (n - 1) (node sw_ne se_nw sw_se se_sw))
                           (hashlifeResultAux (n - 1) (node se_nw se_ne se_sw se_se))
                           hr5.1 hr6.1 hr8.1 hr9.1 hr5.2 hr6.2 hr8.2 hr9.2
    -- Unfold hRA's recursive arm now that the wave facts are established.
    simp only [hashlifeResultAux, if_neg heq, MacroCell.level]
    exact node_level_cellWf_conjuncts n hn3 _ _ _ _
        honw.1 hone.1 hosw.1 hose.1 honw.2 hone.2 hosw.2 hose.2

/-- **(c.142) Level + well-formedness preservation of `hashlifeResultAux`**,
    over the OPAQUE `cellWf` predicate. For `2 ≤ L` and a well-formed level-`L`
    cell, `hashlifeResultAux L c` is well-formed and level `L - 1`.

    This is the gate for P4.3 (and the wave-2 layer of the lane): wave-2
    super-cells `q_*` are built from `hashlifeResultAux` RESULTS `r_i`, so
    instantiating the central-correctness IH on `q_*` requires `r_i`'s level
    and well-formedness — which only this lemma provides. c.140 proved the
    transparent `.wf` version diverges on whnf (8M heartbeats); the opaque
    `cellWf` conclusion breaks that defeq divergence. -/
theorem hashlifeResultAux_level_cellWf :
    ∀ (L : Nat) (c : MacroCell), cellWf c → c.level = L → 2 ≤ L →
      ((hashlifeResultAux L c).level = L - 1 ∧ cellWf (hashlifeResultAux L c)) := by
  intro L
  induction L using Nat.strongRecOn with
  | ind n ih =>
    intro c hwf hc hn2
    by_cases h2 : n = 2
    · subst h2
      refine ⟨?_, ?_⟩
      · have hdef : hashlifeResultAux 2 c = hashlifeResult c := by
          show hashlifeResultAux 2 c = hashlifeResultAux c.level c
          rw [hc]
        rw [hdef]
        exact level_hashlifeResult_of_level_two c (wf_of_cellWf hwf) hc
      · have hdef : hashlifeResultAux 2 c = hashlifeResult c := by
          show hashlifeResultAux 2 c = hashlifeResultAux c.level c
          rw [hc]
        rw [hdef]
        exact cellWf_of_wf _ (wf_hashlifeResult_of_level_two c (wf_of_cellWf hwf) hc)
    · have hn3 : 3 ≤ n := by omega
      have hk' : c.level = (n - 2) + 2 := by omega
      obtain ⟨nw_nw, nw_ne, nw_sw, nw_se, ne_nw, ne_ne, ne_sw, ne_se,
              sw_nw, sw_ne, sw_sw, sw_se, se_nw, se_ne, se_sw, se_se, rfl, hgrands⟩ :=
        p4_double_nine_shape c (n - 2) (wf_of_cellWf hwf) hk'
      exact hashlifeResultAux_level_cellWf_step n hn3
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se hgrands ih

/-- The central-correctness statement, abstracted as a named predicate.
    Quoting it as `centralCorrect c j` (instead of the unfolded `2^j`-indexed
    Grid equality) stops the elaborator from running `whnf` on
    `hashlifeResultAux (j+2) c.toGrid` while checking the `ih` argument type of
    `p4_wave1_ih`; that reduction diverges (it pattern-matches `c`, a free
    variable). Unlike the c.138 `@[irreducible]` variant, a plain `def` still
    allows defeq at the `hashlifeResult_central_correct` -> `p4_succ_membership`
    threading boundary (c.139). -/
def centralCorrect (c : MacroCell) (j : Nat) : Prop :=
  (hashlifeResultAux (j + 2) c).toGrid ((2^j : Nat), (2^j : Nat)) =
    restrictGridTo (evolve (2^j) (c.toGrid (0, 0))) (2^j : Int) (2^(j+1))

/-- **The whnf-wall bypass (4th abstraction technique, c.153).**

    `centralCorrect c j` is a *grid equality*. To reason about pointwise
    membership `p ∈ (hashlifeResultAux (j+2) c).toGrid off` WITHOUT whnf-reducing
    the `hashlifeResultAux` term (the wall that blocked c.138–c.140), apply
    `p ∈ ·` to both sides of the equality by **congruence** (`congrArg`), then
    `Iff.of_eq`. This substitutes the `hashlifeResultAux` term *syntactically* —
    it is never unfolded. The four previous techniques (opaque-binder helper
    c.139, `inductive cellWf` c.142, plain `def centralCorrect` c.139,
    `set m := k-1` c.147) all work *around* the wall by hiding hRA behind an
    opaque binder; this one crosses it by congruence, which is exactly what
    G2/G3 need (they must inspect the *membership* of the composed result, not
    just its level/wf).

    Instantiated with `mem_restrictGridTo`, this is the **G1 reduction**
    (membership of a sub-cell whose `centralCorrect` is known, e.g. `q_j` via
    `ih`) in one sorry-free step. The residual wall is **G3 assembly** (how
    `(hashlifeResultAux (k+2) c).toGrid off` decomposes into the four
    `(hashlifeResultAux (k+1) q_j).toGrid off_j` — the `toCellsAux` walk on an
    `hRA` that unfolds), which remains to be bridged. This lemma is the
    `p4_succ_membership` analogue of the P4.3 gate lemma (`hashlifeResultAux_
    level_cellWf`, c.142): sorry-stable infrastructure that unlocks the next
    attack. -/
theorem centralCorrect_mem (c : MacroCell) (j : Nat) (p : Int × Int)
    (h : centralCorrect c j) :
    p ∈ (hashlifeResultAux (j + 2) c).toGrid ((2^j : Nat), (2^j : Nat)) ↔
      isAlive (evolve (2^j) (c.toGrid (0, 0))) p = true ∧
      (2^j : Int) ≤ p.1 ∧ p.1 < (2^j : Int) + 2^(j+1) ∧
      (2^j : Int) ≤ p.2 ∧ p.2 < (2^j : Int) + 2^(j+1) := by
  have hb : p ∈ (hashlifeResultAux (j + 2) c).toGrid ((2^j : Nat), (2^j : Nat)) ↔
      p ∈ restrictGridTo (evolve (2^j) (c.toGrid (0, 0))) (2^j : Int) (2^(j+1)) :=
    Iff.of_eq (congrArg (fun g : Grid => p ∈ g) h)
  rw [hb, mem_restrictGridTo]
  refine ⟨fun ⟨Hm, h1, h2, h3, h4⟩ => ⟨?_, h1, h2, h3, h4⟩,
          fun ⟨H, h1, h2, h3, h4⟩ => ⟨?_, h1, h2, h3, h4⟩⟩ <;>
    simp_all [isAlive]

/-- **Offset-generalized centralCorrect membership** (P4.4 offset-matching G2 gate).

    `centralCorrect_mem` characterizes membership of a cell's result at its
    *canonical* centered offset `(2^j, 2^j)`. The P4.4 offset-matching assembly
    needs the same characterization at the **quadrant offsets** where the
    super-cells `q_*` actually sit in the parent result node (e.g. NW quadrant at
    `(2^k, 2^k)`, per `mem_toGrid_node`). This lemma re-anchors
    `centralCorrect_mem` from `(2^j, 2^j)` to an arbitrary offset `(a, b)` via
    `toGrid_shift_between`: the alive-status is evaluated at the back-shifted
    point `(p.1 - a + 2^j, p.2 - b + 2^j)`, and the centered window bounds
    `[2^j, 2^j + 2^(j+1))` translate to `[a, a + 2^(j+1))` (and `[b, b + 2^(j+1))`).

    Pure composition of `centralCorrect_mem` (G2 congruence, c.153) and
    `toGrid_shift_between` (#4797, the double-shift ingredient) — sorry-free gate
    ingredient. `evolve_half_step` (proven sorry-free) consumes this gate to fold
    the half-step `2^k = 2^(k-1) ∘ 2^(k-1)`; the residual research heart is the
    **G3 wave-assembly** — how `(hashlifeResultAux (k+2) parent)` decomposes into
    the four `(hashlifeResultAux (k+1) q_j)` sub-results at the quadrant offsets —
    carried by the `sorry` of `p4_nw_supercell_agree` (the NW supercell root). -/
theorem centralCorrect_mem_shift (c : MacroCell) (j : Nat) (a b : Int) (p : Int × Int)
    (h : centralCorrect c j) :
    p ∈ (hashlifeResultAux (j + 2) c).toGrid (a, b) ↔
      isAlive (evolve (2^j) (c.toGrid (0, 0)))
        (p.1 - a + (2^j : Int), p.2 - b + (2^j : Int)) = true ∧
      a ≤ p.1 ∧ p.1 < a + 2^(j+1) ∧
      b ≤ p.2 ∧ p.2 < b + 2^(j+1) := by
  -- Re-anchor `(a,b)` → the canonical `(2^j,2^j)` offset. `centralCorrect_mem`'s
  -- canonical offset is the Nat-cast `↑(2^j)` (the display of `(2^j : Nat)`
  -- coerced to Int), so we instantiate `toGrid_shift_between` with
  -- `a' = b' = (2^j : Nat)` to match its rewrite pattern (native `(2^j : Int)`
  -- would not unify — the c.146/c.147 native-Int-vs-Nat-cast distinction).
  have hshift : p ∈ (hashlifeResultAux (j + 2) c).toGrid (a, b) ↔
      (p.1 - a + (2^j : Nat), p.2 - b + (2^j : Nat)) ∈
        (hashlifeResultAux (j + 2) c).toGrid ((2^j : Nat), (2^j : Nat)) :=
    toGrid_shift_between
  rw [hshift, centralCorrect_mem c j _ h]
  -- `centralCorrect_mem`'s bounds carry native `(2^j : Int)` literals, while the
  -- substituted point carries `↑(2^j)` (Nat-cast). Normalize to a single atom
  -- (c.146: linarith otherwise sees `↑(2^j)` and `(2^j : Int)` as unrelated).
  rw [show ((2 : Nat)^j).cast = (2^j : Int) from Nat.cast_pow 2 j]
  refine ⟨fun ⟨H, h1, h2, h3, h4⟩ => ⟨H, ?_, ?_, ?_, ?_⟩,
          fun ⟨H, h1, h2, h3, h4⟩ => ⟨H, ?_, ?_, ?_, ?_⟩⟩ <;> linarith

/-- **P4.2 helper (c.139 workaround).** The `ih` *application*
    `ih (node nw_se ne_sw sw_ne se_nk) (k-1) ...` diverges on `whnf` when it
    appears inline inside `p4_wave1_ih`'s body, because there the four
    grandchildren are free variables tied into a 16-grandchild / 32-fact local
    context (post `p4_double_nine_shape` obtain). Moving the application into
    this standalone helper makes `nw_se` etc. opaque binders at the application
    site, which is enough to stop the divergence (minimal-repro probe
    `WhnfProbe.lean`, arm 4 diverges / arm 6 compiles). -/
private theorem p4_wave1_ih_step
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_se ne_sw sw_ne se_nw : MacroCell)
    (hnw_se_l : nw_se.level = k) (hne_sw_l : ne_sw.level = k)
    (hsw_ne_l : sw_ne.level = k) (hse_nw_l : se_nw.level = k)
    (hnw_se_w : nw_se.wf = true) (hne_sw_w : ne_sw.wf = true)
    (hsw_ne_w : sw_ne.wf = true) (hse_nw_w : se_nw.wf = true)
    (ih : ∀ (c' : MacroCell) (j : Nat), j < k → c'.wf = true → c'.level = j + 2 →
      centralCorrect c' j) :
    centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1) := by
  have hn5 := node_wf_level_of_four hnw_se_l hne_sw_l hsw_ne_l hse_nw_l
                                    hnw_se_w hne_sw_w hsw_ne_w hse_nw_w
  exact ih (node nw_se ne_sw sw_ne se_nw) (k - 1) (by omega) hn5.2 (by omega)

/-- **P4.3 helper (c.142/c.139 pattern).** Wave-1 result facts for one sub-cell
    `n` (a double-nine `n_i`): `n`'s level-`(k+1)` well-formedness yields, via the
    proven preservation lemma `hashlifeResultAux_level_cellWf`, that the wave-1
    result `hashlifeResultAux (k+1) n` has level `k` and `cellWf`. `n` is an
    OPAQUE binder here so the `hashlifeResultAux` term in the conclusion does not
    whnf-reduce (calling the preservation lemma inline, with `n` spelled out as a
    `node` of grandchildren, makes the elaborator whnf the conclusion's nested
    `hashlifeResultAux` term — divergent). -/
private theorem wave1_result_facts (k : Nat) (hk1 : 1 ≤ k) (n : MacroCell)
    (hn_wf : n.wf = true) (hn_lvl : n.level = k + 1) :
    (hashlifeResultAux (k + 1) n).level = k ∧ cellWf (hashlifeResultAux (k + 1) n) := by
  have hcn := cellWf_of_wf n hn_wf
  exact hashlifeResultAux_level_cellWf (k + 1) n hcn hn_lvl (by omega)

/-- **P4.3 helper (wave 2).** The `ih` *application*
    `ih (node r1 r2 r4 r5) (k - 1) ...` for the NW super-cell `q_nw`
    (`= node r1 r2 r4 r5`, the four wave-1 results `r_i`), done in a standalone
    helper so the four `r_i` are opaque binders at the application site —
    same whnf-isolation pattern as `p4_wave1_ih_step` (c.139). The `r_i` are
    `hashlifeResultAux` results whose level (`k`) and `cellWf` are established
    by the proven preservation lemma `hashlifeResultAux_level_cellWf` (c.142),
    then bridged to `.wf = true` for the central-correctness `ih` (which is on
    `.wf`). `q_nw` is taken as representative (the three other super-cells are
    isomorphic, queued). -/
private theorem p4_wave2_ih_step
    (k : Nat) (hk1 : 1 ≤ k)
    (r1 r2 r4 r5 : MacroCell)
    (hr1_l : r1.level = k) (hr2_l : r2.level = k)
    (hr4_l : r4.level = k) (hr5_l : r5.level = k)
    (hr1_w : r1.wf = true) (hr2_w : r2.wf = true)
    (hr4_w : r4.wf = true) (hr5_w : r5.wf = true)
    (ih : ∀ (c' : MacroCell) (j : Nat), j < k → c'.wf = true → c'.level = j + 2 →
      centralCorrect c' j) :
    centralCorrect (node r1 r2 r4 r5) (k - 1) := by
  have hq := node_wf_level_of_four hr1_l hr2_l hr4_l hr5_l
                                    hr1_w hr2_w hr4_w hr5_w
  exact ih (node r1 r2 r4 r5) (k - 1) (by omega) hq.2 (by omega)

/-- **P4.2** (IH application, wave 1): for the center sub-cell
    `n5 = node nw_se ne_sw sw_ne se_nw` of the double-nine decomposition,
    `hashlifeResultAux (k+1) n5` agrees with `evolve (2^(k-1))` on `n5`'s
    centered window. This is the induction hypothesis (passed in explicitly by
    `p4_succ_membership`, breaking the cyclic back-reference to
    `hashlifeResult_central_correct`) applied to the level-`(k+1)` sub-cell
    `n5` (whose level is `k+1 = (k-1)+2`). The `ih` application is delegated to
    `p4_wave1_ih_step` (c.139 workaround for the whnf divergence). -/
theorem p4_wave1_ih
    (c : MacroCell) (k : Nat) (hwf : c.wf = true) (hk : c.level = k + 2) (hk1 : 1 ≤ k)
    (ih : ∀ (c' : MacroCell) (j : Nat), j < k → c'.wf = true → c'.level = j + 2 →
      centralCorrect c' j) :
    ∃ nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
       sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell,
      c = node (node nw_nw nw_ne nw_sw nw_se)
               (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se)
               (node se_nw se_ne se_sw se_se) ∧
      centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1) := by
  obtain ⟨nw_nw, nw_ne, nw_sw, nw_se, ne_nw, ne_ne, ne_sw, ne_se,
          sw_nw, sw_ne, sw_sw, sw_se, se_nw, se_ne, se_sw, se_se, rfl, hgrands⟩ :=
    p4_double_nine_shape c k hwf hk
  obtain ⟨hnw_nw_l, hnw_nw_w, hnw_ne_l, hnw_ne_w, hnw_sw_l, hnw_sw_w, hnw_se_l, hnw_se_w,
          hne_nw_l, hne_nw_w, hne_ne_l, hne_ne_w, hne_sw_l, hne_sw_w, hne_se_l, hne_se_w,
          hsw_nw_l, hsw_nw_w, hsw_ne_l, hsw_ne_w, hsw_sw_l, hsw_sw_w, hsw_se_l, hsw_se_w,
          hse_nw_l, hse_nw_w, hse_ne_l, hse_ne_w, hse_sw_l, hse_sw_w, hse_se_l, hse_se_w⟩ :=
    hgrands
  refine ⟨nw_nw, nw_ne, nw_sw, nw_se, ne_nw, ne_ne, ne_sw, ne_se,
          sw_nw, sw_ne, sw_sw, sw_se, se_nw, se_ne, se_sw, se_se, rfl, ?_⟩
  exact p4_wave1_ih_step k hk1 nw_se ne_sw sw_ne se_nw
          hnw_se_l hne_sw_l hsw_ne_l hse_nw_l
          hnw_se_w hne_sw_w hsw_ne_w hse_nw_w ih


/-- **P4.3** (IH application, wave 2): for each of the four super-cells
    `q_*` built from the wave-1 results `r_i`, `hashlifeResultAux (k+1) q_*`
    agrees with `evolve (2^(k-1))` on `q_*`'s centered window. Same shape as
    P4.2 but on the second wave of the double-nine. Difficulty: P4.3
    (mechanical IH, structurally identical to P4.2 — may factor through a
    common helper). -/
theorem p4_wave2_ih
    (c : MacroCell) (k : Nat) (hwf : c.wf = true) (hk : c.level = k + 2) (hk1 : 1 ≤ k)
    (ih : ∀ (c' : MacroCell) (j : Nat), j < k → c'.wf = true → c'.level = j + 2 →
      centralCorrect c' j) :
    ∃ nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
       sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell,
      c = node (node nw_nw nw_ne nw_sw nw_se)
               (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se)
               (node se_nw se_ne se_sw se_se) ∧
      centralCorrect
        (node (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
              (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
              (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
              (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw)))
        (k - 1) ∧
      centralCorrect
        (node (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
              (hashlifeResultAux (k + 1) (node ne_nw ne_ne ne_sw ne_se))
              (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
              (hashlifeResultAux (k + 1) (node ne_sw ne_se se_nw se_ne)))
        (k - 1) ∧
      centralCorrect
        (node (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
              (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
              (hashlifeResultAux (k + 1) (node sw_nw sw_ne sw_sw sw_se))
              (hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw)))
        (k - 1) ∧
      centralCorrect
        (node (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
              (hashlifeResultAux (k + 1) (node ne_sw ne_se se_nw se_ne))
              (hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
              (hashlifeResultAux (k + 1) (node se_nw se_ne se_sw se_se)))
        (k - 1) := by
  obtain ⟨nw_nw, nw_ne, nw_sw, nw_se, ne_nw, ne_ne, ne_sw, ne_se,
          sw_nw, sw_ne, sw_sw, sw_se, se_nw, se_ne, se_sw, se_se, rfl, hgrands⟩ :=
    p4_double_nine_shape c k hwf hk
  obtain ⟨hnw_nw_l, hnw_nw_w, hnw_ne_l, hnw_ne_w, hnw_sw_l, hnw_sw_w, hnw_se_l, hnw_se_w,
          hne_nw_l, hne_nw_w, hne_ne_l, hne_ne_w, hne_sw_l, hne_sw_w, hne_se_l, hne_se_w,
          hsw_nw_l, hsw_nw_w, hsw_ne_l, hsw_ne_w, hsw_sw_l, hsw_sw_w, hsw_se_l, hsw_se_w,
          hse_nw_l, hse_nw_w, hse_ne_l, hse_ne_w, hse_sw_l, hse_sw_w, hse_se_l, hse_se_w⟩ :=
    hgrands
  -- n1 = node nw_nw nw_ne nw_sw nw_se: level+wf, then preservation (c.142) -> r1 facts.
  have hq1 := node_wf_level_of_four hnw_nw_l hnw_ne_l hnw_sw_l hnw_se_l
                                    hnw_nw_w hnw_ne_w hnw_sw_w hnw_se_w
  have hr1 := wave1_result_facts k hk1 (node nw_nw nw_ne nw_sw nw_se) hq1.2 hq1.1
  -- n2 = node nw_ne ne_nw nw_se ne_sw
  have hq2 := node_wf_level_of_four hnw_ne_l hne_nw_l hnw_se_l hne_sw_l
                                    hnw_ne_w hne_nw_w hnw_se_w hne_sw_w
  have hr2 := wave1_result_facts k hk1 (node nw_ne ne_nw nw_se ne_sw) hq2.2 hq2.1
  -- n3 = node ne_nw ne_ne ne_sw ne_se
  have hq3 := node_wf_level_of_four hne_nw_l hne_ne_l hne_sw_l hne_se_l
                                    hne_nw_w hne_ne_w hne_sw_w hne_se_w
  have hr3 := wave1_result_facts k hk1 (node ne_nw ne_ne ne_sw ne_se) hq3.2 hq3.1
  -- n4 = node nw_sw nw_se sw_nw sw_ne
  have hq4 := node_wf_level_of_four hnw_sw_l hnw_se_l hsw_nw_l hsw_ne_l
                                    hnw_sw_w hnw_se_w hsw_nw_w hsw_ne_w
  have hr4 := wave1_result_facts k hk1 (node nw_sw nw_se sw_nw sw_ne) hq4.2 hq4.1
  -- n5 = node nw_se ne_sw sw_ne se_nw
  have hq5 := node_wf_level_of_four hnw_se_l hne_sw_l hsw_ne_l hse_nw_l
                                    hnw_se_w hne_sw_w hsw_ne_w hse_nw_w
  have hr5 := wave1_result_facts k hk1 (node nw_se ne_sw sw_ne se_nw) hq5.2 hq5.1
  -- n6 = node ne_sw ne_se se_nw se_ne
  have hq6 := node_wf_level_of_four hne_sw_l hne_se_l hse_nw_l hse_ne_l
                                    hne_sw_w hne_se_w hse_nw_w hse_ne_w
  have hr6 := wave1_result_facts k hk1 (node ne_sw ne_se se_nw se_ne) hq6.2 hq6.1
  -- n7 = node sw_nw sw_ne sw_sw sw_se
  have hq7 := node_wf_level_of_four hsw_nw_l hsw_ne_l hsw_sw_l hsw_se_l
                                    hsw_nw_w hsw_ne_w hsw_sw_w hsw_se_w
  have hr7 := wave1_result_facts k hk1 (node sw_nw sw_ne sw_sw sw_se) hq7.2 hq7.1
  -- n8 = node sw_ne se_nw sw_se se_sw
  have hq8 := node_wf_level_of_four hsw_ne_l hse_nw_l hsw_se_l hse_sw_l
                                    hsw_ne_w hse_nw_w hsw_se_w hse_sw_w
  have hr8 := wave1_result_facts k hk1 (node sw_ne se_nw sw_se se_sw) hq8.2 hq8.1
  -- n9 = node se_nw se_ne se_sw se_se
  have hq9 := node_wf_level_of_four hse_nw_l hse_ne_l hse_sw_l hse_se_l
                                    hse_nw_w hse_ne_w hse_sw_w hse_se_w
  have hr9 := wave1_result_facts k hk1 (node se_nw se_ne se_sw se_se) hq9.2 hq9.1
  refine ⟨nw_nw, nw_ne, nw_sw, nw_se, ne_nw, ne_ne, ne_sw, ne_se,
          sw_nw, sw_ne, sw_sw, sw_se, se_nw, se_ne, se_sw, se_se, rfl, ?_, ?_, ?_, ?_⟩
  · -- q_nw = node r1 r2 r4 r5
    exact p4_wave2_ih_step k hk1
            (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
            (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
            (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
            (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
            hr1.1 hr2.1 hr4.1 hr5.1
            (wf_of_cellWf hr1.2) (wf_of_cellWf hr2.2)
            (wf_of_cellWf hr4.2) (wf_of_cellWf hr5.2) ih
  · -- q_ne = node r2 r3 r5 r6
    exact p4_wave2_ih_step k hk1
            (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
            (hashlifeResultAux (k + 1) (node ne_nw ne_ne ne_sw ne_se))
            (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
            (hashlifeResultAux (k + 1) (node ne_sw ne_se se_nw se_ne))
            hr2.1 hr3.1 hr5.1 hr6.1
            (wf_of_cellWf hr2.2) (wf_of_cellWf hr3.2)
            (wf_of_cellWf hr5.2) (wf_of_cellWf hr6.2) ih
  · -- q_sw = node r4 r5 r7 r8
    exact p4_wave2_ih_step k hk1
            (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
            (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
            (hashlifeResultAux (k + 1) (node sw_nw sw_ne sw_sw sw_se))
            (hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
            hr4.1 hr5.1 hr7.1 hr8.1
            (wf_of_cellWf hr4.2) (wf_of_cellWf hr5.2)
            (wf_of_cellWf hr7.2) (wf_of_cellWf hr8.2) ih
  · -- q_se = node r5 r6 r8 r9
    exact p4_wave2_ih_step k hk1
            (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
            (hashlifeResultAux (k + 1) (node ne_sw ne_se se_nw se_ne))
            (hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
            (hashlifeResultAux (k + 1) (node se_nw se_ne se_sw se_se))
            hr5.1 hr6.1 hr8.1 hr9.1
            (wf_of_cellWf hr5.2) (wf_of_cellWf hr6.2)
            (wf_of_cellWf hr8.2) (wf_of_cellWf hr9.2) ih

/-! ### P4.4 decomposition — balisage en sous-sorries

The research-level composition `evolve (2^k) = evolve (2^(k-1)) ∘ evolve (2^(k-1))`
on the centered window is decomposed into four named sub-goals, each
independently attackable. This turns the monolithic P4.4 `sorry` into a chain
of milestones with clear interfaces (the same methodology that isolated
`hashlifeResultAux_level_cellWf` as a sub-goal unblocked P4.3, c.142).

- **S1 (CLOSED — `evolve_add` below)** : function-iteration composition.
  `evolve (a + b) g = evolve a (evolve b g)`. Pure `step^[·]` arithmetic, no
  `hashlifeResultAux`, no whnf wall — proven.
- **S2 (CLOSED — `window_cone_in_domain` below)** : boundary does not leak —
  for `p` in the centered window `[2^k, 2^k + 2^(k+1))²`, the light cone
  `lightCone p (2^k)` (radius of `evolve 2^(k-1)`, via `step_light_cone`) stays
  inside the domain covered by `c.toGrid (0,0)`. Pure Manhattan arithmetic, no
  `hashlifeResultAux`, no whnf wall — proven (`manhattan_deviation` Nat→Int
  bridge + power-normalization + pure-Int `linarith`).
- **S3 (sub-sorry)** : sub-cell coverage — the quadrant super-cell `q_j` whose
  centered region contains `p` agrees with `c.toGrid` on that light cone, so
  `evolve 2^(k-1) (c.toGrid) p = evolve 2^(k-1) (q_j.toGrid) p` by
  `step_light_cone (2^(k-1))`.
- **S4 (sub-sorry, core)** : assemble — combine S1+S2+S3 with the four
  `centralCorrect q_j (k-1)` facts from P4.3 (`p4_wave2_ih`) to conclude the
  pointwise membership agreement that `p4_succ_membership` needs.

S1 (composition) and S2 (no-leak) are closed; the remaining open surface is
the sub-cell-coverage + assembly argument (S3, S4), carried by the residual
`sorry` of `p4_succ_membership`. The standalone `p4_half_steps_compose`
theorem (former `: True` placeholder) was deleted in N2-bis: its pure-evolve
content is exactly `evolve_add` + `evolve_half_step` (both proven), and its
wave-assembly content is exactly the S3/S4 residual, so it duplicated an
already-closed obligation — a vacuous placeholder (G.2). -/

/-- **S1** (CLOSED): `evolve (a + b) g = evolve a (evolve b g)`.

Pure function-iteration arithmetic — `evolve n g = step^[n] g`, so iteration
splits additively. The first closed milestone of the P4.4 balisage: the
composition `evolve 2^k = evolve 2^(k-1) ∘ evolve 2^(k-1)` is exactly
`evolve_add (2^(k-1)) (2^(k-1)) g`. -/
theorem evolve_add (a b : Nat) (g : Grid) :
    evolve (a + b) g = evolve a (evolve b g) := by
  induction a with
  | zero => simp [evolve_zero]
  | succ n ih =>
    rw [Nat.succ_add, evolve_succ, evolve_succ, ih]

/-- **S1 2^k instantiation** (CLOSED): `evolve 2^k = evolve 2^(k-1) ∘ evolve 2^(k-1)`.

The exact `2^k`-form of `evolve_add` (S1) that the glue `p4_succ_membership`
and the eventual P4.4 assemble step (S4) consume: the centered-window result of
`evolve 2^k` decomposes into two `evolve 2^(k-1)` half-steps (wave 1 then wave
2). Gated on `1 ≤ k` so that the predecessor `k-1` is well-defined as a `Nat`.
The power fact `2^k = 2^(k-1) + 2^(k-1)` is discharged in pure `Nat`
(`Nat.pow_succ` + `ring`); `omega` is avoided on the powers because it loses the
positivity of the `2^(k-1)` atom under the additive doubling (cf. the c.146
omega-limitation lesson on `window_cone_in_domain`). -/
theorem evolve_half_step (k : Nat) (hk : 1 ≤ k) (g : Grid) :
    evolve (2^k) g = evolve (2^(k-1)) (evolve (2^(k-1)) g) := by
  -- Introduce a fresh name `m` for the predecessor `k-1`. A plain
  -- `have hpred : k = (k-1) + 1` then `rw [hpred]` rewrites the `k` *inside*
  -- `2^(k-1)` too (since `k` appears in `k-1`), leaving atoms `2^(k-1)` vs
  -- `2^(1+(k-1)-1)` that `ring` cannot unify. `set` makes `m` opaque so
  -- `rw [hkm]` touches only the LHS-exponent `k`.
  set m := k - 1 with hm
  have hkm : k = m + 1 := by omega
  have h2pow : 2^k = 2^m + 2^m := by rw [hkm, Nat.pow_succ]; ring
  rw [h2pow, evolve_add]

/-- **S2 helper**: lift the `Nat` `manhattan` bound to per-coordinate `Int.abs`
    bounds. Isolated from `window_cone_in_domain` below so the cone/window
    reasoning works purely in `Int`: `omega` closes the `Nat.natAbs` goals here
    in isolation, but splits the `Nat` `2^k` atom from its `(2^k : Int)` cast
    when both appear in one goal (a known `omega` limitation on mixed
    `Nat`/`Int` atoms). -/
private theorem manhattan_deviation (p q : Int × Int) (R : Nat)
    (h : manhattan p q ≤ R) : |p.1 - q.1| ≤ (R : Int) ∧ |p.2 - q.2| ≤ (R : Int) := by
  -- Isolate the Nat `manhattan`/`natAbs` → `Int.abs` lifting from the
  -- power/window reasoning, so `window_cone_in_domain` below works purely in
  -- `Int` (omega handles `Int.abs` + powers cleanly, but struggles when
  -- `Nat.natAbs` and `Int.abs` of the same term share a goal).
  unfold manhattan at h
  have h1' : Int.natAbs (p.1 - q.1) ≤ R := by omega
  have h2' : Int.natAbs (p.2 - q.2) ≤ R := by omega
  refine ⟨?_, ?_⟩
  · rw [Int.abs_eq_natAbs]; exact_mod_cast h1'
  · rw [Int.abs_eq_natAbs]; exact_mod_cast h2'

/-- **S2** (CLOSED): the light cone does not leak out of the MacroCell domain.

    For a point `p` in the centered window `[2^k, 2^k + 2^(k+1))²` (the region
    the Hashlife result covers), any cell `q` within Manhattan distance `2^k`
    of `p` — i.e. any cell in the light cone `lightCone p (2^k)` (radius `2^k`
    is exactly the cone radius of `evolve 2^(k-1)` via `step_light_cone`) —
    stays inside the full MacroCell domain `[0, 2^(k+2))²`.

    This is the geometric core of the "boundary does not leak" half of P4.4:
    it is why the wave-2 super-cells, each computing `evolve 2^(k-1)` on its
    own grid, nonetheless agree with the global `evolve 2^k` on the centered
    window — every cell that could influence a centered point is still within
    the MacroCell's recorded domain. No `hashlifeResultAux`, no whnf wall —
    pure Manhattan arithmetic over `Int`, reusing `manhattan` (L85). The proof
    bridges via `manhattan_deviation`, proves the power facts `2^(k+1) = 2·2^k`
    and `2^(k+2) = 4·2^k` in pure `Nat` (rw + `Nat.pow_succ`), rewrites them in
    so everything is linear in the single atom `2^k`, and closes with `linarith`
    (`omega` loses the positivity of `2^k` under the multiplicative atoms). -/
private theorem window_cone_in_domain (k : Nat) (p q : Int × Int)
    (hp1_lo : (2^k : Int) ≤ p.1) (hp1_hi : p.1 < 2^k + 2^(k+1))
    (hp2_lo : (2^k : Int) ≤ p.2) (hp2_hi : p.2 < 2^k + 2^(k+1))
    (hc : manhattan p q ≤ 2^k) :
    (0 : Int) ≤ q.1 ∧ q.1 < 2^(k+2) ∧ (0 : Int) ≤ q.2 ∧ q.2 < 2^(k+2) := by
  -- Bridge the Nat `manhattan` bound to per-coordinate `Int` abs bounds, then
  -- unpack abs into linear inequalities (linarith does not split `|x|`).
  obtain ⟨hq1, hq2⟩ := manhattan_deviation p q (2^k) hc
  -- `manhattan_deviation` types its bound as `↑(2^k)` (Nat cast of the Nat
  -- radius), but the window hypotheses below use the native-Int `(2^k : Int)`
  -- (`HPow`). These are the same value but distinct terms, so `linarith` would
  -- see two unrelated atoms. Normalize via `Nat.cast_pow` to a single atom.
  have hk_pow : (↑((2:Nat)^k) : Int) = (2^k : Int) := Nat.cast_pow 2 k
  rw [hk_pow] at hq1 hq2
  obtain ⟨hq1lo, hq1hi⟩ := abs_le.mp hq1
  obtain ⟨hq2lo, hq2hi⟩ := abs_le.mp hq2
  -- Power facts proven in pure Nat (rw only — omega splits the Nat `2^k` from
  -- `Nat.pow_succ` against the `(2^k : Int)` casts in scope), lifted to Int.
  -- Factored into `Conway.Life.pow_two_add_one_int`/`pow_two_add_two_int`
  -- (ConeGeometry, imported above), shared with `window_cheb_cone_in_domain`.
  have hpe1 : (2^(k+1) : Int) = 2 * (2^k : Int) := pow_two_add_one_int k
  have hpe2 : (2^(k+2) : Int) = 4 * (2^k : Int) := pow_two_add_two_int k
  -- Rewrite every power occurrence into a multiple of the single atom `2^k`,
  -- so the goal reduces to pure linear `Int` arithmetic in `2^k`. `linarith`
  -- (not `omega`) closes it: omega loses the positivity of `2^k` when juggling
  -- the `2^(k+1)`/`2^(k+2)` multiplicative atoms (counterexample: `2^k ≤ -1`),
  -- while `linarith` treats `2^k` as a plain linear variable, and the bounds
  -- `0 ≤ q.i`, `q.i < 4·2^k` follow from `p.i ∈ [2^k, 3·2^k)` and
  -- `|p.i - q.i| ≤ 2^k` with no sign assumption.
  rw [hpe1] at hp1_hi hp2_hi
  rw [hpe2]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals linarith

/-- **P4.4 NW-quadrant shift lemma (factorisé, c.488).** Caractérise l'appartenance
    pointwise `p ∈ (hashlifeResultAux (k+1) q_nw).toGrid (2^k, 2^k)` du quadrant NW
    (offset `(2^k, 2^k)` via `mem_toGrid_node`) en une conjonction `isAlive ... ∧
    bounds`, où `q_nw = node r1 r2 r4 r5` est la super-cellule des quatre résultats
    wave-1.

    **Pourquoi factoriser hors `p4_succ_membership`** : ces étapes (construire
    `centralCorrect q_nw (k-1)` via `p4_wave2_ih_step`, puis appliquer
    `centralCorrect_mem_shift` pour réancrer l'offset `(2^k, 2^k)`) étaient inline
    dans `p4_succ_membership` (snapshot #6724 run-4) et déclenchaient un whnf
    timeout (200000 heartbeats) sur la tête de la déclaration monolithique. Le
    budget heartbeats se réinitialise **par déclaration** : un lemme standalone au
    corps court compile sans timeout, et `p4_succ_membership` n'a plus qu'à
    l'appliquer (`have hnw_shift := p4_nw_shift_lemma ...`) sans ré-encourir le
    coût d'élaboration inline. Pattern cohérent avec `p4_wave2_ih_step` (c.142).

    **Corps** : `p4_wave2_ih_step` (ih sur la super-cellule opaque) →
    `centralCorrect_mem_shift` (réancrage offset, G2 congruence). Sorry-free. -/
private theorem p4_nw_shift_lemma
    (k : Nat) (hk1 : 1 ≤ k)
    (r1 r2 r4 r5 : MacroCell)
    (hr1_l : r1.level = k) (hr2_l : r2.level = k)
    (hr4_l : r4.level = k) (hr5_l : r5.level = k)
    (hr1_w : r1.wf = true) (hr2_w : r2.wf = true)
    (hr4_w : r4.wf = true) (hr5_w : r5.wf = true)
    (ih : ∀ (c' : MacroCell) (j : Nat), j < k → c'.wf = true → c'.level = j + 2 →
      centralCorrect c' j)
    (p : Int × Int) :
    p ∈ (hashlifeResultAux ((k - 1) + 2) (node r1 r2 r4 r5)).toGrid
          ((2^k : Int), (2^k : Int)) ↔
      isAlive (evolve (2^(k - 1)) ((node r1 r2 r4 r5).toGrid (0, 0)))
        (p.1 - (2^k : Int) + (2^(k - 1) : Int),
         p.2 - (2^k : Int) + (2^(k - 1) : Int)) = true ∧
      (2^k : Int) ≤ p.1 ∧ p.1 < (2^k : Int) + 2^((k - 1) + 1) ∧
      (2^k : Int) ≤ p.2 ∧ p.2 < (2^k : Int) + 2^((k - 1) + 1) := by
  have hcc : centralCorrect (node r1 r2 r4 r5) (k - 1) :=
    p4_wave2_ih_step k hk1 r1 r2 r4 r5
      hr1_l hr2_l hr4_l hr5_l hr1_w hr2_w hr4_w hr5_w ih
  exact centralCorrect_mem_shift (node r1 r2 r4 r5) (k - 1)
    (2^k) (2^k) p hcc

/-- Local `isAlive … = true ↔ p ∈ …` bridge. Mirrors `LightCone.isAlive_true_iff_mem`
    verbatim, but LightCone is DOWNSTREAM of this file (`LightCone.lean` imports
    `Conway.Life.HashlifeCorrectness`), so importing it here would be a cycle.
    `private` keeps it file-local — no clash with LightCone's public theorem. -/
private theorem isAlive_true_iff_mem_local (g : Grid) (p : Int × Int) :
    isAlive g p = true ↔ p ∈ g := by
  rw [isAlive]; exact List.elem_iff

/-! ### Miroirs boîte-Chebyshev (LightCone, cycle d'import — #6724 c.92)

Les trois lemmes suivants reprennent VERBATIM `chebDist_le_one_of_moore`,
`step_box_local` et `evolve_box_agree` de `LightCone.lean` (livrés sorry-free
par #9577). `LightCone` est EN AVAL de ce fichier (il importe
`Conway.Life.HashlifeCorrectness`) : les importer ici serait un cycle — même
schéma que `isAlive_true_iff_mem_local` ci-dessus. Tous leurs ingrédients sont
EN AMONT : `chebDist`/`chebDist_self`/`chebDist_triangle` (`ConeGeometry`,
importé L81), `mooreNeighbors`/`evolve_zero`/`evolve_succ` (`Conway.Life`),
`aliveNext_local` (L851) et `isAlive_step_eq_aliveNext` (L873) (ce fichier).

C'est la machinerie-clé du redesign borné du mur NW : la boîte Chebyshev
ÉTROITE `[p-u, p+u]` remplace le cône Manhattan `2·u` de `evolve_cone_agree`,
qui débordait la fenêtre du supercell (réfutation c.91, bloc après le mur). -/

/-- Miroir de `LightCone.chebDist_le_one_of_moore` : un voisin de Moore de `p`
    est à distance Chebyshev au plus 1 (le voisinage de Moore EST la boule
    unité Chebyshev). -/
private theorem chebDist_le_one_of_moore_local (p q : Int × Int)
    (hq : q ∈ mooreNeighbors p) : chebDist p q ≤ 1 := by
  unfold chebDist mooreNeighbors at *
  simp only [List.mem_cons] at hq
  rcases hq with h | h | h | h | h | h | h | h | h
  · have hd1 : q.1 - p.1 = -1 := by rw [h]; omega
    have hd2 : q.2 - p.2 = -1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · have hd1 : q.1 - p.1 = -1 := by rw [h]; omega
    have hd2 : q.2 - p.2 = 0 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · have hd1 : q.1 - p.1 = -1 := by rw [h]; omega
    have hd2 : q.2 - p.2 = 1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · have hd1 : q.1 - p.1 = 0 := by rw [h]; omega
    have hd2 : q.2 - p.2 = -1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · have hd1 : q.1 - p.1 = 0 := by rw [h]; omega
    have hd2 : q.2 - p.2 = 1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · have hd1 : q.1 - p.1 = 1 := by rw [h]; omega
    have hd2 : q.2 - p.2 = -1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · have hd1 : q.1 - p.1 = 1 := by rw [h]; omega
    have hd2 : q.2 - p.2 = 0 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · have hd1 : q.1 - p.1 = 1 := by rw [h]; omega
    have hd2 : q.2 - p.2 = 1 := by rw [h]; omega
    rw [hd1, hd2]; decide
  · simp at h

/-- Miroir de `LightCone.step_box_local` : si `g₁ g₂` coïncident sur la boîte
    Chebyshev de rayon 1 autour de `p` (la cellule et ses huit voisins de
    Moore), un pas préserve l'accord en `p`. Analogue étroit de `step_local`
    (L901, cône Manhattan-2 lâche). -/
private theorem step_box_local_mirror (g₁ g₂ : Grid) (p : Int × Int)
    (h_box : ∀ q, chebDist p q ≤ 1 → isAlive g₁ q = isAlive g₂ q) :
    isAlive (step g₁) p = isAlive (step g₂) p := by
  have h_self : isAlive g₁ p = isAlive g₂ p := by
    apply h_box p
    have heq : chebDist p p = 0 := chebDist_self p
    omega
  have h_nbrs : ∀ q ∈ mooreNeighbors p, isAlive g₁ q = isAlive g₂ q := by
    intro q hq
    exact h_box q (chebDist_le_one_of_moore_local p q hq)
  have h_alive : aliveNext g₁ p = aliveNext g₂ p :=
    aliveNext_local g₁ g₂ p h_self h_nbrs
  rw [isAlive_step_eq_aliveNext, isAlive_step_eq_aliveNext, h_alive]

/-- Miroir de `LightCone.evolve_box_agree` : si `g₁ g₂` coïncident sur la boîte
    Chebyshev de rayon `u` autour de `p`, après `u` générations elles ont la
    même vivacité en `p`. Analogue étroit de `step_light_cone` (L931, cône
    Manhattan `2·u` — le facteur 2 perdu est exactement ce qui faisait déborder
    le mur NW hors de la fenêtre du supercell). -/
private theorem evolve_box_agree_local (u : Nat) (g₁ g₂ : Grid) (p : Int × Int)
    (h_box : ∀ q, chebDist p q ≤ u → isAlive g₁ q = isAlive g₂ q) :
    isAlive (evolve u g₁) p = isAlive (evolve u g₂) p := by
  induction u generalizing p with
  | zero =>
    simp only [evolve_zero]
    have hpp : chebDist p p ≤ 0 := by
      have heq : chebDist p p = 0 := chebDist_self p
      omega
    exact h_box p hpp
  | succ n ih =>
    simp only [evolve_succ]
    apply step_box_local_mirror
    intro q hpq
    apply ih
    intro r hqr
    apply h_box r
    have htri : chebDist p r ≤ chebDist p q + chebDist q r := chebDist_triangle p r q
    omega

/-- **crux (a) offset building block (sorry-free, #6724 c.749).** The
    `2^level`-pinned quadrant decomposition of a `node`'s `toGrid` membership.
    `mem_toGrid_node` (L1478) already decomposes `(node nw ne sw se).toGrid
    (r0,c0)` but leaves the quadrant offset as the OPAQUE `2 ^ nw.level`; this
    specialization pins it to the concrete `2 ^ k` once `nw.level = k` is known.

    This is the "lemme intermédiaire nommé sur les offsets seuls" prescribed for
    crux (a) (DM `msg-20260729T010408-cromnx`): the quadrant-offset arithmetic
    (NW `(0,0)`, NE `(0, 2^k)`, SW `(2^k, 0)`, SE `(2^k, 2^k)`) isolated from the
    game-of-life theory. Proven by `mem_toGrid_node` + the level rewrite — no
    `sorry`, no game semantics. It is the available offset machinery the bridge
    `(a)` half assembles over (see `p4_nw_g3_bridge` docstring); the bridge is
    armed below with `hR1_l … hR5_l : R_j.level = k` precisely so it can apply
    this lemma to pin every `(node R1 R2 R4 R5)` offset. -/
private theorem p4_nw_offset_decomp (k : Nat)
    (R1 R2 R4 R5 : MacroCell) (hR1_l : R1.level = k) (p : Int × Int) :
    p ∈ (node R1 R2 R4 R5).toGrid (0, 0) ↔
      p ∈ R1.toGrid (0, 0) ∨
      p ∈ R2.toGrid (0, (2 ^ k : Int)) ∨
      p ∈ R4.toGrid ((2 ^ k : Int), 0) ∨
      p ∈ R5.toGrid ((2 ^ k : Int), (2 ^ k : Int)) := by
  rw [mem_toGrid_node, hR1_l]
  simp only [Int.zero_add, Int.add_zero]

/-! ### Bornes d'empreinte de `toCellsAux` + navette booléenne (mur (a), c.94)

Les quatre lemmes d'accord de grille de l'étape 2 du plan DEMO 63 exigent
d'exclure des sous-cellules par leur seule POSITION : borne inférieure (les
origines des quadrants ne font que croître — aucun `wf` requis) et borne
supérieure (empreinte de côté `2^level` — `wf` requis pour aligner l'empreinte
réelle sur celle annoncée). Aucun lemme d'empreinte n'existe dans
`MacroCell.lean` (vérifié par grep) : les voici, privés à ce fichier. -/

/-- Navette booléenne : une équivalence des `= true` donne l'égalité `Bool`. -/
private theorem p4_bool_eq_of_iff : ∀ (a b : Bool), (a = true ↔ b = true) → a = b := by
  decide

/-- Borne inférieure d'empreinte (sans `wf`) : tout point énuméré par
    `toCellsAux r0 c0` est au sud-est (au sens large) de l'origine `(r0, c0)`. -/
private theorem p4_toCellsAux_origin_le (c : MacroCell) :
    ∀ (r0 c0 : Int) (x : Int × Int), x ∈ c.toCellsAux r0 c0 → r0 ≤ x.1 ∧ c0 ≤ x.2 := by
  induction c with
  | leaf b =>
    intro r0 c0 x hx
    cases b with
    | false => simp only [toCellsAux] at hx; cases hx
    | true =>
      simp only [toCellsAux, List.mem_singleton] at hx
      subst hx
      exact ⟨le_refl r0, le_refl c0⟩
  | node nw ne sw se ihnw ihne ihsw ihse =>
    intro r0 c0 x hx
    simp only [toCellsAux, List.mem_append, or_assoc] at hx
    have hpos : (0 : Int) < 2 ^ nw.level := pow_pos (by norm_num) nw.level
    have hcast : ((2 ^ nw.level : Nat) : Int) = 2 ^ nw.level := by
      norm_cast
    rcases hx with hx | hx | hx | hx
    · exact ihnw _ _ x hx
    · obtain ⟨h1, h2⟩ := ihne _ _ x hx
      omega
    · obtain ⟨h1, h2⟩ := ihsw _ _ x hx
      omega
    · obtain ⟨h1, h2⟩ := ihse _ _ x hx
      omega

/-- Borne supérieure d'empreinte (avec `wf`) : tout point énuméré par
    `toCellsAux r0 c0` d'une cellule bien formée reste dans le carré de côté
    `2^level` ancré en `(r0, c0)`. Le `wf` est indispensable : il aligne les
    niveaux des quatre quadrants, donc l'empreinte réelle sur celle annoncée. -/
private theorem p4_toCellsAux_lt (c : MacroCell) :
    ∀ (r0 c0 : Int) (x : Int × Int), c.wf = true → x ∈ c.toCellsAux r0 c0 →
      x.1 < r0 + (2 ^ c.level : Int) ∧ x.2 < c0 + (2 ^ c.level : Int) := by
  induction c with
  | leaf b =>
    intro r0 c0 x _ hx
    cases b with
    | false => simp only [toCellsAux] at hx; cases hx
    | true =>
      simp only [toCellsAux, List.mem_singleton] at hx
      subst hx
      simp only [MacroCell.level, pow_zero]
      show r0 < r0 + 1 ∧ c0 < c0 + 1
      omega
  | node nw ne sw se ihnw ihne ihsw ihse =>
    intro r0 c0 x hwf hx
    obtain ⟨hwnw, hwne, hwsw, hwse, hlne, hlsw, hlse⟩ := wf_node_elim hwf
    simp only [toCellsAux, List.mem_append, or_assoc] at hx
    have hpos : (0 : Int) < 2 ^ nw.level := pow_pos (by norm_num) nw.level
    have hsplit : (2 ^ (node nw ne sw se).level : Int) = 2 ^ nw.level + 2 ^ nw.level := by
      show (2 ^ (1 + nw.level) : Int) = 2 ^ nw.level + 2 ^ nw.level
      rw [pow_add, pow_one]
      ring
    have hcast : ((2 ^ nw.level : Nat) : Int) = 2 ^ nw.level := by
      norm_cast
    rcases hx with hx | hx | hx | hx
    · obtain ⟨h1, h2⟩ := ihnw _ _ x hwnw hx
      omega
    · obtain ⟨h1, h2⟩ := ihne _ _ x hwne hx
      rw [hlne] at h1 h2
      omega
    · obtain ⟨h1, h2⟩ := ihsw _ _ x hwsw hx
      rw [hlsw] at h1 h2
      omega
    · obtain ⟨h1, h2⟩ := ihse _ _ x hwse hx
      rw [hlse] at h1 h2
      omega

/-- Corollaire `toGrid` de la borne inférieure (sans `wf`). -/
private theorem p4_mem_toGrid_origin_le (c : MacroCell) (r0 c0 : Int) (x : Int × Int)
    (hx : x ∈ c.toGrid (r0, c0)) : r0 ≤ x.1 ∧ c0 ≤ x.2 := by
  rw [mem_toGrid] at hx
  exact p4_toCellsAux_origin_le c r0 c0 x hx

/-- Corollaire `toGrid` de la borne supérieure (avec `wf`). -/
private theorem p4_mem_toGrid_lt (c : MacroCell) (r0 c0 : Int) (x : Int × Int)
    (hwf : c.wf = true) (hx : x ∈ c.toGrid (r0, c0)) :
    x.1 < r0 + (2 ^ c.level : Int) ∧ x.2 < c0 + (2 ^ c.level : Int) := by
  rw [mem_toGrid] at hx
  exact p4_toCellsAux_lt c r0 c0 x hwf hx

/-- Ré-ancrage ponctuel : évaluer la grille d'une cellule posée en `(a, b)`
    revient à évaluer la grille posée à l'origine au point translaté.
    Version booléenne de `mem_toGrid_shift`. -/
private theorem p4_isAlive_toGrid_shift (c : MacroCell) (a b : Int) (r : Int × Int) :
    isAlive (c.toGrid (a, b)) r = isAlive (c.toGrid (0, 0)) (r.1 - a, r.2 - b) := by
  apply p4_bool_eq_of_iff
  rw [isAlive_true_iff_mem_local, isAlive_true_iff_mem_local]
  exact mem_toGrid_shift

/-! ### Étape 2 — les quatre lemmes d'accord de grille parent/recombinaison

Le parent (niveau `k+2`) et chaque nœud de recombinaison de la première vague
coïncident sur le rectangle d'agrément du quadrant correspondant : chaque
sous-cellule du parent y survivant est l'un des quatre petits-enfants du nœud
de recombinaison, aux mêmes offsets absolus ; les autres sont exclues par pure
position (bornes d'empreinte ci-dessus). Les sept petits-enfants NON contraints
par `hn1..hn5` (`ne_ne, ne_se, sw_sw, sw_se, se_ne, se_sw, se_se`) ne sont
exclus QUE par borne inférieure — aucun `wf` du parent n'est requis. -/

/-- Accord parent / `n1` (non translaté) sur `[0, 2·2^k)²`. -/
private theorem p4_nw_parent_agree_n1 (k : Nat)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
      sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (hn1_l : (node nw_nw nw_ne nw_sw nw_se).level = k + 1)
    (x : Int × Int)
    (hx : 0 ≤ x.1 ∧ x.1 < (2 ^ k : Int) + (2 ^ k : Int) ∧
          0 ≤ x.2 ∧ x.2 < (2 ^ k : Int) + (2 ^ k : Int)) :
    isAlive ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
        (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid (0, 0)) x
      = isAlive ((node nw_nw nw_ne nw_sw nw_se).toGrid (0, 0)) x := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  apply p4_bool_eq_of_iff
  rw [isAlive_true_iff_mem_local, isAlive_true_iff_mem_local]
  have hBB : (2 ^ (k + 1) : Int) = (2 ^ k : Int) + (2 ^ k : Int) := by
    rw [pow_succ]; ring
  rw [mem_toGrid_node (nw := node nw_nw nw_ne nw_sw nw_se), hn1_l, hBB]
  simp only [Int.zero_add, Int.add_zero]
  constructor
  · rintro (h | h | h | h)
    · exact h
    · obtain ⟨-, hc⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
  · intro h
    exact Or.inl h

/-- Accord parent / `n2` translaté de `(0, 2^k)` sur `[0, 2·2^k) × [2^k, 3·2^k)`. -/
private theorem p4_nw_parent_agree_n2 (k : Nat)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
      sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (hn1_l : (node nw_nw nw_ne nw_sw nw_se).level = k + 1)
    (hn1_w : (node nw_nw nw_ne nw_sw nw_se).wf = true)
    (hn2_l : (node nw_ne ne_nw nw_se ne_sw).level = k + 1)
    (hn2_w : (node nw_ne ne_nw nw_se ne_sw).wf = true)
    (x : Int × Int)
    (hx : 0 ≤ x.1 ∧ x.1 < (2 ^ k : Int) + (2 ^ k : Int) ∧
          (2 ^ k : Int) ≤ x.2 ∧ x.2 < (2 ^ k : Int) + (2 ^ k : Int) + (2 ^ k : Int)) :
    isAlive ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
        (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid (0, 0)) x
      = isAlive ((node nw_ne ne_nw nw_se ne_sw).toGrid (0, (2 ^ k : Int))) x := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hl_nwnw, hl_nwne, hl_nwsw, hl_nwse, hw_nwnw, hw_nwne, hw_nwsw, hw_nwse⟩ :=
    wf_node_quad_level hn1_l hn1_w
  obtain ⟨-, hl_nenw, -, hl_nesw, -, hw_nenw, -, hw_nesw⟩ :=
    wf_node_quad_level hn2_l hn2_w
  apply p4_bool_eq_of_iff
  rw [isAlive_true_iff_mem_local, isAlive_true_iff_mem_local]
  have hBB : (2 ^ (k + 1) : Int) = (2 ^ k : Int) + (2 ^ k : Int) := by
    rw [pow_succ]; ring
  rw [mem_toGrid_node (nw := nw_ne) (ne := ne_nw) (sw := nw_se) (se := ne_sw), hl_nwne]
  rw [mem_toGrid_node (nw := node nw_nw nw_ne nw_sw nw_se), hn1_l, hBB]
  rw [mem_toGrid_node (nw := nw_nw) (ne := nw_ne) (sw := nw_sw) (se := nw_se), hl_nwnw]
  rw [mem_toGrid_node (nw := ne_nw) (ne := ne_ne) (sw := ne_sw) (se := ne_se), hl_nenw]
  simp only [Int.zero_add, Int.add_zero]
  constructor
  · rintro ((h | h | h | h) | (h | h | h | h) | h | h)
    · obtain ⟨-, hc⟩ := p4_mem_toGrid_lt _ _ _ x hw_nwnw h
      rw [hl_nwnw] at hc
      exfalso; omega
    · exact Or.inl h
    · obtain ⟨-, hc⟩ := p4_mem_toGrid_lt _ _ _ x hw_nwsw h
      rw [hl_nwsw] at hc
      exfalso; omega
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · obtain ⟨-, hc⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
    · exact Or.inr (Or.inr (Or.inr h))
    · obtain ⟨-, hc⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
  · rintro (h | h | h | h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl h))))

/-- Accord parent / `n4` translaté de `(2^k, 0)` sur `[2^k, 3·2^k) × [0, 2·2^k)`. -/
private theorem p4_nw_parent_agree_n4 (k : Nat)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
      sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (hn1_l : (node nw_nw nw_ne nw_sw nw_se).level = k + 1)
    (hn1_w : (node nw_nw nw_ne nw_sw nw_se).wf = true)
    (hn4_l : (node nw_sw nw_se sw_nw sw_ne).level = k + 1)
    (hn4_w : (node nw_sw nw_se sw_nw sw_ne).wf = true)
    (x : Int × Int)
    (hx : (2 ^ k : Int) ≤ x.1 ∧ x.1 < (2 ^ k : Int) + (2 ^ k : Int) + (2 ^ k : Int) ∧
          0 ≤ x.2 ∧ x.2 < (2 ^ k : Int) + (2 ^ k : Int)) :
    isAlive ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
        (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid (0, 0)) x
      = isAlive ((node nw_sw nw_se sw_nw sw_ne).toGrid ((2 ^ k : Int), 0)) x := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hl_nwnw, hl_nwne, hl_nwsw, hl_nwse, hw_nwnw, hw_nwne, hw_nwsw, hw_nwse⟩ :=
    wf_node_quad_level hn1_l hn1_w
  obtain ⟨-, -, hl_swnw, hl_swne, -, -, hw_swnw, hw_swne⟩ :=
    wf_node_quad_level hn4_l hn4_w
  apply p4_bool_eq_of_iff
  rw [isAlive_true_iff_mem_local, isAlive_true_iff_mem_local]
  have hBB : (2 ^ (k + 1) : Int) = (2 ^ k : Int) + (2 ^ k : Int) := by
    rw [pow_succ]; ring
  rw [mem_toGrid_node (nw := nw_sw) (ne := nw_se) (sw := sw_nw) (se := sw_ne), hl_nwsw]
  rw [mem_toGrid_node (nw := node nw_nw nw_ne nw_sw nw_se), hn1_l, hBB]
  rw [mem_toGrid_node (nw := nw_nw) (ne := nw_ne) (sw := nw_sw) (se := nw_se), hl_nwnw]
  rw [mem_toGrid_node (nw := sw_nw) (ne := sw_ne) (sw := sw_sw) (se := sw_se), hl_swnw]
  simp only [Int.zero_add, Int.add_zero]
  constructor
  · rintro ((h | h | h | h) | h | (h | h | h | h) | h)
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_lt _ _ _ x hw_nwnw h
      rw [hl_nwnw] at hr
      exfalso; omega
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_lt _ _ _ x hw_nwne h
      rw [hl_nwne] at hr
      exfalso; omega
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain ⟨-, hc⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
    · obtain ⟨-, hc⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
  · rintro (h | h | h | h)
    · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl h))))

/-- Accord parent / `n5` translaté de `(2^k, 2^k)` sur `[2^k, 3·2^k)²`. -/
private theorem p4_nw_parent_agree_n5 (k : Nat)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
      sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (hn1_l : (node nw_nw nw_ne nw_sw nw_se).level = k + 1)
    (hn1_w : (node nw_nw nw_ne nw_sw nw_se).wf = true)
    (hn2_l : (node nw_ne ne_nw nw_se ne_sw).level = k + 1)
    (hn2_w : (node nw_ne ne_nw nw_se ne_sw).wf = true)
    (hn4_l : (node nw_sw nw_se sw_nw sw_ne).level = k + 1)
    (hn4_w : (node nw_sw nw_se sw_nw sw_ne).wf = true)
    (hn5_l : (node nw_se ne_sw sw_ne se_nw).level = k + 1)
    (hn5_w : (node nw_se ne_sw sw_ne se_nw).wf = true)
    (x : Int × Int)
    (hx : (2 ^ k : Int) ≤ x.1 ∧ x.1 < (2 ^ k : Int) + (2 ^ k : Int) + (2 ^ k : Int) ∧
          (2 ^ k : Int) ≤ x.2 ∧ x.2 < (2 ^ k : Int) + (2 ^ k : Int) + (2 ^ k : Int)) :
    isAlive ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
        (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid (0, 0)) x
      = isAlive ((node nw_se ne_sw sw_ne se_nw).toGrid ((2 ^ k : Int), (2 ^ k : Int))) x := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hl_nwnw, hl_nwne, hl_nwsw, hl_nwse, hw_nwnw, hw_nwne, hw_nwsw, hw_nwse⟩ :=
    wf_node_quad_level hn1_l hn1_w
  obtain ⟨-, hl_nenw, -, -, -, hw_nenw, -, -⟩ :=
    wf_node_quad_level hn2_l hn2_w
  obtain ⟨-, -, hl_swnw, -, -, -, hw_swnw, -⟩ :=
    wf_node_quad_level hn4_l hn4_w
  obtain ⟨-, -, -, hl_senw, -, -, -, hw_senw⟩ :=
    wf_node_quad_level hn5_l hn5_w
  apply p4_bool_eq_of_iff
  rw [isAlive_true_iff_mem_local, isAlive_true_iff_mem_local]
  have hBB : (2 ^ (k + 1) : Int) = (2 ^ k : Int) + (2 ^ k : Int) := by
    rw [pow_succ]; ring
  rw [mem_toGrid_node (nw := nw_se) (ne := ne_sw) (sw := sw_ne) (se := se_nw), hl_nwse]
  rw [mem_toGrid_node (nw := node nw_nw nw_ne nw_sw nw_se), hn1_l, hBB]
  rw [mem_toGrid_node (nw := nw_nw) (ne := nw_ne) (sw := nw_sw) (se := nw_se), hl_nwnw]
  rw [mem_toGrid_node (nw := ne_nw) (ne := ne_ne) (sw := ne_sw) (se := ne_se), hl_nenw]
  rw [mem_toGrid_node (nw := sw_nw) (ne := sw_ne) (sw := sw_sw) (se := sw_se), hl_swnw]
  rw [mem_toGrid_node (nw := se_nw) (ne := se_ne) (sw := se_sw) (se := se_se), hl_senw]
  simp only [Int.zero_add, Int.add_zero]
  constructor
  · rintro ((h | h | h | h) | (h | h | h | h) | (h | h | h | h) | (h | h | h | h))
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_lt _ _ _ x hw_nwnw h
      rw [hl_nwnw] at hr
      exfalso; omega
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_lt _ _ _ x hw_nwne h
      rw [hl_nwne] at hr
      exfalso; omega
    · obtain ⟨-, hc⟩ := p4_mem_toGrid_lt _ _ _ x hw_nwsw h
      rw [hl_nwsw] at hc
      exfalso; omega
    · exact Or.inl h
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_lt _ _ _ x hw_nenw h
      rw [hl_nenw] at hr
      exfalso; omega
    · obtain ⟨-, hc⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
    · exact Or.inr (Or.inl h)
    · obtain ⟨-, hc⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
    · obtain ⟨-, hc⟩ := p4_mem_toGrid_lt _ _ _ x hw_swnw h
      rw [hl_swnw] at hc
      exfalso; omega
    · exact Or.inr (Or.inr (Or.inl h))
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
    · exact Or.inr (Or.inr (Or.inr h))
    · obtain ⟨-, hc⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
  · rintro (h | h | h | h)
    · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

/-- Accord parent / `n3` (enfant NE, mur NE) translaté de `(0, 2·2^k)` sur
    `[0, 2·2^k) × [2·2^k, 4·2^k)`. Le rectangle est exactement l'empreinte du
    quadrant NE du parent : seul l'enfant NE survit, les trois autres quadrants
    sont exclus par bornes. -/
private theorem p4_ne_parent_agree_n3 (k : Nat)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
      sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (hn1_l : (node nw_nw nw_ne nw_sw nw_se).level = k + 1)
    (hn1_w : (node nw_nw nw_ne nw_sw nw_se).wf = true)
    (x : Int × Int)
    (hx : 0 ≤ x.1 ∧ x.1 < (2 ^ k : Int) + (2 ^ k : Int) ∧
          (2 ^ k : Int) + (2 ^ k : Int) ≤ x.2 ∧
          x.2 < (2 ^ k : Int) + (2 ^ k : Int) + (2 ^ k : Int) + (2 ^ k : Int)) :
    isAlive ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
        (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid (0, 0)) x
      = isAlive ((node ne_nw ne_ne ne_sw ne_se).toGrid
          (0, (2 ^ k : Int) + (2 ^ k : Int))) x := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  apply p4_bool_eq_of_iff
  rw [isAlive_true_iff_mem_local, isAlive_true_iff_mem_local]
  have hBB : (2 ^ (k + 1) : Int) = (2 ^ k : Int) + (2 ^ k : Int) := by
    rw [pow_succ]; ring
  rw [mem_toGrid_node (nw := node nw_nw nw_ne nw_sw nw_se), hn1_l, hBB]
  simp only [Int.zero_add, Int.add_zero]
  constructor
  · rintro (h | h | h | h)
    · obtain ⟨-, hc⟩ := p4_mem_toGrid_lt _ _ _ x hn1_w h
      rw [hn1_l, hBB] at hc
      exfalso; omega
    · exact h
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
  · intro h
    exact Or.inr (Or.inl h)

/-- Accord parent / `n6` (mur NE) translaté de `(2^k, 2·2^k)` sur
    `[2^k, 3·2^k) × [2·2^k, 4·2^k)`. Le rectangle chevauche les quadrants NE et
    SE du parent ; à l'intérieur, seuls `ne_sw`/`ne_se` (moitié basse du NE) et
    `se_nw`/`se_ne` (moitié haute du SE) survivent — exactement les quatre
    enfants de `n6`. -/
private theorem p4_ne_parent_agree_n6 (k : Nat)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
      sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (hn1_l : (node nw_nw nw_ne nw_sw nw_se).level = k + 1)
    (hn1_w : (node nw_nw nw_ne nw_sw nw_se).wf = true)
    (hn3_l : (node ne_nw ne_ne ne_sw ne_se).level = k + 1)
    (hn3_w : (node ne_nw ne_ne ne_sw ne_se).wf = true)
    (hn6_l : (node ne_sw ne_se se_nw se_ne).level = k + 1)
    (hn6_w : (node ne_sw ne_se se_nw se_ne).wf = true)
    (hn7_l : (node sw_nw sw_ne sw_sw sw_se).level = k + 1)
    (hn7_w : (node sw_nw sw_ne sw_sw sw_se).wf = true)
    (x : Int × Int)
    (hx : (2 ^ k : Int) ≤ x.1 ∧ x.1 < (2 ^ k : Int) + (2 ^ k : Int) + (2 ^ k : Int) ∧
          (2 ^ k : Int) + (2 ^ k : Int) ≤ x.2 ∧
          x.2 < (2 ^ k : Int) + (2 ^ k : Int) + (2 ^ k : Int) + (2 ^ k : Int)) :
    isAlive ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
        (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid (0, 0)) x
      = isAlive ((node ne_sw ne_se se_nw se_ne).toGrid
          ((2 ^ k : Int), (2 ^ k : Int) + (2 ^ k : Int))) x := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hl_nenw, hl_nene, -, -, hw_nenw, hw_nene, -, -⟩ :=
    wf_node_quad_level hn3_l hn3_w
  obtain ⟨hl_nesw, -, hl_senw, -, -, -, -, -⟩ :=
    wf_node_quad_level hn6_l hn6_w
  apply p4_bool_eq_of_iff
  rw [isAlive_true_iff_mem_local, isAlive_true_iff_mem_local]
  have hBB : (2 ^ (k + 1) : Int) = (2 ^ k : Int) + (2 ^ k : Int) := by
    rw [pow_succ]; ring
  rw [mem_toGrid_node (nw := ne_sw) (ne := ne_se) (sw := se_nw) (se := se_ne), hl_nesw]
  rw [mem_toGrid_node (nw := node nw_nw nw_ne nw_sw nw_se), hn1_l, hBB]
  rw [mem_toGrid_node (nw := ne_nw) (ne := ne_ne) (sw := ne_sw) (se := ne_se), hl_nenw]
  rw [mem_toGrid_node (nw := se_nw) (ne := se_ne) (sw := se_sw) (se := se_se), hl_senw]
  simp only [Int.zero_add, Int.add_zero]
  constructor
  · rintro (h | (h | h | h | h) | h | (h | h | h | h))
    · obtain ⟨-, hc⟩ := p4_mem_toGrid_lt _ _ _ x hn1_w h
      rw [hn1_l, hBB] at hc
      exfalso; omega
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_lt _ _ _ x hw_nenw h
      rw [hl_nenw] at hr
      exfalso; omega
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_lt _ _ _ x hw_nene h
      rw [hl_nene] at hr
      exfalso; omega
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain ⟨-, hc⟩ := p4_mem_toGrid_lt _ _ _ x hn7_w h
      rw [hn7_l, hBB] at hc
      exfalso; omega
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
  · rintro (h | h | h | h)
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

/-! ### Étape 4 (préparation) — caractérisation par quadrant du supernœud résultat

Le supernœud `node R1 R2 R4 R5` (niveau `k+1`) est caractérisé quadrant par
quadrant : sur chaque quadrant de `[0, 2·2^k)²`, sa grille vaut l'évolution
`2^(k-1)` du nœud de recombinaison correspondant, au point re-translaté que
produit `centralCorrect_mem_shift`. Les trois autres quadrants sont exclus par
leurs propres bornes (les conjonctions de `centralCorrect_mem_shift`), via
`hA : 2^(k-1+1) = 2^k` (qui exige `1 ≤ k`). -/

/-- Quadrant NW du supernœud : `R1` seul survit sur `[0, 2^k)²`. -/
private theorem p4_nw_rside_char_nw (k : Nat) (hk1 : 1 ≤ k)
    (c1 c2 c4 c5 R1 R2 R4 R5 : MacroCell)
    (hR1 : R1 = hashlifeResultAux (k + 1) c1)
    (hR2 : R2 = hashlifeResultAux (k + 1) c2)
    (hR4 : R4 = hashlifeResultAux (k + 1) c4)
    (hR5 : R5 = hashlifeResultAux (k + 1) c5)
    (hR1_l : R1.level = k)
    (hcc1 : centralCorrect c1 (k - 1)) (hcc2 : centralCorrect c2 (k - 1))
    (hcc4 : centralCorrect c4 (k - 1)) (hcc5 : centralCorrect c5 (k - 1))
    (x : Int × Int)
    (hx : 0 ≤ x.1 ∧ x.1 < (2 ^ k : Int) ∧ 0 ≤ x.2 ∧ x.2 < (2 ^ k : Int)) :
    isAlive ((node R1 R2 R4 R5).toGrid (0, 0)) x
      = isAlive (evolve (2 ^ (k - 1)) (c1.toGrid (0, 0)))
          (x.1 - 0 + (2 ^ (k - 1) : Int), x.2 - 0 + (2 ^ (k - 1) : Int)) := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  have hA : (2 ^ (k - 1 + 1) : Int) = (2 ^ k : Int) := by
    have hk : k - 1 + 1 = k := by omega
    rw [hk]
  have hfuel : k + 1 = k - 1 + 2 := by omega
  rw [hfuel] at hR1 hR2 hR4 hR5
  apply p4_bool_eq_of_iff
  rw [isAlive_true_iff_mem_local]
  rw [p4_nw_offset_decomp k R1 R2 R4 R5 hR1_l x]
  rw [hR1, hR2, hR4, hR5]
  rw [centralCorrect_mem_shift c1 (k - 1) 0 0 x hcc1,
      centralCorrect_mem_shift c2 (k - 1) 0 (2 ^ k : Int) x hcc2,
      centralCorrect_mem_shift c4 (k - 1) (2 ^ k : Int) 0 x hcc4,
      centralCorrect_mem_shift c5 (k - 1) (2 ^ k : Int) (2 ^ k : Int) x hcc5]
  constructor
  · rintro (⟨H, hb1, hb2, hb3, hb4⟩ | ⟨-, hb1, hb2, hb3, hb4⟩ |
      ⟨-, hb1, hb2, hb3, hb4⟩ | ⟨-, hb1, hb2, hb3, hb4⟩)
    · exact H
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
  · intro H
    refine Or.inl ⟨H, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Quadrant NE du supernœud : `R2` seul survit sur `[0, 2^k) × [2^k, 2·2^k)`. -/
private theorem p4_nw_rside_char_ne (k : Nat) (hk1 : 1 ≤ k)
    (c1 c2 c4 c5 R1 R2 R4 R5 : MacroCell)
    (hR1 : R1 = hashlifeResultAux (k + 1) c1)
    (hR2 : R2 = hashlifeResultAux (k + 1) c2)
    (hR4 : R4 = hashlifeResultAux (k + 1) c4)
    (hR5 : R5 = hashlifeResultAux (k + 1) c5)
    (hR1_l : R1.level = k)
    (hcc1 : centralCorrect c1 (k - 1)) (hcc2 : centralCorrect c2 (k - 1))
    (hcc4 : centralCorrect c4 (k - 1)) (hcc5 : centralCorrect c5 (k - 1))
    (x : Int × Int)
    (hx : 0 ≤ x.1 ∧ x.1 < (2 ^ k : Int) ∧
          (2 ^ k : Int) ≤ x.2 ∧ x.2 < (2 ^ k : Int) + (2 ^ k : Int)) :
    isAlive ((node R1 R2 R4 R5).toGrid (0, 0)) x
      = isAlive (evolve (2 ^ (k - 1)) (c2.toGrid (0, 0)))
          (x.1 - 0 + (2 ^ (k - 1) : Int), x.2 - (2 ^ k : Int) + (2 ^ (k - 1) : Int)) := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  have hA : (2 ^ (k - 1 + 1) : Int) = (2 ^ k : Int) := by
    have hk : k - 1 + 1 = k := by omega
    rw [hk]
  have hfuel : k + 1 = k - 1 + 2 := by omega
  rw [hfuel] at hR1 hR2 hR4 hR5
  apply p4_bool_eq_of_iff
  rw [isAlive_true_iff_mem_local]
  rw [p4_nw_offset_decomp k R1 R2 R4 R5 hR1_l x]
  rw [hR1, hR2, hR4, hR5]
  rw [centralCorrect_mem_shift c1 (k - 1) 0 0 x hcc1,
      centralCorrect_mem_shift c2 (k - 1) 0 (2 ^ k : Int) x hcc2,
      centralCorrect_mem_shift c4 (k - 1) (2 ^ k : Int) 0 x hcc4,
      centralCorrect_mem_shift c5 (k - 1) (2 ^ k : Int) (2 ^ k : Int) x hcc5]
  constructor
  · rintro (⟨-, hb1, hb2, hb3, hb4⟩ | ⟨H, hb1, hb2, hb3, hb4⟩ |
      ⟨-, hb1, hb2, hb3, hb4⟩ | ⟨-, hb1, hb2, hb3, hb4⟩)
    · exfalso; omega
    · exact H
    · exfalso; omega
    · exfalso; omega
  · intro H
    refine Or.inr (Or.inl ⟨H, ?_, ?_, ?_, ?_⟩) <;> omega

/-- Quadrant SW du supernœud : `R4` seul survit sur `[2^k, 2·2^k) × [0, 2^k)`. -/
private theorem p4_nw_rside_char_sw (k : Nat) (hk1 : 1 ≤ k)
    (c1 c2 c4 c5 R1 R2 R4 R5 : MacroCell)
    (hR1 : R1 = hashlifeResultAux (k + 1) c1)
    (hR2 : R2 = hashlifeResultAux (k + 1) c2)
    (hR4 : R4 = hashlifeResultAux (k + 1) c4)
    (hR5 : R5 = hashlifeResultAux (k + 1) c5)
    (hR1_l : R1.level = k)
    (hcc1 : centralCorrect c1 (k - 1)) (hcc2 : centralCorrect c2 (k - 1))
    (hcc4 : centralCorrect c4 (k - 1)) (hcc5 : centralCorrect c5 (k - 1))
    (x : Int × Int)
    (hx : (2 ^ k : Int) ≤ x.1 ∧ x.1 < (2 ^ k : Int) + (2 ^ k : Int) ∧
          0 ≤ x.2 ∧ x.2 < (2 ^ k : Int)) :
    isAlive ((node R1 R2 R4 R5).toGrid (0, 0)) x
      = isAlive (evolve (2 ^ (k - 1)) (c4.toGrid (0, 0)))
          (x.1 - (2 ^ k : Int) + (2 ^ (k - 1) : Int), x.2 - 0 + (2 ^ (k - 1) : Int)) := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  have hA : (2 ^ (k - 1 + 1) : Int) = (2 ^ k : Int) := by
    have hk : k - 1 + 1 = k := by omega
    rw [hk]
  have hfuel : k + 1 = k - 1 + 2 := by omega
  rw [hfuel] at hR1 hR2 hR4 hR5
  apply p4_bool_eq_of_iff
  rw [isAlive_true_iff_mem_local]
  rw [p4_nw_offset_decomp k R1 R2 R4 R5 hR1_l x]
  rw [hR1, hR2, hR4, hR5]
  rw [centralCorrect_mem_shift c1 (k - 1) 0 0 x hcc1,
      centralCorrect_mem_shift c2 (k - 1) 0 (2 ^ k : Int) x hcc2,
      centralCorrect_mem_shift c4 (k - 1) (2 ^ k : Int) 0 x hcc4,
      centralCorrect_mem_shift c5 (k - 1) (2 ^ k : Int) (2 ^ k : Int) x hcc5]
  constructor
  · rintro (⟨-, hb1, hb2, hb3, hb4⟩ | ⟨-, hb1, hb2, hb3, hb4⟩ |
      ⟨H, hb1, hb2, hb3, hb4⟩ | ⟨-, hb1, hb2, hb3, hb4⟩)
    · exfalso; omega
    · exfalso; omega
    · exact H
    · exfalso; omega
  · intro H
    refine Or.inr (Or.inr (Or.inl ⟨H, ?_, ?_, ?_, ?_⟩)) <;> omega

/-- Quadrant SE du supernœud : `R5` seul survit sur `[2^k, 2·2^k)²`. -/
private theorem p4_nw_rside_char_se (k : Nat) (hk1 : 1 ≤ k)
    (c1 c2 c4 c5 R1 R2 R4 R5 : MacroCell)
    (hR1 : R1 = hashlifeResultAux (k + 1) c1)
    (hR2 : R2 = hashlifeResultAux (k + 1) c2)
    (hR4 : R4 = hashlifeResultAux (k + 1) c4)
    (hR5 : R5 = hashlifeResultAux (k + 1) c5)
    (hR1_l : R1.level = k)
    (hcc1 : centralCorrect c1 (k - 1)) (hcc2 : centralCorrect c2 (k - 1))
    (hcc4 : centralCorrect c4 (k - 1)) (hcc5 : centralCorrect c5 (k - 1))
    (x : Int × Int)
    (hx : (2 ^ k : Int) ≤ x.1 ∧ x.1 < (2 ^ k : Int) + (2 ^ k : Int) ∧
          (2 ^ k : Int) ≤ x.2 ∧ x.2 < (2 ^ k : Int) + (2 ^ k : Int)) :
    isAlive ((node R1 R2 R4 R5).toGrid (0, 0)) x
      = isAlive (evolve (2 ^ (k - 1)) (c5.toGrid (0, 0)))
          (x.1 - (2 ^ k : Int) + (2 ^ (k - 1) : Int),
           x.2 - (2 ^ k : Int) + (2 ^ (k - 1) : Int)) := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  have hA : (2 ^ (k - 1 + 1) : Int) = (2 ^ k : Int) := by
    have hk : k - 1 + 1 = k := by omega
    rw [hk]
  have hfuel : k + 1 = k - 1 + 2 := by omega
  rw [hfuel] at hR1 hR2 hR4 hR5
  apply p4_bool_eq_of_iff
  rw [isAlive_true_iff_mem_local]
  rw [p4_nw_offset_decomp k R1 R2 R4 R5 hR1_l x]
  rw [hR1, hR2, hR4, hR5]
  rw [centralCorrect_mem_shift c1 (k - 1) 0 0 x hcc1,
      centralCorrect_mem_shift c2 (k - 1) 0 (2 ^ k : Int) x hcc2,
      centralCorrect_mem_shift c4 (k - 1) (2 ^ k : Int) 0 x hcc4,
      centralCorrect_mem_shift c5 (k - 1) (2 ^ k : Int) (2 ^ k : Int) x hcc5]
  constructor
  · rintro (⟨-, hb1, hb2, hb3, hb4⟩ | ⟨-, hb1, hb2, hb3, hb4⟩ |
      ⟨-, hb1, hb2, hb3, hb4⟩ | ⟨H, hb1, hb2, hb3, hb4⟩)
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · exact H
  · intro H
    refine Or.inr (Or.inr (Or.inr ⟨H, ?_, ?_, ?_, ?_⟩)) <;> omega

end Life
end Conway
