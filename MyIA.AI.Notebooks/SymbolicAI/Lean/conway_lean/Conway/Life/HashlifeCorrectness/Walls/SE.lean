/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Conway.Life.HashlifeCorrectness.Walls.SE

Sub-module of `Conway.Life.HashlifeCorrectness`. Phase 3b multi-agent
prover targets (Epic #1453). Scope: /-- **c.90 §1 — SE overlap wall (DIAGONAL mirror of `p4_nw_overlap_wall`
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
/-- **c.90 §1 — SE overlap wall (DIAGONAL mirror of `p4_nw_overlap_wall`
    L2987; OW-authorized by #6875 mirror symmetry).**

    The residual grid-level overlap realignment for the SE quadrant: the
    once-half-stepped parent grid agrees, on the central light cone, with the
    SE wave-1 supercell `node R5 R6 R8 R9` read at the SE-anchored local
    point.

    **Anchor derivation (differs from a naive copy of the NW wall).** The SE
    supercell's origin sits at parent coordinate `(2^k + 2^(k-1), 2^k +
    2^(k-1))` (the SE outer offset `(2^(k+1), 2^(k+1))` re-centered by the
    half-step `2^(k-1)`), so the local point is `r - (2^k + 2^(k-1))` on BOTH
    coordinates — i.e. `r - 3·2^(k-1)`, the diagonal reflection of NW's
    `r - 2^(k-1)`. Because SE lies on the same diagonal as NW, the whole
    `p4_nw_g3_bridge` locality machinery (`evolve_shift` +
    `evolve_cone_agree`) mirrors verbatim with shift vector
    `(2^k + 2^(k-1), 2^k + 2^(k-1))` — see `p4_se_g3_bridge` below, which
    consumes this wall via `exact` (the faithful-extraction test, cf. c.43:
    sufficiency is compiler-checked each build; satisfiability is the
    residual obstruction, same map A/B/C as the NW wall's c.8124 docstring,
    mutatis mutandis under the diagonal reflection).

    Sorry count: this is the ONE sorry introduced by the c.90 SE-arm port
    (the port closes the se-quadrant bullet sorry in `p4_succ_membership`,
    net FLAT). ai-01 keeps the proof (tree-lock #6875). -/
private theorem p4_se_overlap_wall
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R5 R6 R8 R9 : MacroCell)
    (hR5 : R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
    (hR6 : R6 = hashlifeResultAux (k + 1) (node ne_sw ne_se se_nw se_ne))
    (hR8 : R8 = hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
    (hR9 : R9 = hashlifeResultAux (k + 1) (node se_nw se_ne se_sw se_se))
    (hR5_l : R5.level = k) (hR6_l : R6.level = k)
    (hR8_l : R8.level = k) (hR9_l : R9.level = k)
    (hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1))
    (hcc6 : centralCorrect (node ne_sw ne_se se_nw se_ne) (k - 1))
    (hcc8 : centralCorrect (node sw_ne se_nw sw_se se_sw) (k - 1))
    (hcc9 : centralCorrect (node se_nw se_ne se_sw se_se) (k - 1))
    (p : Int × Int) :
    ∀ r ∈ lightCone p (2^k),
      isAlive (evolve (2^(k - 1))
          ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
                 (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
            (0, 0))) r
        = isAlive ((node R5 R6 R8 R9).toGrid (0, 0))
            (r.1 - ((2^k : Int) + (2^(k - 1) : Int)),
             r.2 - ((2^k : Int) + (2^(k - 1) : Int))) := by
  sorry

/-- **c.90 §2 — SE G3 bridge (diagonal mirror of `p4_nw_g3_bridge` L3080,
    proven sorry-free by the same locality machinery).**

    Both quadrants on the main diagonal have a SYMMETRIC point translation
    (`p - 2^(k+1) + 2^(k-1) = p - 3·2^(k-1)` on both coordinates), so the
    NW bridge's proof ports verbatim: expose the symmetric half-step form,
    simplify the eval point, shift the supercell grid by
    `(2^k + 2^(k-1), 2^k + 2^(k-1))` via `evolve_shift`/`isAlive_shift`,
    then transport the cone agreement through the outer `evolve (2^(k-1))`
    with `evolve_cone_agree`. The residual is exactly the (a) inner
    agreement `p4_se_overlap_wall` above — consumed here via `exact`, which
    IS the faithful-extraction test for the wall's statement (an
    under-hypothesized or mis-anchored wall would not close this goal;
    cf. the #8768 `R_j.level = k` load-bearing note on the NW bridge). -/
private theorem p4_se_g3_bridge
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R5 R6 R8 R9 : MacroCell)
    (hR5 : R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
    (hR6 : R6 = hashlifeResultAux (k + 1) (node ne_sw ne_se se_nw se_ne))
    (hR8 : R8 = hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
    (hR9 : R9 = hashlifeResultAux (k + 1) (node se_nw se_ne se_sw se_se))
    (hR5_l : R5.level = k) (hR6_l : R6.level = k)
    (hR8_l : R8.level = k) (hR9_l : R9.level = k)
    (hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1))
    (hcc6 : centralCorrect (node ne_sw ne_se se_nw se_ne) (k - 1))
    (hcc8 : centralCorrect (node sw_ne se_nw sw_se se_sw) (k - 1))
    (hcc9 : centralCorrect (node se_nw se_ne se_sw se_se) (k - 1))
    (p : Int × Int) :
    isAlive (evolve (2^k)
        ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
          (0, 0))) p
      = isAlive (evolve (2^(k - 1)) ((node R5 R6 R8 R9).toGrid (0, 0)))
          (p.1 - ((2^k + (2^k : Int))) + (2^(k - 1) : Int),
           p.2 - ((2^k + (2^k : Int))) + (2^(k - 1) : Int)) := by
  rw [evolve_half_step k hk1]
  -- Point simplification: `- 2^(k+1) + 2^(k-1) = - 3·2^(k-1)` (diagonal,
  -- both coordinates — the SE analog of NW's `- 2^k + 2^(k-1) = - 2^(k-1)`).
  have h2k : (2^k : Int) = (2^(k - 1) : Int) + (2^(k - 1) : Int) := by
    have hn : 2^k = 2^(k - 1) + 2^(k - 1) := by
      set m := k - 1 with hm
      have hkm : k = m + 1 := by omega
      rw [hkm, Nat.pow_succ]; ring
    exact mod_cast hn
  have hpt1 : p.1 - ((2^k + (2^k : Int))) + (2^(k - 1) : Int)
      = p.1 - ((2^k : Int) + (2^(k - 1) : Int)) := by omega
  have hpt2 : p.2 - ((2^k + (2^k : Int))) + (2^(k - 1) : Int)
      = p.2 - ((2^k : Int) + (2^(k - 1) : Int)) := by omega
  rw [hpt1, hpt2]
  -- RHS evals at `p - (2^k + 2^(k-1))`; rewrite to eval at `p` on a shifted grid.
  have hR : isAlive (evolve (2^(k - 1)) ((node R5 R6 R8 R9).toGrid (0, 0)))
        (p.1 - ((2^k : Int) + (2^(k - 1) : Int)), p.2 - ((2^k : Int) + (2^(k - 1) : Int)))
      = isAlive (evolve (2^(k - 1))
          (shift ((2^k : Int) + (2^(k - 1) : Int), (2^k : Int) + (2^(k - 1) : Int))
            ((node R5 R6 R8 R9).toGrid (0, 0)))) p := by
    rw [← evolve_shift, isAlive_shift]
  rw [hR]
  -- Both sides eval at `p`. Transport through the outer `evolve (2^(k-1))`.
  apply evolve_cone_agree (t := 0) (u := 2^(k - 1))
  · -- h_cone : ∀ r ∈ lightCone p (2 * (0 + 2^(k-1))), ...
    intro r hr
    rw [isAlive_shift]
    have h2u : 2 * (0 + 2^(k - 1)) = 2^k := by
      set m := k - 1 with hm
      have hkm : k = m + 1 := by omega
      rw [hkm, Nat.pow_succ]; ring
    rw [h2u] at hr
    exact p4_se_overlap_wall k hk1
      nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
      sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
      R5 R6 R8 R9 hR5 hR6 hR8 hR9 hR5_l hR6_l hR8_l hR9_l
      hcc5 hcc6 hcc8 hcc9 p r hr
  · -- hq : p ∈ lightCone p (2 * 0)
    exact self_mem_lightCone p 0

/-- **c.90 §3 — SE supercell agreement (diagonal mirror of
    `p4_nw_supercell_agree` L3221; proven from the bridge, NOT sorry'd).**

    Unlike the NE/SW counterparts (whose agree lemmas carry their own inline
    `sorry` after the half-step fold), the SE agreement is fully discharged
    by `p4_se_g3_bridge` — the diagonal symmetry makes the bridge machinery
    portable, so the SE chain reaches the same structural depth as NW: the
    single residual lives in the named wall, extraction-tested at every
    build. -/
private theorem p4_se_supercell_agree
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R5 R6 R8 R9 : MacroCell)
    (hR5 : R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
    (hR6 : R6 = hashlifeResultAux (k + 1) (node ne_sw ne_se se_nw se_ne))
    (hR8 : R8 = hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
    (hR9 : R9 = hashlifeResultAux (k + 1) (node se_nw se_ne se_sw se_se))
    (hR5_l : R5.level = k) (hR6_l : R6.level = k)
    (hR8_l : R8.level = k) (hR9_l : R9.level = k)
    (hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1))
    (hcc6 : centralCorrect (node ne_sw ne_se se_nw se_ne) (k - 1))
    (hcc8 : centralCorrect (node sw_ne se_nw sw_se se_sw) (k - 1))
    (hcc9 : centralCorrect (node se_nw se_ne se_sw se_se) (k - 1))
    (p : Int × Int) :
    isAlive (evolve (2^(k - 1)) (evolve (2^(k - 1))
        ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
          (0, 0)))) p
      = isAlive (evolve (2^(k - 1)) ((node R5 R6 R8 R9).toGrid (0, 0)))
          (p.1 - ((2^k + (2^k : Int))) + (2^(k - 1) : Int),
           p.2 - ((2^k + (2^k : Int))) + (2^(k - 1) : Int)) := by
  -- Fold the LHS double half-step into a single `evolve 2^k`, then discharge
  -- via the named bridge (the `exact` IS the specialization test — cf. NW).
  rw [← evolve_half_step k hk1]
  exact p4_se_g3_bridge k hk1
    nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
    sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
    R5 R6 R8 R9 hR5 hR6 hR8 hR9
    hR5_l hR6_l hR8_l hR9_l hcc5 hcc6 hcc8 hcc9 p

set_option maxHeartbeats 1000000 in
/-- **c.90 §4 — SE membership arm (opaque-binder, sorry-free wiring —
    diagonal mirror of the NW arm L3273 / same skeleton as SW arm L3751).**
    Discharges the SE quadrant of `p4_succ_membership` over OPAQUE wave-1
    results `R5 R6 R8 R9` (SE supercell wave-1 sub-cells), with a fresh
    heartbeat budget. The `p4_succ_membership` call site merely *applies*
    this arm with `R_j := hashlifeResultAux (k+1) n_j` (pure substitution,
    no whnf). The one residual sorry lives in `p4_se_overlap_wall` (via
    `p4_se_supercell_agree` → `p4_se_g3_bridge`); here everything is wired.

    Chain: `p4_se_shift_lemma.mp` (supercell isAlive at `p'` + window bounds
    at SE outer offset `(2^k + 2^k, 2^k + 2^k)`) → `mem_restrictGridTo` →
    `isAlive_true_iff_mem` + `evolve_half_step` + `p4_se_supercell_agree`
    fold the membership into `hsup.1`; the four coordinate bounds discharge
    from the shift window by omega (both row AND column use the SW row
    pattern — the SE offset is outer on both axes).

    Same `hout_nw` opaque-binder pattern as the NE/SW arms: both SE offsets
    are anchored on `2^out_nw.level` (the outer NW supercell's level — the
    common reference for all four quadrants). -/
private theorem p4_se_membership_arm
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R5 R6 R8 R9 : MacroCell)
    (hR5 : R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
    (hR6 : R6 = hashlifeResultAux (k + 1) (node ne_sw ne_se se_nw se_ne))
    (hR8 : R8 = hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
    (hR9 : R9 = hashlifeResultAux (k + 1) (node se_nw se_ne se_sw se_se))
    (hn5_l : (node nw_se ne_sw sw_ne se_nw).level = k + 1)
    (hn6_l : (node ne_sw ne_se se_nw se_ne).level = k + 1)
    (hn8_l : (node sw_ne se_nw sw_se se_sw).level = k + 1)
    (hn9_l : (node se_nw se_ne se_sw se_se).level = k + 1)
    (hn5_w : (node nw_se ne_sw sw_ne se_nw).wf = true)
    (hn6_w : (node ne_sw ne_se se_nw se_ne).wf = true)
    (hn8_w : (node sw_ne se_nw sw_se se_sw).wf = true)
    (hn9_w : (node se_nw se_ne se_sw se_se).wf = true)
    (hR5_l : R5.level = k) (hR6_l : R6.level = k)
    (hR8_l : R8.level = k) (hR9_l : R9.level = k)
    (hR5_w : R5.wf = true) (hR6_w : R6.wf = true)
    (hR8_w : R8.wf = true) (hR9_w : R9.wf = true)
    (ih : ∀ (c' : MacroCell) (j : Nat), j < k → c'.wf = true → c'.level = j + 2 →
      centralCorrect c' j)
    (p : Int × Int)
    -- Geometric offset: SE supercell `(node R5 R6 R8 R9)` lives at outer
    -- offset `(2^k + 2^out_nw.level, 2^k + 2^out_nw.level)` per
    -- `mem_toGrid_node` (both the SE row and the SE column of the outer
    -- quadrants get the `+ 2^out_nw.level` shift). The arm takes
    -- `hout_nw_l : out_nw.level = k` and bridges `2^out_nw.level = 2^k` via
    -- `congrArg` (cf. c.8122/c.8123), applied to BOTH coordinates at once.
    (hout_nw : MacroCell)
    (hout_nw_l : hout_nw.level = k)
    (hse : p ∈ (hashlifeResultAux (k + 1) (node R5 R6 R8 R9)).toGrid
            ((2^k : Int) + (2^hout_nw.level : Int),
             (2^k : Int) + (2^hout_nw.level : Int))) :
    p ∈ restrictGridTo (evolve (2^k)
        ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
          (0, 0)))
        (2^k : Int) (2^(k+1)) := by
  -- Fuel-align (k+1) → (k-1)+2 on the OPAQUE-node membership, then bridge the
  -- SE offsets `2^hout_nw.level` to literal `2^k` via `congrArg` (both axes
  -- rewritten by the same equation). Then the SE shift lemma's `.mp` is
  -- whnf-clean over opaque `R_j` (fresh budget).
  rw [show (k + 1) = (k - 1) + 2 from by omega] at hse
  have hpow : (2^hout_nw.level : Int) = (2^k : Int) :=
    congrArg (fun n => (2^n : Int)) hout_nw_l
  have hbridge : ((2^k : Int) + (2^hout_nw.level : Int)) = (2^k + (2^k : Int)) := by
    rw [hpow]
  rw [hbridge] at hse
  have hsup := (p4_se_shift_lemma k hk1 R5 R6 R8 R9
      hR5_l hR6_l hR8_l hR9_l hR5_w hR6_w hR8_w hR9_w ih p).mp hse
  -- hsup.1 : isAlive (evolve 2^(k-1) ((node R5 R6 R8 R9).toGrid 0)) p' = true
  -- hsup.2 : (2^k + 2^k) ≤ p.1 ∧ p.1 < (2^k + 2^k) + 2^((k-1)+1) ∧
  --          (2^k + 2^k) ≤ p.2 ∧ p.2 < (2^k + 2^k) + 2^((k-1)+1)
  rw [mem_restrictGridTo]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- membership: fold `evolve 2^k` via half-step + SE supercell agreement into hsup.1
    rw [← isAlive_true_iff_mem_local]
    rw [evolve_half_step k hk1]
    -- The 4 wave-1 sub-cells of the SE supercell are n5/n6/n8/n9 (level k+1,
    -- G2 at level k-1). Each `centralCorrect n_j (k-1)` is the IH projection
    -- (j = k-1 < k by hk1, level j+2 = k+1 matches).
    have hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1) :=
      ih _ (k - 1) (by omega) hn5_w (by rw [hn5_l]; omega)
    have hcc6 : centralCorrect (node ne_sw ne_se se_nw se_ne) (k - 1) :=
      ih _ (k - 1) (by omega) hn6_w (by rw [hn6_l]; omega)
    have hcc8 : centralCorrect (node sw_ne se_nw sw_se se_sw) (k - 1) :=
      ih _ (k - 1) (by omega) hn8_w (by rw [hn8_l]; omega)
    have hcc9 : centralCorrect (node se_nw se_ne se_sw se_se) (k - 1) :=
      ih _ (k - 1) (by omega) hn9_w (by rw [hn9_l]; omega)
    rw [p4_se_supercell_agree k hk1
          nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
          sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
          R5 R6 R8 R9 hR5 hR6 hR8 hR9
          hR5_l hR6_l hR8_l hR9_l hcc5 hcc6 hcc8 hcc9 p]
    exact hsup.1
  · -- 2^k ≤ p.1 (we have hsup.2.1 : (2^k + 2^k) ≤ p.1, strictly stronger)
    exact le_trans (by norm_num : (2^k : Int) ≤ 2^k + 2^k) hsup.2.1
  · -- p.1 < 2^k + 2^(k+1) (= 2^k + 2^k + 2^k = 3·2^k)
    have hb := hsup.2.2.1
    have he : (k - 1) + 1 = k := by omega
    rw [he] at hb
    have hbridge : ((2 ^ (k + 1) : Nat) : Int) = 2 ^ k + 2 ^ k := by
      push_cast; rw [pow_succ]; ring
    have hpos : (0 : Int) < 2 ^ k := pow_pos (by norm_num) k
    rw [hbridge]
    omega
  · -- 2^k ≤ p.2 (we have hsup.2.2.2.1 : (2^k + 2^k) ≤ p.2, strictly stronger)
    exact le_trans (by norm_num : (2^k : Int) ≤ 2^k + 2^k) hsup.2.2.2.1
  · -- p.2 < 2^k + 2^(k+1) (we have hsup.2.2.2.2 : p.2 < (2^k + 2^k) + 2^k)
    have hb := hsup.2.2.2.2
    have he : (k - 1) + 1 = k := by omega
    rw [he] at hb
    have hbridge : ((2 ^ (k + 1) : Nat) : Int) = 2 ^ k + 2 ^ k := by
      push_cast; rw [pow_succ]; ring
    have hpos : (0 : Int) < 2 ^ k := pow_pos (by norm_num) k
    rw [hbridge]
    omega

/-- **NW membership arm, reciprocal direction (mpr assembly).**
    Mirror of `p4_nw_membership_arm` for the `mpr` case of
    `p4_succ_membership`: FROM the global cell-state `hmem` (the RHS
    membership under `evolve 2^k`) plus the NW-quadrant router bounds
    `hp1..hp4` (from `quad_partition_bounds`), TO the node-quadrant
    membership at anchor `(2^k, 2^k)`. All ingredients are the mp arm's,
    consumed backwards: `p4_nw_shift_lemma.mpr` needs (a) the shift window
    (from `hp1..hp4`, since `2^((k-1)+1) = 2^k`) and (b) the supercell
    `isAlive` at the shifted point — obtained from `hmem` by folding
    `evolve 2^k` into the double half-step (`evolve_half_step`) and crossing
    `p4_nw_supercell_agree` RIGHT-to-LEFT (`rw [← …]`; the agreement is a
    Bool equation, hence reversible — a sorried agreement stays usable in
    `rw`, so this wiring is textually sorry-free for all four quadrants). -/
private theorem p4_nw_membership_arm_rev
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R1 R2 R4 R5 : MacroCell)
    (hR1 : R1 = hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
    (hR2 : R2 = hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
    (hR4 : R4 = hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
    (hR5 : R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
    (hn1_l : (node nw_nw nw_ne nw_sw nw_se).level = k + 1)
    (hn2_l : (node nw_ne ne_nw nw_se ne_sw).level = k + 1)
    (hn4_l : (node nw_sw nw_se sw_nw sw_ne).level = k + 1)
    (hn5_l : (node nw_se ne_sw sw_ne se_nw).level = k + 1)
    (hn1_w : (node nw_nw nw_ne nw_sw nw_se).wf = true)
    (hn2_w : (node nw_ne ne_nw nw_se ne_sw).wf = true)
    (hn4_w : (node nw_sw nw_se sw_nw sw_ne).wf = true)
    (hn5_w : (node nw_se ne_sw sw_ne se_nw).wf = true)
    (hR1_l : R1.level = k) (hR2_l : R2.level = k)
    (hR4_l : R4.level = k) (hR5_l : R5.level = k)
    (hR1_w : R1.wf = true) (hR2_w : R2.wf = true)
    (hR4_w : R4.wf = true) (hR5_w : R5.wf = true)
    (ih : ∀ (c' : MacroCell) (j : Nat), j < k → c'.wf = true → c'.level = j + 2 →
      centralCorrect c' j)
    (p : Int × Int)
    (hmem : p ∈ evolve (2^k)
        ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
          (0, 0)))
    (hp1 : (2^k : Int) ≤ p.1) (hp2 : p.1 < (2^k : Int) + 2^k)
    (hp3 : (2^k : Int) ≤ p.2) (hp4 : p.2 < (2^k : Int) + 2^k) :
    p ∈ (hashlifeResultAux (k + 1) (node R1 R2 R4 R5)).toGrid
        ((2^k : Int), (2^k : Int)) := by
  -- Fuel-align (k+1) → (k-1)+2 on the GOAL, then enter through the shift
  -- lemma's `.mpr` (whnf-clean over opaque `R_i`, fresh budget).
  rw [show (k + 1) = (k - 1) + 2 from by omega]
  have he : (k - 1) + 1 = k := by omega
  have hw : (2^k : Int) ≤ p.1 ∧ p.1 < (2^k : Int) + 2^((k - 1) + 1) ∧
            (2^k : Int) ≤ p.2 ∧ p.2 < (2^k : Int) + 2^((k - 1) + 1) := by
    rw [he]
    exact ⟨hp1, by omega, hp3, by omega⟩
  refine (p4_nw_shift_lemma k hk1 R1 R2 R4 R5
      hR1_l hR2_l hR4_l hR5_l hR1_w hR2_w hR4_w hR5_w ih p).mpr ⟨?_, hw⟩
  -- Residual: the supercell isAlive at the shifted point. Fold it back into
  -- `hmem` via the supercell agreement (Bool equation, consumed R-to-L) +
  -- the half-step composition, then the isAlive/mem bridge.
  have hcc1 : centralCorrect (node nw_nw nw_ne nw_sw nw_se) (k - 1) :=
    ih _ (k - 1) (by omega) hn1_w (by rw [hn1_l]; omega)
  have hcc2 : centralCorrect (node nw_ne ne_nw nw_se ne_sw) (k - 1) :=
    ih _ (k - 1) (by omega) hn2_w (by rw [hn2_l]; omega)
  have hcc4 : centralCorrect (node nw_sw nw_se sw_nw sw_ne) (k - 1) :=
    ih _ (k - 1) (by omega) hn4_w (by rw [hn4_l]; omega)
  have hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1) :=
    ih _ (k - 1) (by omega) hn5_w (by rw [hn5_l]; omega)
  rw [← p4_nw_supercell_agree k hk1
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
        R1 R2 R4 R5 hR1 hR2 hR4 hR5
        hn1_l hn2_l hn4_l hn5_l hn1_w hn2_w hn4_w hn5_w
        hR1_l hR2_l hR4_l hR5_l hcc1 hcc2 hcc4 hcc5 p hw]
  rw [← evolve_half_step k hk1]
  rw [isAlive_true_iff_mem_local]
  exact hmem

set_option maxHeartbeats 4000000 in
/-- **NE membership arm, reciprocal direction (mpr assembly — mirror of
    `p4_ne_membership_arm`).** Same opaque-binder + `hout_nw` level-anchor
    pattern as the mp arm. The inline `congrArg` bridge normalizes the GOAL's
    anchor `2^k + 2^hout_nw.level` to the literal `2^k + 2^k` with zero
    residual context equations (heartbeat lesson: leftover `hpow`/`hbridge`
    hypotheses with `2^hout_nw.level` atoms poison every downstream `omega`
    preprocessing pass — cumulative whnf exhaustion, cf. the mp arm). 4M
    budget: same wide signature (16 binders + 5 R + `hn1..hn7`). -/
private theorem p4_ne_membership_arm_rev
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R1 R2 R3 R5 R6 : MacroCell)
    (hR1 : R1 = hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
    (hR2 : R2 = hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
    (hR3 : R3 = hashlifeResultAux (k + 1) (node ne_nw ne_ne ne_sw ne_se))
    (hR5 : R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
    (hR6 : R6 = hashlifeResultAux (k + 1) (node ne_sw ne_se se_nw se_ne))
    (hn1_l : (node nw_nw nw_ne nw_sw nw_se).level = k + 1)
    (hn2_l : (node nw_ne ne_nw nw_se ne_sw).level = k + 1)
    (hn3_l : (node ne_nw ne_ne ne_sw ne_se).level = k + 1)
    (hn4_l : (node nw_sw nw_se sw_nw sw_ne).level = k + 1)
    (hn5_l : (node nw_se ne_sw sw_ne se_nw).level = k + 1)
    (hn6_l : (node ne_sw ne_se se_nw se_ne).level = k + 1)
    (hn7_l : (node sw_nw sw_ne sw_sw sw_se).level = k + 1)
    (hn1_w : (node nw_nw nw_ne nw_sw nw_se).wf = true)
    (hn2_w : (node nw_ne ne_nw nw_se ne_sw).wf = true)
    (hn3_w : (node ne_nw ne_ne ne_sw ne_se).wf = true)
    (hn4_w : (node nw_sw nw_se sw_nw sw_ne).wf = true)
    (hn5_w : (node nw_se ne_sw sw_ne se_nw).wf = true)
    (hn6_w : (node ne_sw ne_se se_nw se_ne).wf = true)
    (hn7_w : (node sw_nw sw_ne sw_sw sw_se).wf = true)
    (hR1_l : R1.level = k) (hR2_l : R2.level = k) (hR3_l : R3.level = k)
    (hR5_l : R5.level = k) (hR6_l : R6.level = k)
    (hR1_w : R1.wf = true) (hR2_w : R2.wf = true) (hR3_w : R3.wf = true)
    (hR5_w : R5.wf = true) (hR6_w : R6.wf = true)
    (ih : ∀ (c' : MacroCell) (j : Nat), j < k → c'.wf = true → c'.level = j + 2 →
      centralCorrect c' j)
    (p : Int × Int)
    (hout_nw : MacroCell)
    (hout_nw_l : hout_nw.level = k)
    (hmem : p ∈ evolve (2^k)
        ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
          (0, 0)))
    (hp1 : (2^k : Int) ≤ p.1) (hp2 : p.1 < (2^k : Int) + 2^k)
    (hp3 : (2^k : Int) + 2^k ≤ p.2) (hp4 : p.2 < (2^k : Int) + 2*2^k) :
    p ∈ (hashlifeResultAux (k + 1) (node R2 R3 R5 R6)).toGrid
        ((2^k : Int), (2^k + (2^hout_nw.level : Int))) := by
  -- Bridge the GOAL's anchor to the literal form (inline, no residual
  -- equations), fuel-align, then the NE shift lemma's `.mpr`.
  rw [show (2^k + (2^hout_nw.level : Int)) = (2^k + (2^k : Int)) from by
    rw [congrArg (fun n => (2^n : Int)) hout_nw_l]]
  rw [show (k + 1) = (k - 1) + 2 from by omega]
  have he : (k - 1) + 1 = k := by omega
  have hw : (2^k : Int) ≤ p.1 ∧ p.1 < (2^k : Int) + 2^((k - 1) + 1) ∧
            ((2^k + (2^k : Int))) ≤ p.2 ∧
              p.2 < ((2^k + (2^k : Int))) + 2^((k - 1) + 1) := by
    rw [he]
    exact ⟨hp1, by omega, hp3, by omega⟩
  refine (p4_ne_shift_lemma k hk1 R2 R3 R5 R6
      hR2_l hR3_l hR5_l hR6_l hR2_w hR3_w hR5_w hR6_w ih p).mpr ⟨?_, hw⟩
  have hcc2 : centralCorrect (node nw_ne ne_nw nw_se ne_sw) (k - 1) :=
    ih _ (k - 1) (by omega) hn2_w (by rw [hn2_l]; omega)
  have hcc3 : centralCorrect (node ne_nw ne_ne ne_sw ne_se) (k - 1) :=
    ih _ (k - 1) (by omega) hn3_w (by rw [hn3_l]; omega)
  have hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1) :=
    ih _ (k - 1) (by omega) hn5_w (by rw [hn5_l]; omega)
  have hcc6 : centralCorrect (node ne_sw ne_se se_nw se_ne) (k - 1) :=
    ih _ (k - 1) (by omega) hn6_w (by rw [hn6_l]; omega)
  rw [← p4_ne_supercell_agree k hk1
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
        R2 R3 R5 R6 hR2 hR3 hR5 hR6
        hn1_l hn2_l hn3_l hn4_l hn5_l hn6_l hn7_l
        hn1_w hn2_w hn3_w hn4_w hn5_w hn6_w hn7_w
        hR2_l hR3_l hR5_l hR6_l hcc2 hcc3 hcc5 hcc6 p hw]
  rw [← evolve_half_step k hk1]
  rw [isAlive_true_iff_mem_local]
  exact hmem

set_option maxHeartbeats 1000000 in
/-- **SW membership arm, reciprocal direction (mpr assembly — mirror of
    `p4_sw_membership_arm`, NW-SE reflection of the NE rev arm).**
    `p4_sw_supercell_agree` is still sorried (po-2023 perimeter, #6724) but
    remains usable in `rw` — the wiring here is textually sorry-free and
    completes at the axiom level the day the SW wall closes. -/
private theorem p4_sw_membership_arm_rev
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R4 R5 R7 R8 : MacroCell)
    (hR4 : R4 = hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
    (hR5 : R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
    (hR7 : R7 = hashlifeResultAux (k + 1) (node sw_nw sw_ne sw_sw sw_se))
    (hR8 : R8 = hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
    (hn4_l : (node nw_sw nw_se sw_nw sw_ne).level = k + 1)
    (hn5_l : (node nw_se ne_sw sw_ne se_nw).level = k + 1)
    (hn7_l : (node sw_nw sw_ne sw_sw sw_se).level = k + 1)
    (hn8_l : (node sw_ne se_nw sw_se se_sw).level = k + 1)
    (hn4_w : (node nw_sw nw_se sw_nw sw_ne).wf = true)
    (hn5_w : (node nw_se ne_sw sw_ne se_nw).wf = true)
    (hn7_w : (node sw_nw sw_ne sw_sw sw_se).wf = true)
    (hn8_w : (node sw_ne se_nw sw_se se_sw).wf = true)
    (hR4_l : R4.level = k) (hR5_l : R5.level = k)
    (hR7_l : R7.level = k) (hR8_l : R8.level = k)
    (hR4_w : R4.wf = true) (hR5_w : R5.wf = true)
    (hR7_w : R7.wf = true) (hR8_w : R8.wf = true)
    (ih : ∀ (c' : MacroCell) (j : Nat), j < k → c'.wf = true → c'.level = j + 2 →
      centralCorrect c' j)
    (p : Int × Int)
    (hout_nw : MacroCell)
    (hout_nw_l : hout_nw.level = k)
    (hmem : p ∈ evolve (2^k)
        ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
          (0, 0)))
    (hp1 : (2^k : Int) + 2^k ≤ p.1) (hp2 : p.1 < (2^k : Int) + 2*2^k)
    (hp3 : (2^k : Int) ≤ p.2) (hp4 : p.2 < (2^k : Int) + 2^k) :
    p ∈ (hashlifeResultAux (k + 1) (node R4 R5 R7 R8)).toGrid
        ((2^k : Int) + (2^hout_nw.level : Int), (2^k : Int)) := by
  rw [show ((2^k : Int) + (2^hout_nw.level : Int)) = (2^k + (2^k : Int)) from by
    rw [congrArg (fun n => (2^n : Int)) hout_nw_l]]
  rw [show (k + 1) = (k - 1) + 2 from by omega]
  have he : (k - 1) + 1 = k := by omega
  have hw : ((2^k + (2^k : Int))) ≤ p.1 ∧
              p.1 < ((2^k + (2^k : Int))) + 2^((k - 1) + 1) ∧
            (2^k : Int) ≤ p.2 ∧ p.2 < (2^k : Int) + 2^((k - 1) + 1) := by
    rw [he]
    exact ⟨hp1, by omega, hp3, by omega⟩
  refine (p4_sw_shift_lemma k hk1 R4 R5 R7 R8
      hR4_l hR5_l hR7_l hR8_l hR4_w hR5_w hR7_w hR8_w ih p).mpr ⟨?_, hw⟩
  have hcc4 : centralCorrect (node nw_sw nw_se sw_nw sw_ne) (k - 1) :=
    ih _ (k - 1) (by omega) hn4_w (by rw [hn4_l]; omega)
  have hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1) :=
    ih _ (k - 1) (by omega) hn5_w (by rw [hn5_l]; omega)
  have hcc7 : centralCorrect (node sw_nw sw_ne sw_sw sw_se) (k - 1) :=
    ih _ (k - 1) (by omega) hn7_w (by rw [hn7_l]; omega)
  have hcc8 : centralCorrect (node sw_ne se_nw sw_se se_sw) (k - 1) :=
    ih _ (k - 1) (by omega) hn8_w (by rw [hn8_l]; omega)
  rw [← p4_sw_supercell_agree k hk1
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
        R4 R5 R7 R8 hR4 hR5 hR7 hR8
        hR4_l hR5_l hR7_l hR8_l hcc4 hcc5 hcc7 hcc8 p]
  rw [← evolve_half_step k hk1]
  rw [isAlive_true_iff_mem_local]
  exact hmem

set_option maxHeartbeats 1000000 in
/-- **SE membership arm, reciprocal direction (mpr assembly — mirror of
    `p4_se_membership_arm`, diagonal reflection of the NW rev arm).**
    Both SE anchor coordinates carry `2^hout_nw.level`; the single inline
    bridge `rw` rewrites both occurrences at once (same as the mp arm).
    `p4_se_supercell_agree` rests on the sorried `p4_se_overlap_wall`
    (po-2023 perimeter) but stays usable in `rw` — wiring sorry-free. -/
private theorem p4_se_membership_arm_rev
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R5 R6 R8 R9 : MacroCell)
    (hR5 : R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
    (hR6 : R6 = hashlifeResultAux (k + 1) (node ne_sw ne_se se_nw se_ne))
    (hR8 : R8 = hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
    (hR9 : R9 = hashlifeResultAux (k + 1) (node se_nw se_ne se_sw se_se))
    (hn5_l : (node nw_se ne_sw sw_ne se_nw).level = k + 1)
    (hn6_l : (node ne_sw ne_se se_nw se_ne).level = k + 1)
    (hn8_l : (node sw_ne se_nw sw_se se_sw).level = k + 1)
    (hn9_l : (node se_nw se_ne se_sw se_se).level = k + 1)
    (hn5_w : (node nw_se ne_sw sw_ne se_nw).wf = true)
    (hn6_w : (node ne_sw ne_se se_nw se_ne).wf = true)
    (hn8_w : (node sw_ne se_nw sw_se se_sw).wf = true)
    (hn9_w : (node se_nw se_ne se_sw se_se).wf = true)
    (hR5_l : R5.level = k) (hR6_l : R6.level = k)
    (hR8_l : R8.level = k) (hR9_l : R9.level = k)
    (hR5_w : R5.wf = true) (hR6_w : R6.wf = true)
    (hR8_w : R8.wf = true) (hR9_w : R9.wf = true)
    (ih : ∀ (c' : MacroCell) (j : Nat), j < k → c'.wf = true → c'.level = j + 2 →
      centralCorrect c' j)
    (p : Int × Int)
    (hout_nw : MacroCell)
    (hout_nw_l : hout_nw.level = k)
    (hmem : p ∈ evolve (2^k)
        ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
          (0, 0)))
    (hp1 : (2^k : Int) + 2^k ≤ p.1) (hp2 : p.1 < (2^k : Int) + 2*2^k)
    (hp3 : (2^k : Int) + 2^k ≤ p.2) (hp4 : p.2 < (2^k : Int) + 2*2^k) :
    p ∈ (hashlifeResultAux (k + 1) (node R5 R6 R8 R9)).toGrid
        ((2^k : Int) + (2^hout_nw.level : Int),
         (2^k : Int) + (2^hout_nw.level : Int)) := by
  rw [show ((2^k : Int) + (2^hout_nw.level : Int)) = (2^k + (2^k : Int)) from by
    rw [congrArg (fun n => (2^n : Int)) hout_nw_l]]
  rw [show (k + 1) = (k - 1) + 2 from by omega]
  have he : (k - 1) + 1 = k := by omega
  have hw : ((2^k + (2^k : Int))) ≤ p.1 ∧
              p.1 < ((2^k + (2^k : Int))) + 2^((k - 1) + 1) ∧
            ((2^k + (2^k : Int))) ≤ p.2 ∧
              p.2 < ((2^k + (2^k : Int))) + 2^((k - 1) + 1) := by
    rw [he]
    exact ⟨hp1, by omega, hp3, by omega⟩
  refine (p4_se_shift_lemma k hk1 R5 R6 R8 R9
      hR5_l hR6_l hR8_l hR9_l hR5_w hR6_w hR8_w hR9_w ih p).mpr ⟨?_, hw⟩
  have hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1) :=
    ih _ (k - 1) (by omega) hn5_w (by rw [hn5_l]; omega)
  have hcc6 : centralCorrect (node ne_sw ne_se se_nw se_ne) (k - 1) :=
    ih _ (k - 1) (by omega) hn6_w (by rw [hn6_l]; omega)
  have hcc8 : centralCorrect (node sw_ne se_nw sw_se se_sw) (k - 1) :=
    ih _ (k - 1) (by omega) hn8_w (by rw [hn8_l]; omega)
  have hcc9 : centralCorrect (node se_nw se_ne se_sw se_se) (k - 1) :=
    ih _ (k - 1) (by omega) hn9_w (by rw [hn9_l]; omega)
  rw [← p4_se_supercell_agree k hk1
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
        R5 R6 R8 R9 hR5 hR6 hR8 hR9
        hR5_l hR6_l hR8_l hR9_l hcc5 hcc6 hcc8 hcc9 p]
  rw [← evolve_half_step k hk1]
  rw [isAlive_true_iff_mem_local]
  exact hmem

set_option maxHeartbeats 1000000 in
/-- **P4 entry point**: the pointwise membership biconditional for the
    inductive step. Glues `p4_double_nine_shape` (P4.1), `p4_wave1_ih`
    (P4.2), and `p4_wave2_ih` (P4.3). The P4.4 half-step composition is
    subsumed by the closed lemmas `evolve_add` (L2353) + `evolve_half_step`
    (L2370) and the wave-assembly residual carried in this proof body's own
    `sorry`. Once the residual closes, this function produces the
    `∀ p, p ∈ ... ↔ p ∈ ...` hypothesis that `p4_ext_bridge` consumes.

    **Pointwise-proof balisage (c.147)** — the residual `sorry` after `intro p`
    is the pointwise form of the P4.4 sub-cell coverage (S3) + assemble (S4)
    argument, decomposed here into three named pieces:
    - **G1 (geometric, tractable)** — RHS reduction: `p ∈ restrictGridTo
      (evolve 2^k g) 2^k 2^(k+1)` splits via `mem_restrictGridTo` into window
      bounds `[2^k, 3·2^k)²` (since `2^k + 2^(k+1) = 3·2^k`) plus the cell-state
      `isAlive (evolve 2^k g) p`. Pure arithmetic, no `hashlifeResultAux`.
    - **G2 (whnf-hard)** — LHS reduction: `p ∈ (hashlifeResultAux (k+2) c).toGrid
      (2^k, 2^k)` agrees, on the containing quadrant `q_j`, with `evolve 2^(k-1)`
      on `q_j.toGrid`, via the four `centralCorrect q_j (k-1)` from `_h3` (P4.3).
      Touches `hashlifeResultAux` results → the c.139/142/143 whnf wall.
    - **G3 (whnf-hard assemble)** — combine G1 and G2 with `step_light_cone`
      (locality, radius `2·2^k`) and `evolve_half_step` (the `2^k` half-step
      `evolve 2^k = evolve 2^(k-1) ∘ evolve 2^(k-1)`, now closed): the local
      sub-cell computation equals the global `evolve 2^k` on the centered window.

    Of these, `evolve_half_step` (the G3 half-step composition) is closed;
    G1/G2/G3 themselves remain `sorry` because they compose `hashlifeResultAux`
    results (the whnf-hard core, reserved for dedicated multi-cycle effort). -/
noncomputable def p4_succ_membership
    (c : MacroCell) (k : Nat) (hwf : c.wf = true) (hk : c.level = k + 2) (hk1 : 1 ≤ k)
    (ih : ∀ (c' : MacroCell) (j : Nat), j < k → c'.wf = true → c'.level = j + 2 →
      centralCorrect c' j) :
    ∀ p, p ∈ (hashlifeResultAux (k + 2) c).toGrid ((2^k : Nat), (2^k : Nat)) ↔
        p ∈ restrictGridTo (evolve (2^k) (c.toGrid (0, 0))) (2^k : Int) (2^(k+1)) := by
  have _h1 := p4_double_nine_shape c k hwf hk
  have _h2 := p4_wave1_ih c k hwf hk hk1 ih
  have _h3 := p4_wave2_ih c k hwf hk hk1 ih
  intro p
  -- LHS assembly (c.156). The 3 G3 gates (hcnode, hashlifeResultAux_succ_node,
  -- if_neg) now compose through the whnf wall, exposing the `node out_*`
  -- constructor and decomposing it via `mem_toGrid_node`.
  -- Destruct c via _h1 (p4_double_nine_shape: c = node(node×4)×4 ∧ 16 facts).
  obtain ⟨nw_nw, nw_ne, nw_sw, nw_se, ne_nw, ne_ne, ne_sw, ne_se,
          sw_nw, sw_ne, sw_sw, sw_se, se_nw, se_ne, se_sw, se_se, _hcshape⟩ := _h1
  obtain ⟨hcnode, hfacts⟩ := _hcshape
  -- Rewrite the input cell to its 16-grandchild node, then iota-reduce hRA.
  rw [hcnode]
  rw [show (k + 2) = (k + 1) + 1 from by omega]
  rw [hashlifeResultAux_succ_node]
  -- The if-condition (node16).level == 2 is FALSE for k >= 1 (level = k+2 >= 3).
  -- Discharge via the clean-context helper (opaque binders, c.139/c.143 pattern):
  -- applying it here keeps the level term inferred, never whnf-re-elaborated.
  have hne2 := node16_level_ne_two k hk1
    nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
    sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se hfacts.1
  rw [if_neg hne2]
  -- LHS is now `p ∈ (node out_nw out_ne out_sw out_se).toGrid (2^k, 2^k)`;
  -- `mem_toGrid_node` (G3) decomposes it into the four quadrant memberships.
  rw [mem_toGrid_node]
  -- RESIDUAL (the offset-matching assembly): each `out_*.toGrid (off_*, off_*)`
  -- must be characterized via `centralCorrect_mem` (G2 congruence, crossing the
  -- whnf wall on the composed result) + the induction hypothesis `centralCorrect
  -- q_* (k-1)` from `_h3`, then bridged to the RHS window via `evolve_half_step`
  -- (the `2^k` half-step) + `evolve_add` (G1). The offsets `2^out_*.level` vs
  -- `2^k` and the ih at level (k-1) vs goal at level k are the matching core.
  -- G3 wave-assembly: decomposed into 5 named sub-sorries (4 quadrants + mpr),
  -- per the ai-01 plan step 8. Each sub-sorry is independently attackable:
  -- the 4 mp cases apply centralCorrect_mem_shift (G2) on the corresponding
  -- q_j from _h3, then evolve_half_step (G3) + evolve_cone_agree (locality)
  -- to bridge to the global evolve 2^k window; mpr uses quad_partition_bounds
  -- to route p to the correct quadrant.
  refine ⟨?mp, ?mpr⟩
  case mp =>
    intro hlhs
    rcases hlhs with hnw | hne | hsw | hse
    · -- nw quadrant: p ∈ out_nw.toGrid (2^k, 2^k)
      -- goal: p ∈ restrictGridTo (evolve (2^k) (toGrid (0,0) <c destructuré en nodes>)) (2^k) (2^(k+1))
      -- Step 1: destructure the 32-conjunct grandchild facts into hg1..hg32.
      obtain ⟨hnw_nw_l, hnw_nw_w, hnw_ne_l, hnw_ne_w, hnw_sw_l, hnw_sw_w, hnw_se_l, hnw_se_w,
              hne_nw_l, hne_nw_w, hne_ne_l, hne_ne_w, hne_sw_l, hne_sw_w, hne_se_l, hne_se_w,
              hsw_nw_l, hsw_nw_w, hsw_ne_l, hsw_ne_w, hsw_sw_l, hsw_sw_w, hsw_se_l, hsw_se_w,
              hse_nw_l, hse_nw_w, hse_ne_l, hse_ne_w, hse_sw_l, hse_sw_w, hse_se_l, hse_se_w⟩ := hfacts
      -- Step 2: build 9 wave-1 result facts (level + cellWf) via node_wf_level_of_four + wave1_result_facts.
      -- n1 = node nw_nw nw_ne nw_sw nw_se
      have hn1 := node_wf_level_of_four hnw_nw_l hnw_ne_l hnw_sw_l hnw_se_l
                                        hnw_nw_w hnw_ne_w hnw_sw_w hnw_se_w
      have r1 := wave1_result_facts k hk1 (node nw_nw nw_ne nw_sw nw_se) hn1.2 hn1.1
      -- n2 = node nw_ne ne_nw nw_se ne_sw
      have hn2 := node_wf_level_of_four hnw_ne_l hne_nw_l hnw_se_l hne_sw_l
                                        hnw_ne_w hne_nw_w hnw_se_w hne_sw_w
      have r2 := wave1_result_facts k hk1 (node nw_ne ne_nw nw_se ne_sw) hn2.2 hn2.1
      -- n4 = node nw_sw nw_se sw_nw sw_ne
      have hn4 := node_wf_level_of_four hnw_sw_l hnw_se_l hsw_nw_l hsw_ne_l
                                        hnw_sw_w hnw_se_w hsw_nw_w hsw_ne_w
      have r4 := wave1_result_facts k hk1 (node nw_sw nw_se sw_nw sw_ne) hn4.2 hn4.1
      -- n5 = node nw_se ne_sw sw_ne se_nw
      have hn5 := node_wf_level_of_four hnw_se_l hne_sw_l hsw_ne_l hse_nw_l
                                        hnw_se_w hne_sw_w hsw_ne_w hse_nw_w
      have r5 := wave1_result_facts k hk1 (node nw_se ne_sw sw_ne se_nw) hn5.2 hn5.1
      -- With r1, r2, r4, r5 (the four wave-1 results), apply the opaque-binder
      -- nw arm lemma. `R_i := hashlifeResultAux (k+1) n_i` is pure substitution
      -- (no whnf): the whnf-hard shift consumption happens inside the arm over
      -- opaque binders (fresh heartbeat budget). Normalize hnw's Nat-cast offset
      -- `↑(2^k)` to `(2^k : Int)` so it unifies with the arm's hypothesis.
      push_cast at hnw
      exact p4_nw_membership_arm k hk1
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
        (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
        (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
        (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
        (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
        rfl rfl rfl rfl
        hn1.1 hn2.1 hn4.1 hn5.1
        hn1.2 hn2.2 hn4.2 hn5.2
        r1.1 r2.1 r4.1 r5.1
        (wf_of_cellWf r1.2) (wf_of_cellWf r2.2) (wf_of_cellWf r4.2) (wf_of_cellWf r5.2)
        ih p hnw

    · -- ne quadrant: p ∈ out_ne.toGrid (2^k, 2^k + 2^level)
      -- Factorization (c.8122 — defensive extraction): the residual sorry is the
      -- mirror of the NW wall (off-by-shift `{2,3,5,6}` vs `{1,2,4,5}`). Build
      -- the 4 NE wave-1 sub-cells n2/n3/n5/n6 + wave-0 results R2/R3/R5/R6, then
      -- apply the opaque-binder `p4_ne_membership_arm`. The whnf-hard step is
      -- encapsulated in the arm over opaque `R_j` (fresh heartbeat budget).
      obtain ⟨hnw_nw_l, hnw_nw_w, hnw_ne_l, hnw_ne_w, hnw_sw_l, hnw_sw_w, hnw_se_l, hnw_se_w,
              hne_nw_l, hne_nw_w, hne_ne_l, hne_ne_w, hne_sw_l, hne_sw_w, hne_se_l, hne_se_w,
              hsw_nw_l, hsw_nw_w, hsw_ne_l, hsw_ne_w, hsw_sw_l, hsw_sw_w, hsw_se_l, hsw_se_w,
              hse_nw_l, hse_nw_w, hse_ne_l, hse_ne_w, hse_sw_l, hse_sw_w, hse_se_l, hse_se_w⟩ := hfacts
      -- n1 = node nw_nw nw_ne nw_sw nw_se (the OUTER NW supercell, used for
      -- the NE offset `2^out_nw.level` per `mem_toGrid_node`).
      have hn1 := node_wf_level_of_four hnw_nw_l hnw_ne_l hnw_sw_l hnw_se_l
                                        hnw_nw_w hnw_ne_w hnw_sw_w hnw_se_w
      have r1 := wave1_result_facts k hk1 (node nw_nw nw_ne nw_sw nw_se) hn1.2 hn1.1
      -- n2 = node nw_ne ne_nw nw_se ne_sw
      have hn2 := node_wf_level_of_four hnw_ne_l hne_nw_l hnw_se_l hne_sw_l
                                        hnw_ne_w hne_nw_w hnw_se_w hne_sw_w
      have r2 := wave1_result_facts k hk1 (node nw_ne ne_nw nw_se ne_sw) hn2.2 hn2.1
      -- n3 = node ne_nw ne_ne ne_sw ne_se
      have hn3 := node_wf_level_of_four hne_nw_l hne_ne_l hne_sw_l hne_se_l
                                        hne_nw_w hne_ne_w hne_sw_w hne_se_w
      have r3 := wave1_result_facts k hk1 (node ne_nw ne_ne ne_sw ne_se) hn3.2 hn3.1
      -- n5 = node nw_se ne_sw sw_ne se_nw
      have hn5 := node_wf_level_of_four hnw_se_l hne_sw_l hsw_ne_l hse_nw_l
                                        hnw_se_w hne_sw_w hsw_ne_w hse_nw_w
      have r5 := wave1_result_facts k hk1 (node nw_se ne_sw sw_ne se_nw) hn5.2 hn5.1
      -- n6 = node ne_sw ne_se se_nw se_ne
      have hn6 := node_wf_level_of_four hne_sw_l hne_se_l hse_nw_l hse_ne_l
                                        hne_sw_w hne_se_w hse_nw_w hse_ne_w
      have r6 := wave1_result_facts k hk1 (node ne_sw ne_se se_nw se_ne) hn6.2 hn6.1
      -- n4_ne = node nw_sw nw_se sw_nw sw_ne (SW-of-NW quadrant cell, the THIRD
      -- wave-1 child of `out_nw`). Needed in scope for `hinner` since `out_nw`
      -- itself holds the opaquely-binder hashlifeResultAux of (R1.node R2 R4 R5).
      have hn_nw_sw := node_wf_level_of_four hnw_sw_l hnw_se_l hsw_nw_l hsw_ne_l
                                              hnw_sw_w hnw_se_w hsw_nw_w hsw_ne_w
      have r_nw_sw := wave1_result_facts k hk1 (node nw_sw nw_se sw_nw sw_ne)
                                          hn_nw_sw.2 hn_nw_sw.1
      -- n7 = node sw_nw sw_ne sw_sw sw_se (the OUTER SW child of the parent —
      -- structural-only hypothesis for the NE wall's bound exclusions, no hcc).
      have hn7 := node_wf_level_of_four hsw_nw_l hsw_ne_l hsw_sw_l hsw_se_l
                                        hsw_nw_w hsw_ne_w hsw_sw_w hsw_se_w
      -- Normalize hne's Nat-cast offset `↑(2^k + 2^(k-1))` to the Int form so
      -- it unifies with the arm's hypothesis. Then construct the OUTER NW
      -- supercell `out_nw = R1.node R2 (R_nw_sw) R5` (the level-(k+1) input cell
      -- of `hashlifeResultAux (k+1)` that produces the outer NW quadrant), pass
      -- `out_nw : MacroCell` + `hout_nw_l : out_nw.level = k` so the arm can
      -- bridge `2^out_nw.level = 2^k` via `congrArg` (c.8122).
      --
      -- AVOID `push_cast at hne` (whnf-timeout 200k heartbeats, c.8122 trial-v2):
      -- rewriting through `out_ne.toGrid` (which forces whnf of
      -- `hashlifeResultAux (k+1) (node R2 R3 R5 R6).toGrid`) over a 2^k offset
      -- exceeds the budget. Instead, target the arm's exact form via
      -- `change`-then-`congrArg`: prove the literal Nat→Int equalities and let
      -- Lean's unifier consume them when matching `p4_ne_membership_arm`.
      --
      -- The arm's `hout_nw` is consumed solely via `hout_nw_l : hout_nw.level = k`
      -- (then `congrArg (fun n => (2^n : Int)) hout_nw_l`). We therefore only
      -- need to be ABLE to assert the level fact; the syntactic term is opaque
      -- to the arm. The bridging lemmas built below prove the equalities the
      -- arm's `congrArg` step needs (`2^hout_nw.level = 2^k` mod the offset).
      let out_nw : MacroCell :=
        hashlifeResultAux (k + 1)
          (node (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
                (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
                (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
                (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw)))
      -- hout_nw_l : out_nw.level = k. Proven via the inner-node level-fact: the
      -- 4-arg `node` (level k+1, wf true) maps under `wave1_result_facts` to a
      -- level-k hashlifeResultAux.
      have hout_nw_l : out_nw.level = k :=
        (wave1_result_facts k hk1
          (node (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
                (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
                (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
                (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw)))
          (node_wf_level_of_four r1.1 r2.1 r_nw_sw.1 r5.1
            (wf_of_cellWf r1.2) (wf_of_cellWf r2.2)
            (wf_of_cellWf r_nw_sw.2) (wf_of_cellWf r5.2)).right
          (node_wf_level_of_four r1.1 r2.1 r_nw_sw.1 r5.1
            (wf_of_cellWf r1.2) (wf_of_cellWf r2.2)
            (wf_of_cellWf r_nw_sw.2) (wf_of_cellWf r5.2)).left).1
      -- Targeted Nat→Int coercion on `hne`'s offsets. The arm expects `Int`-typed
      -- offsets; `mem_toGrid_node` already coerced `2^out_nw.level : Int`, so only
      -- the leading `2^k` literals need rewriting. `norm_cast` is more targeted
      -- than `push_cast` (top-level only, no deep whnf).
      norm_cast at hne
      exact p4_ne_membership_arm k hk1
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
        (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))   -- R1
        (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
        (hashlifeResultAux (k + 1) (node ne_nw ne_ne ne_sw ne_se))
        (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
        (hashlifeResultAux (k + 1) (node ne_sw ne_se se_nw se_ne))
        rfl rfl rfl rfl rfl
        hn1.1 hn2.1 hn3.1 hn_nw_sw.1 hn5.1 hn6.1 hn7.1
        hn1.2 hn2.2 hn3.2 hn_nw_sw.2 hn5.2 hn6.2 hn7.2
        r1.1 r2.1 r3.1 r5.1 r6.1
        (wf_of_cellWf r1.2) (wf_of_cellWf r2.2) (wf_of_cellWf r3.2)
        (wf_of_cellWf r5.2) (wf_of_cellWf r6.2)
        ih
        p
        out_nw
        hout_nw_l
        hne
    · -- sw quadrant: p ∈ out_sw.toGrid (2^k + 2^level, 2^k)
      -- Factorization (c.NNNN — defensive extraction): the SW arm is the
      -- NW-SE reflection of the NE arm (c.8122) — same opaque-binder pattern.
      -- Sub-cells are n4/n5/n7/n8 (the SW wave-1 children of the outer
      -- 16-grandkid layout per `p4_double_nine_shape` L2109 + `p4_wave2_ih`
      -- L2629-2633). Build the 4 SW wave-1 sub-cells + wave-0 results
      -- R4/R5/R7/R8, then apply the opaque-binder `p4_sw_membership_arm`.
      -- The whnf-hard step is encapsulated in the arm over opaque `R_j`
      -- (fresh heartbeat budget, set_option at the arm).
      --
      -- IMPORTANT (c.8122 cascade-fix L831): all `hcc_j` and `R_j` literals
      -- must be sourced from `p4_wave2_ih`'s canonical reference (L2629-2633),
      -- NOT copy-pasted across branches. The 16-grid positions for SW sub-cells
      -- are {4,5,7,8} (NE was {2,3,5,6}; symmetric flip of row-axis):
      --   n4 = node nw_sw nw_se sw_nw sw_ne
      --   n5 = node nw_se ne_sw sw_ne se_nw
      --   n7 = node sw_nw sw_ne sw_sw sw_se
      --   n8 = node sw_ne se_nw sw_se se_sw
      obtain ⟨hnw_nw_l, hnw_nw_w, hnw_ne_l, hnw_ne_w, hnw_sw_l, hnw_sw_w, hnw_se_l, hnw_se_w,
              hne_nw_l, hne_nw_w, hne_ne_l, hne_ne_w, hne_sw_l, hne_sw_w, hne_se_l, hne_se_w,
              hsw_nw_l, hsw_nw_w, hsw_ne_l, hsw_ne_w, hsw_sw_l, hsw_sw_w, hsw_se_l, hsw_se_w,
              hse_nw_l, hse_nw_w, hse_ne_l, hse_ne_w, hse_sw_l, hse_sw_w, hse_se_l, hse_se_w⟩ := hfacts
      -- n1 = node nw_nw nw_ne nw_sw nw_se (the OUTER NW supercell, used for
      -- the SW row offset `2^k + 2^out_nw.level` per `mem_toGrid_node`).
      have hn1 := node_wf_level_of_four hnw_nw_l hnw_ne_l hnw_sw_l hnw_se_l
                                        hnw_nw_w hnw_ne_w hnw_sw_w hnw_se_w
      have r1 := wave1_result_facts k hk1 (node nw_nw nw_ne nw_sw nw_se) hn1.2 hn1.1
      -- n2 = node nw_ne ne_nw nw_se ne_sw (NE-of-NW quadrant cell, the SECOND
      -- wave-1 child of `out_nw`). Needed in scope for `out_nw` construction.
      have hn2 := node_wf_level_of_four hnw_ne_l hne_nw_l hnw_se_l hne_sw_l
                                        hnw_ne_w hne_nw_w hnw_se_w hne_sw_w
      have r2 := wave1_result_facts k hk1 (node nw_ne ne_nw nw_se ne_sw) hn2.2 hn2.1
      -- n4 = node nw_sw nw_se sw_nw sw_ne (SW-of-NW, the THIRD wave-1 child of `out_nw`)
      have hn4 := node_wf_level_of_four hnw_sw_l hnw_se_l hsw_nw_l hsw_ne_l
                                        hnw_sw_w hnw_se_w hsw_nw_w hsw_ne_w
      have r4 := wave1_result_facts k hk1 (node nw_sw nw_se sw_nw sw_ne) hn4.2 hn4.1
      -- n5 = node nw_se ne_sw sw_ne se_nw (center bridge)
      have hn5 := node_wf_level_of_four hnw_se_l hne_sw_l hsw_ne_l hse_nw_l
                                        hnw_se_w hne_sw_w hsw_ne_w hse_nw_w
      have r5 := wave1_result_facts k hk1 (node nw_se ne_sw sw_ne se_nw) hn5.2 hn5.1
      -- n7 = node sw_nw sw_ne sw_sw sw_se (SW quadrant cell)
      have hn7 := node_wf_level_of_four hsw_nw_l hsw_ne_l hsw_sw_l hsw_se_l
                                        hsw_nw_w hsw_ne_w hsw_sw_w hsw_se_w
      have r7 := wave1_result_facts k hk1 (node sw_nw sw_ne sw_sw sw_se) hn7.2 hn7.1
      -- n8 = node sw_ne se_nw sw_se se_sw (SW-of-SE bridge)
      have hn8 := node_wf_level_of_four hsw_ne_l hse_nw_l hsw_se_l hse_sw_l
                                        hsw_ne_w hse_nw_w hsw_se_w hse_sw_w
      have r8 := wave1_result_facts k hk1 (node sw_ne se_nw sw_se se_sw) hn8.2 hn8.1
      -- Construct the OUTER NW supercell `out_nw = R1.node R2 (R4) R5`
      -- (level-(k+1) input cell of `hashlifeResultAux (k+1)` that produces the
      -- outer NW quadrant). The SW arm consumes `hout_nw_l : out_nw.level = k`
      -- via `congrArg (fun n => (2^n : Int)) hout_nw_l` (cf. c.8122 NE-arm wiring,
      -- the SW branch uses the same level-anchor as the NE branch — the SW
      -- row offset is `2^k + 2^out_nw.level`, the same `2^out_nw.level` as NE's
      -- column offset, so we re-construct `out_nw` here; this is a syntactic
      -- let, not a new computation, and Lean 4's whnf-friendly transparency
      -- keeps the lemma proof closed).
      let out_nw : MacroCell :=
        hashlifeResultAux (k + 1)
          (node (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
                (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
                (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
                (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw)))
      have hout_nw_l : out_nw.level = k :=
        (wave1_result_facts k hk1
          (node (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
                (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
                (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
                (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw)))
          (node_wf_level_of_four r1.1 r2.1 r4.1 r5.1
            (wf_of_cellWf r1.2) (wf_of_cellWf r2.2)
            (wf_of_cellWf r4.2) (wf_of_cellWf r5.2)).right
          (node_wf_level_of_four r1.1 r2.1 r4.1 r5.1
            (wf_of_cellWf r1.2) (wf_of_cellWf r2.2)
            (wf_of_cellWf r4.2) (wf_of_cellWf r5.2)).left).1
      -- Targeted Nat→Int coercion on `hsw`'s offsets (top-level only, same
      -- pattern as c.8122 NE branch — `norm_cast at hsw` not `push_cast`).
      norm_cast at hsw
      exact p4_sw_membership_arm k hk1
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
        (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
        (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
        (hashlifeResultAux (k + 1) (node sw_nw sw_ne sw_sw sw_se))
        (hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
        rfl rfl rfl rfl
        hn4.1 hn5.1 hn7.1 hn8.1
        hn4.2 hn5.2 hn7.2 hn8.2
        r4.1 r5.1 r7.1 r8.1
        (wf_of_cellWf r4.2) (wf_of_cellWf r5.2) (wf_of_cellWf r7.2) (wf_of_cellWf r8.2)
        ih
        p
        out_nw
        hout_nw_l
        hsw
    · -- se quadrant: p ∈ out_se.toGrid (2^k + 2^level, 2^k + 2^level)
      -- Factorization (c.90 — SE-arm port): the SE arm is the DIAGONAL mirror
      -- of the NW arm — same opaque-binder pattern as NE (c.8122) / SW (c.8123).
      -- Sub-cells are n5/n6/n8/n9 (the SE wave-1 children of the outer
      -- 16-grandkid layout per `p4_double_nine_shape` L2109 + `p4_wave2_ih`
      -- L2629-2633). Build the 4 SE wave-1 sub-cells + wave-0 results
      -- R5/R6/R8/R9, then apply the opaque-binder `p4_se_membership_arm`.
      --
      -- IMPORTANT (c.8122 cascade-fix L831): all `hcc_j` and `R_j` literals
      -- must be sourced from `p4_wave2_ih`'s canonical reference (L2629-2633),
      -- NOT copy-pasted across branches. The 16-grid positions for SE sub-cells
      -- are {5,6,8,9} (diagonal complement of NW's {1,2,4,5}):
      --   n5 = node nw_se ne_sw sw_ne se_nw
      --   n6 = node ne_sw ne_se se_nw se_ne
      --   n8 = node sw_ne se_nw sw_se se_sw
      --   n9 = node se_nw se_ne se_sw se_se
      obtain ⟨hnw_nw_l, hnw_nw_w, hnw_ne_l, hnw_ne_w, hnw_sw_l, hnw_sw_w, hnw_se_l, hnw_se_w,
              hne_nw_l, hne_nw_w, hne_ne_l, hne_ne_w, hne_sw_l, hne_sw_w, hne_se_l, hne_se_w,
              hsw_nw_l, hsw_nw_w, hsw_ne_l, hsw_ne_w, hsw_sw_l, hsw_sw_w, hsw_se_l, hsw_se_w,
              hse_nw_l, hse_nw_w, hse_ne_l, hse_ne_w, hse_sw_l, hse_sw_w, hse_se_l, hse_se_w⟩ := hfacts
      -- n1 = node nw_nw nw_ne nw_sw nw_se (the OUTER NW supercell — BOTH SE
      -- offsets are `2^k + 2^out_nw.level` per `mem_toGrid_node`, anchored on
      -- the first child's level like the NE column / SW row offsets).
      have hn1 := node_wf_level_of_four hnw_nw_l hnw_ne_l hnw_sw_l hnw_se_l
                                        hnw_nw_w hnw_ne_w hnw_sw_w hnw_se_w
      have r1 := wave1_result_facts k hk1 (node nw_nw nw_ne nw_sw nw_se) hn1.2 hn1.1
      -- n2 = node nw_ne ne_nw nw_se ne_sw (NE-of-NW, second wave-1 child of `out_nw`)
      have hn2 := node_wf_level_of_four hnw_ne_l hne_nw_l hnw_se_l hne_sw_l
                                        hnw_ne_w hne_nw_w hnw_se_w hne_sw_w
      have r2 := wave1_result_facts k hk1 (node nw_ne ne_nw nw_se ne_sw) hn2.2 hn2.1
      -- n4 = node nw_sw nw_se sw_nw sw_ne (SW-of-NW, third wave-1 child of `out_nw`)
      have hn4 := node_wf_level_of_four hnw_sw_l hnw_se_l hsw_nw_l hsw_ne_l
                                        hnw_sw_w hnw_se_w hsw_nw_w hsw_ne_w
      have r4 := wave1_result_facts k hk1 (node nw_sw nw_se sw_nw sw_ne) hn4.2 hn4.1
      -- n5 = node nw_se ne_sw sw_ne se_nw (center bridge — FIRST SE sub-cell)
      have hn5 := node_wf_level_of_four hnw_se_l hne_sw_l hsw_ne_l hse_nw_l
                                        hnw_se_w hne_sw_w hsw_ne_w hse_nw_w
      have r5 := wave1_result_facts k hk1 (node nw_se ne_sw sw_ne se_nw) hn5.2 hn5.1
      -- n6 = node ne_sw ne_se se_nw se_ne (E bridge — NE-of-SE)
      have hn6 := node_wf_level_of_four hne_sw_l hne_se_l hse_nw_l hse_ne_l
                                        hne_sw_w hne_se_w hse_nw_w hse_ne_w
      have r6 := wave1_result_facts k hk1 (node ne_sw ne_se se_nw se_ne) hn6.2 hn6.1
      -- n8 = node sw_ne se_nw sw_se se_sw (S bridge — SW-of-SE)
      have hn8 := node_wf_level_of_four hsw_ne_l hse_nw_l hsw_se_l hse_sw_l
                                        hsw_ne_w hse_nw_w hsw_se_w hse_sw_w
      have r8 := wave1_result_facts k hk1 (node sw_ne se_nw sw_se se_sw) hn8.2 hn8.1
      -- n9 = node se_nw se_ne se_sw se_se (SE quadrant cell)
      have hn9 := node_wf_level_of_four hse_nw_l hse_ne_l hse_sw_l hse_se_l
                                        hse_nw_w hse_ne_w hse_sw_w hse_se_w
      have r9 := wave1_result_facts k hk1 (node se_nw se_ne se_sw se_se) hn9.2 hn9.1
      -- Construct the OUTER NW supercell `out_nw` (same level-anchor as the
      -- NE/SW branches — `mem_toGrid_node` shifts BOTH SE coordinates by
      -- `2^out_nw.level`; syntactic let, no new computation).
      let out_nw : MacroCell :=
        hashlifeResultAux (k + 1)
          (node (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
                (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
                (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
                (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw)))
      have hout_nw_l : out_nw.level = k :=
        (wave1_result_facts k hk1
          (node (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
                (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
                (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
                (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw)))
          (node_wf_level_of_four r1.1 r2.1 r4.1 r5.1
            (wf_of_cellWf r1.2) (wf_of_cellWf r2.2)
            (wf_of_cellWf r4.2) (wf_of_cellWf r5.2)).right
          (node_wf_level_of_four r1.1 r2.1 r4.1 r5.1
            (wf_of_cellWf r1.2) (wf_of_cellWf r2.2)
            (wf_of_cellWf r4.2) (wf_of_cellWf r5.2)).left).1
      -- Targeted Nat→Int coercion on `hse`'s offsets (top-level only, same
      -- pattern as the NE/SW branches — `norm_cast at hse` not `push_cast`).
      norm_cast at hse
      exact p4_se_membership_arm k hk1
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
        (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
        (hashlifeResultAux (k + 1) (node ne_sw ne_se se_nw se_ne))
        (hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
        (hashlifeResultAux (k + 1) (node se_nw se_ne se_sw se_se))
        rfl rfl rfl rfl
        hn5.1 hn6.1 hn8.1 hn9.1
        hn5.2 hn6.2 hn8.2 hn9.2
        r5.1 r6.1 r8.1 r9.1
        (wf_of_cellWf r5.2) (wf_of_cellWf r6.2) (wf_of_cellWf r8.2) (wf_of_cellWf r9.2)
        ih
        p
        out_nw
        hout_nw_l
        hse
  case mpr =>
    intro hrhs
    -- RHS → global membership + the four window bounds; `quad_partition_bounds`
    -- routes p to its quadrant; each reciprocal arm (shift `.mpr` ∘
    -- supercell-agree consumed R-to-L ∘ half-step fold) then delivers the
    -- corresponding `mem_toGrid_node` disjunct.
    rw [mem_restrictGridTo] at hrhs
    obtain ⟨hmem, hb1, hb2, hb3, hb4⟩ := hrhs
    have hbridge : ((2 ^ (k + 1) : Nat) : Int) = 2 ^ k + 2 ^ k := by
      push_cast; rw [pow_succ]; ring
    rw [hbridge] at hb2 hb4
    have hpos : (0 : Int) ≤ 2 ^ k := le_of_lt (pow_pos (by norm_num) k)
    have hroute := (quad_partition_bounds (2^k : Int) (2^k : Int) hpos p).mp
      ⟨hb1, by omega, hb3, by omega⟩
    -- Shared towers, built ONCE for the four branches (the mp branches each
    -- rebuilt their own subset; here the router owns them): the 32 grandchild
    -- facts, the 9 wave-1 results r1..r9 (canonical reference `p4_wave2_ih`
    -- L2629-2633), and the outer-NW supercell level anchor.
    obtain ⟨hnw_nw_l, hnw_nw_w, hnw_ne_l, hnw_ne_w, hnw_sw_l, hnw_sw_w, hnw_se_l, hnw_se_w,
            hne_nw_l, hne_nw_w, hne_ne_l, hne_ne_w, hne_sw_l, hne_sw_w, hne_se_l, hne_se_w,
            hsw_nw_l, hsw_nw_w, hsw_ne_l, hsw_ne_w, hsw_sw_l, hsw_sw_w, hsw_se_l, hsw_se_w,
            hse_nw_l, hse_nw_w, hse_ne_l, hse_ne_w, hse_sw_l, hse_sw_w, hse_se_l, hse_se_w⟩ := hfacts
    -- n1 = node nw_nw nw_ne nw_sw nw_se
    have hn1 := node_wf_level_of_four hnw_nw_l hnw_ne_l hnw_sw_l hnw_se_l
                                      hnw_nw_w hnw_ne_w hnw_sw_w hnw_se_w
    have r1 := wave1_result_facts k hk1 (node nw_nw nw_ne nw_sw nw_se) hn1.2 hn1.1
    -- n2 = node nw_ne ne_nw nw_se ne_sw
    have hn2 := node_wf_level_of_four hnw_ne_l hne_nw_l hnw_se_l hne_sw_l
                                      hnw_ne_w hne_nw_w hnw_se_w hne_sw_w
    have r2 := wave1_result_facts k hk1 (node nw_ne ne_nw nw_se ne_sw) hn2.2 hn2.1
    -- n3 = node ne_nw ne_ne ne_sw ne_se
    have hn3 := node_wf_level_of_four hne_nw_l hne_ne_l hne_sw_l hne_se_l
                                      hne_nw_w hne_ne_w hne_sw_w hne_se_w
    have r3 := wave1_result_facts k hk1 (node ne_nw ne_ne ne_sw ne_se) hn3.2 hn3.1
    -- n4 = node nw_sw nw_se sw_nw sw_ne
    have hn4 := node_wf_level_of_four hnw_sw_l hnw_se_l hsw_nw_l hsw_ne_l
                                      hnw_sw_w hnw_se_w hsw_nw_w hsw_ne_w
    have r4 := wave1_result_facts k hk1 (node nw_sw nw_se sw_nw sw_ne) hn4.2 hn4.1
    -- n5 = node nw_se ne_sw sw_ne se_nw (center bridge)
    have hn5 := node_wf_level_of_four hnw_se_l hne_sw_l hsw_ne_l hse_nw_l
                                      hnw_se_w hne_sw_w hsw_ne_w hse_nw_w
    have r5 := wave1_result_facts k hk1 (node nw_se ne_sw sw_ne se_nw) hn5.2 hn5.1
    -- n6 = node ne_sw ne_se se_nw se_ne
    have hn6 := node_wf_level_of_four hne_sw_l hne_se_l hse_nw_l hse_ne_l
                                      hne_sw_w hne_se_w hse_nw_w hse_ne_w
    have r6 := wave1_result_facts k hk1 (node ne_sw ne_se se_nw se_ne) hn6.2 hn6.1
    -- n7 = node sw_nw sw_ne sw_sw sw_se
    have hn7 := node_wf_level_of_four hsw_nw_l hsw_ne_l hsw_sw_l hsw_se_l
                                      hsw_nw_w hsw_ne_w hsw_sw_w hsw_se_w
    have r7 := wave1_result_facts k hk1 (node sw_nw sw_ne sw_sw sw_se) hn7.2 hn7.1
    -- n8 = node sw_ne se_nw sw_se se_sw
    have hn8 := node_wf_level_of_four hsw_ne_l hse_nw_l hsw_se_l hse_sw_l
                                      hsw_ne_w hse_nw_w hsw_se_w hse_sw_w
    have r8 := wave1_result_facts k hk1 (node sw_ne se_nw sw_se se_sw) hn8.2 hn8.1
    -- n9 = node se_nw se_ne se_sw se_se
    have hn9 := node_wf_level_of_four hse_nw_l hse_ne_l hse_sw_l hse_se_l
                                      hse_nw_w hse_ne_w hse_sw_w hse_se_w
    have r9 := wave1_result_facts k hk1 (node se_nw se_ne se_sw se_se) hn9.2 hn9.1
    -- Outer-NW supercell (same syntactic let as the mp NE/SW/SE branches):
    -- the NE/SW/SE disjunct anchors carry `2^out_nw.level`, bridged in the
    -- rev arms via `congrArg` on `hout_nw_l`.
    let out_nw : MacroCell :=
      hashlifeResultAux (k + 1)
        (node (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
              (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
              (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
              (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw)))
    have hout_nw_l : out_nw.level = k :=
      (wave1_result_facts k hk1
        (node (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
              (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
              (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
              (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw)))
        (node_wf_level_of_four r1.1 r2.1 r4.1 r5.1
          (wf_of_cellWf r1.2) (wf_of_cellWf r2.2)
          (wf_of_cellWf r4.2) (wf_of_cellWf r5.2)).right
        (node_wf_level_of_four r1.1 r2.1 r4.1 r5.1
          (wf_of_cellWf r1.2) (wf_of_cellWf r2.2)
          (wf_of_cellWf r4.2) (wf_of_cellWf r5.2)).left).1
    rcases hroute with hq | hq | hq | hq
    · -- NW quadrant (router disjunct 1 = mem_toGrid_node disjunct 1)
      left
      norm_cast
      exact p4_nw_membership_arm_rev k hk1
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
        (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
        (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
        (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
        (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
        rfl rfl rfl rfl
        hn1.1 hn2.1 hn4.1 hn5.1
        hn1.2 hn2.2 hn4.2 hn5.2
        r1.1 r2.1 r4.1 r5.1
        (wf_of_cellWf r1.2) (wf_of_cellWf r2.2) (wf_of_cellWf r4.2) (wf_of_cellWf r5.2)
        ih p hmem hq.1 hq.2.1 hq.2.2.1 hq.2.2.2
    · -- NE quadrant
      right; left
      norm_cast
      exact p4_ne_membership_arm_rev k hk1
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
        (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
        (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
        (hashlifeResultAux (k + 1) (node ne_nw ne_ne ne_sw ne_se))
        (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
        (hashlifeResultAux (k + 1) (node ne_sw ne_se se_nw se_ne))
        rfl rfl rfl rfl rfl
        hn1.1 hn2.1 hn3.1 hn4.1 hn5.1 hn6.1 hn7.1
        hn1.2 hn2.2 hn3.2 hn4.2 hn5.2 hn6.2 hn7.2
        r1.1 r2.1 r3.1 r5.1 r6.1
        (wf_of_cellWf r1.2) (wf_of_cellWf r2.2) (wf_of_cellWf r3.2)
        (wf_of_cellWf r5.2) (wf_of_cellWf r6.2)
        ih p out_nw hout_nw_l hmem hq.1 hq.2.1 hq.2.2.1 hq.2.2.2
    · -- SW quadrant
      right; right; left
      norm_cast
      exact p4_sw_membership_arm_rev k hk1
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
        (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
        (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
        (hashlifeResultAux (k + 1) (node sw_nw sw_ne sw_sw sw_se))
        (hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
        rfl rfl rfl rfl
        hn4.1 hn5.1 hn7.1 hn8.1
        hn4.2 hn5.2 hn7.2 hn8.2
        r4.1 r5.1 r7.1 r8.1
        (wf_of_cellWf r4.2) (wf_of_cellWf r5.2) (wf_of_cellWf r7.2) (wf_of_cellWf r8.2)
        ih p out_nw hout_nw_l hmem hq.1 hq.2.1 hq.2.2.1 hq.2.2.2
    · -- SE quadrant
      right; right; right
      norm_cast
      exact p4_se_membership_arm_rev k hk1
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
        (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
        (hashlifeResultAux (k + 1) (node ne_sw ne_se se_nw se_ne))
        (hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
        (hashlifeResultAux (k + 1) (node se_nw se_ne se_sw se_se))
        rfl rfl rfl rfl
        hn5.1 hn6.1 hn8.1 hn9.1
        hn5.2 hn6.2 hn8.2 hn9.2
        r5.1 r6.1 r8.1 r9.1
        (wf_of_cellWf r5.2) (wf_of_cellWf r6.2) (wf_of_cellWf r8.2) (wf_of_cellWf r9.2)
        ih p out_nw hout_nw_l hmem hq.1 hq.2.1 hq.2.2.1 hq.2.2.2

/-- For a level-`k` MacroCell `c` with `k ≥ 2`, the centered region of
    `hashlifeResultAux (k+2) c` (viewed at offset `(2^k, 2^k)`) equals
    `evolve (2^k)` applied to `c.toGrid (0, 0)` and restricted to the
    centered `[2^k, 2^k + 2^(k+1)) × [2^k, 2^k + 2^(k+1))` region.

    **Statement correction**: offset `(2^k, 2^k)` accounts for centering.

    **Proof strategy** (P4, difficulty: hard, compositional):
    Strong induction on `k`.
    - Base `k = 0`: `hashlifeResultAux 2 c` reduces to `step4x4 c`, which
      is the direct B3/S23 computation on a 4x4 grid. The centered 2x2
      result at offset `(1, 1)` matches `evolve 1` restricted to `[1,3)×[1,3)`.
    - Inductive step `k → k+1`: the recursive Hashlife makes 9 sub-calls on
      level-`(k+1)` cells, then 4 sub-calls on the resulting level-`k`
      supercells. Each sub-call uses the IH at level `k`. The composition
      matches `step^[2^(k+1)]` by the light-cone lemma P2 applied 2^(k-1)
      times (once per "half-step" in the double-nine decomposition). -/
theorem hashlifeResult_central_correct (c : MacroCell) (k : Nat)
    (hwf : c.wf = true) (hk : c.level = k + 2) :
    let result := hashlifeResultAux (k + 2) c
    let resultGrid := result.toGrid ((2^k : Nat), (2^k : Nat))
    let expected := evolve (2^k) (c.toGrid (0, 0))
    resultGrid = restrictGridTo expected (2^k : Int) (2^(k+1)) := by
  -- P4 TARGET: central Hashlife correctness, by STRONG induction on the level
  -- index `k`. The motive quantifies over `c` (reverted before induction) so
  -- the induction hypothesis `ih` ranges over every MacroCell at a smaller
  -- level (not just a fixed `c`): this is required because the recursive step
  -- applies the IH to the double-nine *sub-cells* `n_i` of `c`, which are
  -- MacroCells distinct from `c` itself. A plain `cases k` exposes no such
  -- cross-cell IH, which (c.137) forced `p4_wave1_ih` to stay a vacuous `True`
  -- placeholder to avoid a forbidden mutual-recursion cycle. Threading `ih`
  -- down through `p4_succ_membership` -> `p4_wave1_ih` breaks that cycle (c.138),
  -- and the c.139 helper `p4_wave1_ih_step` makes the `ih` application compile.
  revert c hwf hk
  induction k using Nat.strongRecOn with
  | ind n ih =>
    intro c hwf hk
    cases n with
    | zero => exact hashlifeResult_central_correct_base c hwf hk
    | succ k =>
      have hk1 : 1 ≤ k + 1 := by omega
      exact p4_ext_bridge c (k + 1)
        (p4_succ_membership c (k + 1) hwf hk hk1
          (fun c' j hj hc'w hc'l => ih j hj c' hc'w hc'l))

end Life
end Conway
