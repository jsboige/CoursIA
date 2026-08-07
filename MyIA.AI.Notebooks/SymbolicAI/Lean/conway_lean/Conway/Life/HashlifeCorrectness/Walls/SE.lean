/-  # HashlifeCorrectness.Walls.SE

P4 SE quadrant: shift lemma + overlap wall + G3 bridge + supercell agreement +
membership arm (.mp) and its reciprocal (.mpr). Diagonal mirror of NW.
-/

import Conway.Life.HashlifeCorrectness.Foundation

namespace Conway
namespace Life

open MacroCell

/-- **P4.4 SE-quadrant shift lemma (factorisé, c.552 — rebase de #6944 sur main post-#6955).**
    Symétrique au `p4_ne_shift_lemma` pour l'offset SE OUTER `(2^k + 2^k, 2^k + 2^k) = (2^(k+1), 2^(k+1))`.
    Convention uniforme avec NE/NW (c.8122) : voir `p4_sw_shift_lemma` pour le
    contexte. Sorry-free. -/
private theorem p4_se_shift_lemma
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
          ((2^k + (2^k : Int), 2^k + (2^k : Int))) ↔
      isAlive (evolve (2^(k - 1)) ((node r1 r2 r4 r5).toGrid (0, 0)))
        (p.1 - ((2^k + (2^k : Int))) + (2^(k - 1) : Int),
         p.2 - ((2^k + (2^k : Int))) + (2^(k - 1) : Int)) = true ∧
      ((2^k + (2^k : Int))) ≤ p.1 ∧
        p.1 < ((2^k + (2^k : Int))) + 2^((k - 1) + 1) ∧
      ((2^k + (2^k : Int))) ≤ p.2 ∧
        p.2 < ((2^k + (2^k : Int))) + 2^((k - 1) + 1) := by
  have hcc : centralCorrect (node r1 r2 r4 r5) (k - 1) :=
    p4_wave2_ih_step k hk1 r1 r2 r4 r5
      hr1_l hr2_l hr4_l hr5_l hr1_w hr2_w hr4_w hr5_w ih
  exact centralCorrect_mem_shift (node r1 r2 r4 r5) (k - 1)
    (2^k + (2^k : Int)) (2^k + (2^k : Int)) p hcc

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

end Life
end Conway
