/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Conway.Life.HashlifeCorrectness.Walls.SW

Sub-module of `Conway.Life.HashlifeCorrectness`. Phase 3b multi-agent
prover targets (Epic #1453). Scope: /-- **c.NNNN §1 — SW wave-1 overlap wall (named mirror of `p4_nw_overlap_wall`,
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
/-- **c.NNNN §1 — SW wave-1 overlap wall (named mirror of `p4_nw_overlap_wall`,
    indices `{4,5,7,8}`, NW-SE reflection of c.8122 NE's `{2,3,5,6}`).**
    OW holds the structural mirror of `p4_nw_overlap_wall` (L2945) for the
    SW wave-1 sub-cell quartet `(R4, R5, R7, R8)` = `(n4, n5, n7, n8)` per
    `p4_wave2_ih` L2631-2633. The four sub-cells overlap the SW supercell
    (and only the SW supercell) in the same way the NW quartet
    `(R1, R2, R4, R5)` overlaps the NW supercell: n4 is the NW-bridge,
    n5 the centre, n7 the SW quadrant, n8 the SW/SE bridge. Each `R_j`
    computes evolve 2^(k-1) on `n_j` by `centralCorrect`, but the
    *recomposition* into `hashlifeResultAux (k+1) (node R4 R5 R7 R8)`
    requires grid-level agreement on the central light cone — a structural
    realignment identical in shape to the NW case (L2945-c.750 firsthand map).

    ai-01 OW-authorized via #6875 tree-lock (mirror symmetry, c.8122
    closure of #6724 S3 — applied uniformly to N+1 components). The
    completion of `p4_nw_overlap_wall` via parametric generalization
    will simultaneously close this + the corresponding `p4_ne_overlap_wall`
    + `p4_se_overlap_wall` mirrors, leaving the 4-corner ceremony fully
    wired. Sorry count FLAT (no proof deleted).

    STATEMENT CORRECTION (c.19 piège, option a per ai-01 msg-233116): the
    conclusion offset was previously `(r.1 - 2^(k-1), r.2 - 2^(k-1))` — a
    copy of the NW mirror. But the SW quadrant is the BOTTOM-LEFT corner
    (row-shifted by `2^k` relative to NW, same column), so the correct
    offset is `(r.1 - (2^k + 2^(k-1)), r.2 - 2^(k-1))`. This matches the
    4-corner symmetry now consistent across all three existing walls:
    NW (top-left) = `(2^(k-1), 2^(k-1))`; SW (bottom-left, THIS) =
    `(2^k+2^(k-1), 2^(k-1))`; SE (bottom-right, ai-01 #9539) =
    `(2^k+2^(k-1), 2^k+2^(k-1))` — SOUTH ⇒ r.1 gains `2^k`, EAST ⇒ r.2
    gains `2^k`. No `exact` consumer (verified firsthand), so the
    correction is scaffold-only. The proof remains research-level (#3846);
    `sorry` is retained. -/
private theorem p4_sw_overlap_wall
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R4 R5 R7 R8 : MacroCell)
    (hR4 : R4 = hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
    (hR5 : R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
    (hR7 : R7 = hashlifeResultAux (k + 1) (node sw_nw sw_ne sw_sw sw_se))
    (hR8 : R8 = hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
    (hR4_l : R4.level = k) (hR5_l : R5.level = k)
    (hR7_l : R7.level = k) (hR8_l : R8.level = k)
    (hcc4 : centralCorrect (node nw_sw nw_se sw_nw sw_ne) (k - 1))
    (hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1))
    (hcc7 : centralCorrect (node sw_nw sw_ne sw_sw sw_se) (k - 1))
    (hcc8 : centralCorrect (node sw_ne se_nw sw_se se_sw) (k - 1))
    (p : Int × Int) :
    ∀ r ∈ lightCone p (2^k),
      isAlive (evolve (2^(k - 1))
          ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
                 (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
            (0, 0))) r
        = isAlive ((node R4 R5 R7 R8).toGrid (0, 0))
            (r.1 - ((2^k : Int) + (2^(k - 1) : Int)),
             r.2 - (2^(k - 1) : Int)) := by
  sorry

/-- **c.NNNN §2 — SW-quadrant supercell agreement (mirror of `p4_ne_supercell_agree`
    L3324, NW-SE reflection; carries the residual `p4_sw_overlap_wall` sorry
    in its own named lemma).**
    Same defensive factorization as the NE counterpart: the LHS double
    half-step fold is mechanical via `evolve_half_step` (sorry-free L2370),
    the residual is the grid-level overlap realignment on the central light
    cone — here named `p4_sw_overlap_wall` above (mirror of
    `p4_nw_overlap_wall` per #6875 OW).

    The eval-point translation is the SW analog of the NE form
    (L3345-3346, `(p.1 - 2^k + 2^(k-1), p.2 - (2^k + 2^k) + 2^(k-1))`):
    SW sits at outer offset `(2^k + 2^k, 2^k)` so the row gets the full
    `2^k + 2^k` shift while the column gets the standard `2^k` shift —
    i.e. `(p.1 - (2^k + 2^k) + 2^(k-1), p.2 - 2^k + 2^(k-1))`. The
    membership arm `p4_sw_membership_arm` (next) folds the SW shift lemma's
    `.mp` into this form over opaque R_j.

    Sorry count FLAT (8 → 8) : aucune preuve supprimée, l'énoncé est *renforcé*
    (anti-régression §D ne s'applique pas). ai-01 en garde la preuve (tree-lock
    #6875) ; la frontière reste au niveau `evolve` pour la compilabilité du
    câblage. -/
private theorem p4_sw_supercell_agree
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R4 R5 R7 R8 : MacroCell)
    (hR4 : R4 = hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
    (hR5 : R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
    (hR7 : R7 = hashlifeResultAux (k + 1) (node sw_nw sw_ne sw_sw sw_se))
    (hR8 : R8 = hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
    (hR4_l : R4.level = k) (hR5_l : R5.level = k)
    (hR7_l : R7.level = k) (hR8_l : R8.level = k)
    (hcc4 : centralCorrect (node nw_sw nw_se sw_nw sw_ne) (k - 1))
    (hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1))
    (hcc7 : centralCorrect (node sw_nw sw_ne sw_sw sw_se) (k - 1))
    (hcc8 : centralCorrect (node sw_ne se_nw sw_se se_sw) (k - 1))
    (p : Int × Int) :
    isAlive (evolve (2^(k - 1)) (evolve (2^(k - 1))
        ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
          (0, 0)))) p
      = isAlive (evolve (2^(k - 1)) ((node R4 R5 R7 R8).toGrid (0, 0)))
          (p.1 - ((2^k + (2^k : Int)) : Int) + (2^(k - 1) : Int),
           p.2 - (2^k : Int) + (2^(k - 1) : Int)) := by
  -- The LHS fold `evolve 2^k = evolve 2^(k-1) ∘ evolve 2^(k-1)` is mechanical
  -- (same as NW/NE, sorry-free via `evolve_half_step` L2370). The residual is the
  -- 4-corner overlap wall at indices `{4,5,7,8}` (SW wave-1 sub-cells) — the
  -- structural mirror of `p4_nw_overlap_wall` (L2945) and `p4_ne_overlap_wall`
  -- — and lives as its own named lemma `p4_sw_overlap_wall` above (DEFERRED,
  -- OW-authorized by #6875 mirror symmetry to NW).
  rw [← evolve_half_step k hk1]
  sorry

set_option maxHeartbeats 1000000 in
/-- **c.NNNN §3 — SW membership arm (opaque-binder, sorry-free wiring — c.NNNN
    mirror of NE arm L3409, NW-SE reflection).**
    Discharges the SW quadrant of `p4_succ_membership` over OPAQUE wave-1
    results `R4 R5 R7 R8` (SW supercell wave-1 sub-cells), so this declaration
    gets a fresh 200000-heartbeat budget. The `p4_succ_membership` call site
    merely *applies* this arm with `R_j := hashlifeResultAux (k+1) n_j`
    (pure substitution, no whnf). The one residual sorry lives in
    `p4_sw_supercell_agree`; here everything else is wired.

    Chain: `p4_sw_shift_lemma.mp` (supercell isAlive at `p'` + window bounds
    at SW offset `(2^k + 2^(k-1), 2^k)`) → `mem_restrictGridTo` →
    `isAlive_true_iff_mem` + `evolve_half_step` + `p4_sw_supercell_agree`
    fold the membership into `hsup.1`; the four coordinate bounds discharge
    from the shift window (`2^((k-1)+1) = 2^k ≤ 2^(k+1)`) by omega.

    Same `hout_nw` opaque-binder pattern as the NE arm: the SW outer offset
    `(2^k + 2^k, 2^k)` is anchored on `2^out_nw.level` (the outer NW
    supercell's level — the same reference for all four quadrants). -/
private theorem p4_sw_membership_arm
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
    -- Geometric offset: SW supercell `(node R4 R5 R7 R8)` lives at outer
    -- offset `(2^k + 2^out_nw.level, 2^k)` per `mem_toGrid_node` (the
    -- SW row of the outer quadrants gets `2^k + 2^out_nw.level`; the
    -- SW column gets `2^k`). The arm takes `hout_nw_l : out_nw.level = k`
    -- and bridges `2^out_nw.level = 2^k` via `congrArg` (Lean 4's `2^x` is
    -- `HPow.hPow 2 x`, not a projection — plain `rw` cannot rewrite under it).
    -- Cf. c.8122 (NE arm), NW-SE reflection.
    (hout_nw : MacroCell)
    (hout_nw_l : hout_nw.level = k)
    (hsw : p ∈ (hashlifeResultAux (k + 1) (node R4 R5 R7 R8)).toGrid
            ((2^k : Int) + (2^hout_nw.level : Int), (2^k : Int))) :
    p ∈ restrictGridTo (evolve (2^k)
        ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
          (0, 0)))
        (2^k : Int) (2^(k+1)) := by
  -- Fuel-align (k+1) → (k-1)+2 on the OPAQUE-node membership, then bridge the
  -- SW offset `2^hout_nw.level` to literal `2^k` via `congrArg`. The bridge
  -- consumes `hout_nw_l : hout_nw.level = k`. Then the SW shift lemma's `.mp`
  -- is whnf-clean over opaque `R_j` (fresh budget).
  rw [show (k + 1) = (k - 1) + 2 from by omega] at hsw
  have hpow : (2^hout_nw.level : Int) = (2^k : Int) :=
    congrArg (fun n => (2^n : Int)) hout_nw_l
  have hbridge : (2^k + (2^hout_nw.level : Int)) = (2^k + (2^k : Int)) := by
    rw [hpow]
  rw [hbridge] at hsw
  have hsup := (p4_sw_shift_lemma k hk1 R4 R5 R7 R8
      hR4_l hR5_l hR7_l hR8_l hR4_w hR5_w hR7_w hR8_w ih p).mp hsw
  -- hsup.1 : isAlive (evolve 2^(k-1) ((node R4 R5 R7 R8).toGrid 0)) p' = true
  -- hsup.2 : (2^k + 2^(k-1)) ≤ p.1 ∧ p.1 < (2^k + 2^(k-1)) + 2^((k-1)+1) ∧
  --          2^k ≤ p.2 ∧ p.2 < 2^k + 2^((k-1)+1)
  rw [mem_restrictGridTo]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- membership: fold `evolve 2^k` via half-step + SW supercell agreement into hsup.1
    rw [← isAlive_true_iff_mem_local]
    rw [evolve_half_step k hk1]
    -- The 4 wave-1 sub-cells of the SW supercell are n4/n5/n7/n8 (level k+1,
    -- G2 at level k-1). Each `centralCorrect n_j (k-1)` is the IH projection
    -- (j = k-1 < k by hk1, level j+2 = k+1 matches).
    have hcc4 : centralCorrect (node nw_sw nw_se sw_nw sw_ne) (k - 1) :=
      ih _ (k - 1) (by omega) hn4_w (by rw [hn4_l]; omega)
    have hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1) :=
      ih _ (k - 1) (by omega) hn5_w (by rw [hn5_l]; omega)
    have hcc7 : centralCorrect (node sw_nw sw_ne sw_sw sw_se) (k - 1) :=
      ih _ (k - 1) (by omega) hn7_w (by rw [hn7_l]; omega)
    have hcc8 : centralCorrect (node sw_ne se_nw sw_se se_sw) (k - 1) :=
      ih _ (k - 1) (by omega) hn8_w (by rw [hn8_l]; omega)
    rw [p4_sw_supercell_agree k hk1
          nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
          sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
          R4 R5 R7 R8 hR4 hR5 hR7 hR8
          hR4_l hR5_l hR7_l hR8_l hcc4 hcc5 hcc7 hcc8 p]
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
  · -- 2^k ≤ p.2 (hsup.2.2.2.1 : 2^k ≤ p.2 directly)
    exact hsup.2.2.2.1
  · -- p.2 < 2^k + 2^(k+1) (we have hsup.2.2.2.2 : p.2 < 2^k + 2^k; goal is p.2 < 2^k + 2·2^k = 3·2^k)
    have hb := hsup.2.2.2.2
    have he : (k - 1) + 1 = k := by omega
    rw [he] at hb
    have hbridge : ((2 ^ (k + 1) : Nat) : Int) = 2 ^ k + 2 ^ k := by
      push_cast; rw [pow_succ]; ring
    have hpos : (0 : Int) < 2 ^ k := pow_pos (by norm_num) k
    rw [hbridge]
    omega

end Life
end Conway
