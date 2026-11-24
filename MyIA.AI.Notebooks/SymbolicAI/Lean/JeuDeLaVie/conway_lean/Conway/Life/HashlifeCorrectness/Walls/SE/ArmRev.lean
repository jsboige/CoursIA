/-  # HashlifeCorrectness.Walls.SE.ArmRev

Bras reciproque (.mpr) et assemblage.

Extrait de `Walls/SE.lean` sans reecriture (decoupage #13483) : enonces et
preuves deplaces tels quels ; seule la visibilite change (`private` retire
sur les theoremes partages) pour qu'un maillon aval puisse les citer.
-/

import Conway.Life.HashlifeCorrectness.Walls.SE.Arm

namespace Conway
namespace Life

open MacroCell

set_option maxHeartbeats 4000000 in
/-- **SE membership arm, reciprocal direction (mpr assembly — mirror of
    `p4_se_membership_arm`, diagonal reflection of the NW rev arm).**
    Both SE anchor coordinates carry `2^hout_nw.level`; the single inline
    bridge `rw` rewrites both occurrences at once (same as the mp arm).
    `p4_se_supercell_agree` now rests on the proven windowed
    `p4_se_overlap_wall` — this arm is sorry-free at the axiom level. -/
theorem p4_se_membership_arm_rev
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R5 R6 R8 R9 : MacroCell)
    (hR5 : R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
    (hR6 : R6 = hashlifeResultAux (k + 1) (node ne_sw ne_se se_nw se_ne))
    (hR8 : R8 = hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
    (hR9 : R9 = hashlifeResultAux (k + 1) (node se_nw se_ne se_sw se_se))
    (hn1_l : (node nw_nw nw_ne nw_sw nw_se).level = k + 1)
    (hn2_l : (node nw_ne ne_nw nw_se ne_sw).level = k + 1)
    (hn3_l : (node ne_nw ne_ne ne_sw ne_se).level = k + 1)
    (hn4_l : (node nw_sw nw_se sw_nw sw_ne).level = k + 1)
    (hn5_l : (node nw_se ne_sw sw_ne se_nw).level = k + 1)
    (hn6_l : (node ne_sw ne_se se_nw se_ne).level = k + 1)
    (hn7_l : (node sw_nw sw_ne sw_sw sw_se).level = k + 1)
    (hn8_l : (node sw_ne se_nw sw_se se_sw).level = k + 1)
    (hn9_l : (node se_nw se_ne se_sw se_se).level = k + 1)
    (hn1_w : (node nw_nw nw_ne nw_sw nw_se).wf = true)
    (hn2_w : (node nw_ne ne_nw nw_se ne_sw).wf = true)
    (hn3_w : (node ne_nw ne_ne ne_sw ne_se).wf = true)
    (hn4_w : (node nw_sw nw_se sw_nw sw_ne).wf = true)
    (hn5_w : (node nw_se ne_sw sw_ne se_nw).wf = true)
    (hn6_w : (node ne_sw ne_se se_nw se_ne).wf = true)
    (hn7_w : (node sw_nw sw_ne sw_sw sw_se).wf = true)
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
        hn1_l hn2_l hn3_l hn4_l hn5_l hn6_l hn7_l hn8_l
        hn1_w hn2_w hn3_w hn4_w hn5_w hn6_w hn7_w hn8_w
        hR5_l hR6_l hR8_l hR9_l hcc5 hcc6 hcc8 hcc9 p hw]
  rw [← evolve_half_step k hk1]
  rw [isAlive_true_iff_mem_local]
  exact hmem

end Life
end Conway
