/-  # HashlifeCorrectness.Walls.SE.Arm

Bras d'appartenance SE (.mp), le plus couteux (16M heartbeats).

Extrait de `Walls/SE.lean` sans reecriture (decoupage #13483) : enonces et
preuves deplaces tels quels ; seule la visibilite change (`private` retire
sur les theoremes partages) pour qu'un maillon aval puisse les citer.
-/

import Conway.Life.HashlifeCorrectness.Walls.SE.Supercell

namespace Conway
namespace Life

open MacroCell

set_option maxHeartbeats 16000000 in
/-- **c.90 §4 — SE membership arm (opaque-binder, sorry-free wiring —
    diagonal mirror of the NW arm L3273 / same skeleton as SW arm L3751).**
    Discharges the SE quadrant of `p4_succ_membership` over OPAQUE wave-1
    results `R5 R6 R8 R9` (SE supercell wave-1 sub-cells), with a fresh
    heartbeat budget. The `p4_succ_membership` call site merely *applies*
    this arm with `R_j := hashlifeResultAux (k+1) n_j` (pure substitution,
    no whnf). `p4_se_overlap_wall` (via `p4_se_supercell_agree` →
    `p4_se_g3_bridge`) is now fully proven (windowed, mirror of the NE
    precedent) — this arm is sorry-free at the axiom level.

    Chain: `p4_se_shift_lemma.mp` (supercell isAlive at `p'` + window bounds
    at SE outer offset `(2^k + 2^k, 2^k + 2^k)`) → `mem_restrictGridTo` →
    `isAlive_true_iff_mem` + `evolve_half_step` + `p4_se_supercell_agree`
    fold the membership into `hsup.1`; the four coordinate bounds discharge
    from the shift window by omega (both row AND column use the SW row
    pattern — the SE offset is outer on both axes).

    Same `hout_nw` opaque-binder pattern as the NE/SW arms: both SE offsets
    are anchored on `2^out_nw.level` (the outer NW supercell's level — the
    common reference for all four quadrants). -/
theorem p4_se_membership_arm
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
  rw [show ((2^k : Int) + (2^hout_nw.level : Int)) = (2^k + (2^k : Int)) from by
    rw [congrArg (fun n => (2^n : Int)) hout_nw_l]] at hse
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
    -- Shared arithmetic facts hoisted out of the four IH projections: each
    -- inline `by omega` re-runs omega preprocessing over the arm's full
    -- 18-hypothesis `hn*` context (~1M heartbeats per `have` measured),
    -- so we pay that cost twice instead of eight times.
    have hklt : k - 1 < k := by omega
    have hlvl : k + 1 = (k - 1) + 2 := by omega
    have hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1) :=
      ih _ (k - 1) hklt hn5_w (by rw [hn5_l]; exact hlvl)
    have hcc6 : centralCorrect (node ne_sw ne_se se_nw se_ne) (k - 1) :=
      ih _ (k - 1) hklt hn6_w (by rw [hn6_l]; exact hlvl)
    have hcc8 : centralCorrect (node sw_ne se_nw sw_se se_sw) (k - 1) :=
      ih _ (k - 1) hklt hn8_w (by rw [hn8_l]; exact hlvl)
    have hcc9 : centralCorrect (node se_nw se_ne se_sw se_se) (k - 1) :=
      ih _ (k - 1) hklt hn9_w (by rw [hn9_l]; exact hlvl)
    rw [p4_se_supercell_agree k hk1
          nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
          sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
          R5 R6 R8 R9 hR5 hR6 hR8 hR9
          hn1_l hn2_l hn3_l hn4_l hn5_l hn6_l hn7_l hn8_l
          hn1_w hn2_w hn3_w hn4_w hn5_w hn6_w hn7_w hn8_w
          hR5_l hR6_l hR8_l hR9_l hcc5 hcc6 hcc8 hcc9 p hsup.2]
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

end Life
end Conway
