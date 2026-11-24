/-  # HashlifeCorrectness.Walls.SE.Supercell

Accord de supercellule SE.

Extrait de `Walls/SE.lean` sans reecriture (decoupage #13483) : enonces et
preuves deplaces tels quels ; seule la visibilite change (`private` retire
sur les theoremes partages) pour qu'un maillon aval puisse les citer.
-/

import Conway.Life.HashlifeCorrectness.Walls.SE.G3

namespace Conway
namespace Life

open MacroCell

/-- **SE supercell agreement (PROUVÉ — miroir diagonal de
    `p4_nw_supercell_agree`).**
    Le double half-step du parent coïncide, au point recentré SE, avec le
    half-step du supercell wave-1 `node R5 R6 R8 R9`. Preuve : fold LHS
    (`evolve_half_step`, sorry-free) puis délégation intégrale à
    `p4_se_g3_bridge`, qui décharge l'outer-locality sur le mur
    `p4_se_overlap_wall` — désormais PROUVÉ (fenêtré + hypothèses
    structurelles `hn*`, mêmes renforcements que les murs NE/SW). L'énoncé
    porte donc la fenêtre `hp` (forme exacte des bornes du
    `p4_se_shift_lemma`, `hsup.2` dans l'arm). Ferme le sorry résiduel SE
    de #6724 (S3). -/
theorem p4_se_supercell_agree
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
    (hn1_w : (node nw_nw nw_ne nw_sw nw_se).wf = true)
    (hn2_w : (node nw_ne ne_nw nw_se ne_sw).wf = true)
    (hn3_w : (node ne_nw ne_ne ne_sw ne_se).wf = true)
    (hn4_w : (node nw_sw nw_se sw_nw sw_ne).wf = true)
    (hn5_w : (node nw_se ne_sw sw_ne se_nw).wf = true)
    (hn6_w : (node ne_sw ne_se se_nw se_ne).wf = true)
    (hn7_w : (node sw_nw sw_ne sw_sw sw_se).wf = true)
    (hn8_w : (node sw_ne se_nw sw_se se_sw).wf = true)
    (hR5_l : R5.level = k) (hR6_l : R6.level = k)
    (hR8_l : R8.level = k) (hR9_l : R9.level = k)
    (hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1))
    (hcc6 : centralCorrect (node ne_sw ne_se se_nw se_ne) (k - 1))
    (hcc8 : centralCorrect (node sw_ne se_nw sw_se se_sw) (k - 1))
    (hcc9 : centralCorrect (node se_nw se_ne se_sw se_se) (k - 1))
    (p : Int × Int)
    (hp : ((2^k + (2^k : Int))) ≤ p.1 ∧
          p.1 < ((2^k + (2^k : Int))) + 2^((k - 1) + 1) ∧
          ((2^k + (2^k : Int))) ≤ p.2 ∧
          p.2 < ((2^k + (2^k : Int))) + 2^((k - 1) + 1)) :
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
    hn1_l hn2_l hn3_l hn4_l hn5_l hn6_l hn7_l hn8_l
    hn1_w hn2_w hn3_w hn4_w hn5_w hn6_w hn7_w hn8_w
    hR5_l hR6_l hR8_l hR9_l
    hcc5 hcc6 hcc8 hcc9 p hp

end Life
end Conway
