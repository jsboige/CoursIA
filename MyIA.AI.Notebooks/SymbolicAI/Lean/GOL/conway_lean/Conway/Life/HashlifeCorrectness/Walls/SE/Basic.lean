/-  # HashlifeCorrectness.Walls.SE.Basic

Accord parent / `n9` translate (etape 1 de la chaine SE).

Extrait de `Walls/SE.lean` sans reecriture (decoupage #13483) : enonces et
preuves deplaces tels quels ; seule la visibilite change (`private` retire
sur les theoremes partages) pour qu'un maillon aval puisse les citer.
-/

import Conway.Life.HashlifeCorrectness.Foundation

namespace Conway
namespace Life

open MacroCell

/-- Accord parent / `n9` translaté de `(2·2^k, 2·2^k)` sur `[2·2^k, 4·2^k)²`.
    `n9 = node se_nw se_ne se_sw se_se` est l'enfant SE du parent lui-même :
    une seule décomposition, les trois autres quadrants s'excluent par bornes. -/
theorem p4_se_parent_agree_n9 (k : Nat)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
      sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (hn1_l : (node nw_nw nw_ne nw_sw nw_se).level = k + 1)
    (hn1_w : (node nw_nw nw_ne nw_sw nw_se).wf = true)
    (hn3_l : (node ne_nw ne_ne ne_sw ne_se).level = k + 1)
    (hn3_w : (node ne_nw ne_ne ne_sw ne_se).wf = true)
    (hn7_l : (node sw_nw sw_ne sw_sw sw_se).level = k + 1)
    (hn7_w : (node sw_nw sw_ne sw_sw sw_se).wf = true)
    (x : Int × Int)
    (hx : (2 ^ k : Int) + (2 ^ k : Int) ≤ x.1 ∧
          x.1 < (2 ^ k : Int) + (2 ^ k : Int) + (2 ^ k : Int) + (2 ^ k : Int) ∧
          (2 ^ k : Int) + (2 ^ k : Int) ≤ x.2 ∧
          x.2 < (2 ^ k : Int) + (2 ^ k : Int) + (2 ^ k : Int) + (2 ^ k : Int)) :
    isAlive ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
        (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid (0, 0)) x
      = isAlive ((node se_nw se_ne se_sw se_se).toGrid
          ((2 ^ k : Int) + (2 ^ k : Int), (2 ^ k : Int) + (2 ^ k : Int))) x := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  apply p4_bool_eq_of_iff
  rw [isAlive_true_iff_mem_local, isAlive_true_iff_mem_local]
  have hBB : (2 ^ (k + 1) : Int) = (2 ^ k : Int) + (2 ^ k : Int) := by
    rw [pow_succ]; ring
  rw [mem_toGrid_node (nw := node nw_nw nw_ne nw_sw nw_se), hn1_l, hBB]
  simp only [Int.zero_add, Int.add_zero]
  constructor
  · rintro (h | h | h | h)
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_lt _ _ _ x hn1_w h
      rw [hn1_l, hBB] at hr
      exfalso; omega
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_lt _ _ _ x hn3_w h
      rw [hn3_l, hBB] at hr
      exfalso; omega
    · obtain ⟨-, hc⟩ := p4_mem_toGrid_lt _ _ _ x hn7_w h
      rw [hn7_l, hBB] at hc
      exfalso; omega
    · exact h
  · intro h
    exact Or.inr (Or.inr (Or.inr h))

end Life
end Conway
