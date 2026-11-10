/-  # HashlifeCorrectness.Walls.SE.Overlap

Mur de recouvrement SE (miroir diagonal de NW).

Extrait de `Walls/SE.lean` sans reecriture (decoupage #13483) : enonces et
preuves deplaces tels quels ; seule la visibilite change (`private` retire
sur les theoremes partages) pour qu'un maillon aval puisse les citer.
-/

import Conway.Life.HashlifeCorrectness.Walls.SE.Shift

namespace Conway
namespace Life

open MacroCell

set_option maxHeartbeats 4000000 in
/-- **SE overlap wall (PROUVÉ — miroir DIAGONAL de `p4_nw_overlap_wall` /
    `p4_ne_overlap_wall`, indices `{5,6,8,9}`).**
    Le mur SE : la grille parent une-fois half-steppée coïncide, sur la boîte
    Chebyshev `2^(k-1)` autour de tout point `p` de la fenêtre SE, avec le
    supercell wave-1 SE `node R5 R6 R8 R9` lu au point local SE-ancré
    `(q - (2^k + 2^(k-1)))` sur les DEUX coordonnées (réflexion diagonale
    de NW).

    **Renforcement d'énoncé (même verdict que les murs NE/SW — la forme
    libre `∀ r ∈ lightCone p (2^k)` avec `p` non contraint était FAUSSE,
    réfutable hors de la fenêtre SE).** L'énoncé porte désormais : (1) la
    fenêtre `hp` — la forme EXACTE des bornes produites par
    `p4_se_shift_lemma` (`hsup.2` dans `p4_se_membership_arm`, zéro friction
    de câblage) ; (2) les hypothèses structurelles `hn1..hn8` (niveau `k+1`
    + `wf` des nœuds de recombinaison touchés). Assemblage identique aux
    murs NE/SW : fenêtre → quadrant (`by_cases` sur le point recentré) →
    localité Chebyshev (`evolve_box_agree_local`) sur le nœud de
    recombinaison du quadrant (`p4_nw_parent_agree_n5`,
    `p4_ne_parent_agree_n6`, `p4_sw_parent_agree_n8`,
    `p4_se_parent_agree_n9`) → caractérisation `p4_nw_rside_char_*`
    (paramétrique, réutilisée telle quelle sur le quadruple
    `(R5, R6, R8, R9)`). Ferme le sorry résiduel SE de #6724 (S3). -/
theorem p4_se_overlap_wall
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
    ∀ q, chebDist p q ≤ 2^(k - 1) →
      isAlive (evolve (2^(k - 1))
          ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
                 (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
            (0, 0))) q
        = isAlive ((node R5 R6 R8 R9).toGrid (0, 0))
            (q.1 - ((2^k : Int) + (2^(k - 1) : Int)),
             q.2 - ((2^k : Int) + (2^(k - 1) : Int))) := by
  intro q hq
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
  have hA : (2 ^ (k - 1 + 1) : Int) = (2 ^ k : Int) := by
    have hk : k - 1 + 1 = k := by omega
    rw [hk]
  have hu2 : (2 ^ k : Int) = (2 ^ (k - 1) : Int) + (2 ^ (k - 1) : Int) := by
    rw [← hA, pow_succ]; ring
  have hcastu : ((2 ^ (k - 1) : Nat) : Int) = (2 ^ (k - 1) : Int) := by norm_cast
  rw [hA] at hp2 hp4
  obtain ⟨hq1, hq2⟩ := coord_bound_of_chebDist_le p q _ hq
  by_cases hcx1 : q.1 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) < (2 ^ k : Int) <;>
    by_cases hcx2 : q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) < (2 ^ k : Int)
  · -- Quadrant NO du supercell : `n5` (nœud centre, PARTAGÉ avec les autres
    -- murs), translaté `(2^k, 2^k)`. Réutilisation de `p4_nw_parent_agree_n5`.
    have hbox : ∀ r, chebDist q r ≤ 2 ^ (k - 1) →
        isAlive ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
            (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid (0, 0)) r
          = isAlive (shift ((2 ^ k : Int), (2 ^ k : Int))
              ((node nw_se ne_sw sw_ne se_nw).toGrid (0, 0))) r := by
      intro r hr
      obtain ⟨hr1, hr2⟩ := coord_bound_of_chebDist_le q r _ hr
      rw [isAlive_shift, ← p4_isAlive_toGrid_shift]
      exact p4_nw_parent_agree_n5 k nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se hn1_l hn1_w hn2_l hn2_w
        hn4_l hn4_w hn5_l hn5_w r
        ⟨by omega, by omega, by omega, by omega⟩
    have hL := evolve_box_agree_local (2 ^ (k - 1)) _ _ q hbox
    rw [hL, ← evolve_shift, isAlive_shift]
    have hx' : 0 ≤ q.1 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) ∧
        q.1 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) < (2 ^ k : Int) ∧
        0 ≤ q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) ∧
        q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) < (2 ^ k : Int) :=
      ⟨by omega, by omega, by omega, by omega⟩
    rw [p4_nw_rside_char_nw k hk1 _ _ _ _ R5 R6 R8 R9 hR5 hR6 hR8 hR9 hR5_l
        hcc5 hcc6 hcc8 hcc9
        (q.1 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)),
         q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int))) hx']
    congr 1
    ext <;> (try dsimp only) <;> omega
  · -- Quadrant NE du supercell : `n6`, translaté `(2^k, 2·2^k)`.
    have hbox : ∀ r, chebDist q r ≤ 2 ^ (k - 1) →
        isAlive ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
            (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid (0, 0)) r
          = isAlive (shift ((2 ^ k : Int), (2 ^ k : Int) + (2 ^ k : Int))
              ((node ne_sw ne_se se_nw se_ne).toGrid (0, 0))) r := by
      intro r hr
      obtain ⟨hr1, hr2⟩ := coord_bound_of_chebDist_le q r _ hr
      rw [isAlive_shift, ← p4_isAlive_toGrid_shift]
      exact p4_ne_parent_agree_n6 k nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se hn1_l hn1_w hn3_l hn3_w
        hn6_l hn6_w hn7_l hn7_w r
        ⟨by omega, by omega, by omega, by omega⟩
    have hL := evolve_box_agree_local (2 ^ (k - 1)) _ _ q hbox
    rw [hL, ← evolve_shift, isAlive_shift]
    have hx' : 0 ≤ q.1 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) ∧
        q.1 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) < (2 ^ k : Int) ∧
        (2 ^ k : Int) ≤ q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) ∧
        q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) < (2 ^ k : Int) + (2 ^ k : Int) :=
      ⟨by omega, by omega, by omega, by omega⟩
    rw [p4_nw_rside_char_ne k hk1 _ _ _ _ R5 R6 R8 R9 hR5 hR6 hR8 hR9 hR5_l
        hcc5 hcc6 hcc8 hcc9
        (q.1 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)),
         q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int))) hx']
    congr 1
    ext <;> (try dsimp only) <;> omega
  · -- Quadrant SO du supercell : `n8`, translaté `(2·2^k, 2^k)`.
    have hbox : ∀ r, chebDist q r ≤ 2 ^ (k - 1) →
        isAlive ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
            (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid (0, 0)) r
          = isAlive (shift ((2 ^ k : Int) + (2 ^ k : Int), (2 ^ k : Int))
              ((node sw_ne se_nw sw_se se_sw).toGrid (0, 0))) r := by
      intro r hr
      obtain ⟨hr1, hr2⟩ := coord_bound_of_chebDist_le q r _ hr
      rw [isAlive_shift, ← p4_isAlive_toGrid_shift]
      exact p4_sw_parent_agree_n8 k nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se hn1_l hn1_w hn3_l hn3_w
        hn7_l hn7_w hn8_l hn8_w r
        ⟨by omega, by omega, by omega, by omega⟩
    have hL := evolve_box_agree_local (2 ^ (k - 1)) _ _ q hbox
    rw [hL, ← evolve_shift, isAlive_shift]
    have hx' : (2 ^ k : Int) ≤ q.1 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) ∧
        q.1 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) < (2 ^ k : Int) + (2 ^ k : Int) ∧
        0 ≤ q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) ∧
        q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) < (2 ^ k : Int) :=
      ⟨by omega, by omega, by omega, by omega⟩
    rw [p4_nw_rside_char_sw k hk1 _ _ _ _ R5 R6 R8 R9 hR5 hR6 hR8 hR9 hR5_l
        hcc5 hcc6 hcc8 hcc9
        (q.1 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)),
         q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int))) hx']
    congr 1
    ext <;> (try dsimp only) <;> omega
  · -- Quadrant SE du supercell : `n9` (l'enfant SE du parent), translaté
    -- `(2·2^k, 2·2^k)`.
    have hbox : ∀ r, chebDist q r ≤ 2 ^ (k - 1) →
        isAlive ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
            (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid (0, 0)) r
          = isAlive (shift ((2 ^ k : Int) + (2 ^ k : Int), (2 ^ k : Int) + (2 ^ k : Int))
              ((node se_nw se_ne se_sw se_se).toGrid (0, 0))) r := by
      intro r hr
      obtain ⟨hr1, hr2⟩ := coord_bound_of_chebDist_le q r _ hr
      rw [isAlive_shift, ← p4_isAlive_toGrid_shift]
      exact p4_se_parent_agree_n9 k nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se hn1_l hn1_w hn3_l hn3_w
        hn7_l hn7_w r
        ⟨by omega, by omega, by omega, by omega⟩
    have hL := evolve_box_agree_local (2 ^ (k - 1)) _ _ q hbox
    rw [hL, ← evolve_shift, isAlive_shift]
    have hx' : (2 ^ k : Int) ≤ q.1 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) ∧
        q.1 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) < (2 ^ k : Int) + (2 ^ k : Int) ∧
        (2 ^ k : Int) ≤ q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) ∧
        q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) < (2 ^ k : Int) + (2 ^ k : Int) :=
      ⟨by omega, by omega, by omega, by omega⟩
    rw [p4_nw_rside_char_se k hk1 _ _ _ _ R5 R6 R8 R9 hR5 hR6 hR8 hR9 hR5_l
        hcc5 hcc6 hcc8 hcc9
        (q.1 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)),
         q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int))) hx']
    congr 1
    ext <;> (try dsimp only) <;> omega

end Life
end Conway
