/-  # HashlifeCorrectness.Walls.SE

P4 SE quadrant: shift lemma + overlap wall + G3 bridge + supercell agreement +
membership arm (.mp) and its reciprocal (.mpr). Diagonal mirror of NW.
-/

import Conway.Life.HashlifeCorrectness.Foundation

namespace Conway
namespace Life

open MacroCell


/-- Accord parent / `n9` translaté de `(2·2^k, 2·2^k)` sur `[2·2^k, 4·2^k)²`.
    `n9 = node se_nw se_ne se_sw se_se` est l'enfant SE du parent lui-même :
    une seule décomposition, les trois autres quadrants s'excluent par bornes. -/
private theorem p4_se_parent_agree_n9 (k : Nat)
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

/-! ### Étape 4 (préparation) — caractérisation par quadrant du supernœud résultat

Le supernœud `node R1 R2 R4 R5` (niveau `k+1`) est caractérisé quadrant par
quadrant : sur chaque quadrant de `[0, 2·2^k)²`, sa grille vaut l'évolution
`2^(k-1)` du nœud de recombinaison correspondant, au point re-translaté que
produit `centralCorrect_mem_shift`. Les trois autres quadrants sont exclus par
leurs propres bornes (les conjonctions de `centralCorrect_mem_shift`), via
`hA : 2^(k-1+1) = 2^k` (qui exige `1 ≤ k`). -/


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
private theorem p4_se_overlap_wall
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


/-- **Bridge G3 SE (miroir diagonal de `p4_nw_g3_bridge`, PROUVÉ).**
    Décharge la moitié outer-locality : le double half-step du parent,
    évalué au point recentré du supercell SE, se transporte par
    `evolve_shift` + `evolve_box_agree_local` sur le mur
    `p4_se_overlap_wall` (désormais PROUVÉ, fenêtré). Le vecteur de shift
    est `(2^k + 2^(k-1), 2^k + 2^(k-1))` (l'ancre du supercell SE dans le
    parent — diagonale, les deux coordonnées symétriques). L'énoncé porte
    la fenêtre `hp` et les hypothèses structurelles `hn*` requises par le
    mur renforcé. -/
private theorem p4_se_g3_bridge
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
  -- Both sides eval at `p`. Transport through the outer `evolve (2^(k-1))`
  -- by Chebyshev-box locality onto the (proven) windowed wall.
  apply evolve_box_agree_local
  intro q hq
  rw [isAlive_shift]
  exact p4_se_overlap_wall k hk1
    nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
    sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
    R5 R6 R8 R9 hR5 hR6 hR8 hR9
    hn1_l hn2_l hn3_l hn4_l hn5_l hn6_l hn7_l hn8_l
    hn1_w hn2_w hn3_w hn4_w hn5_w hn6_w hn7_w hn8_w
    hR5_l hR6_l hR8_l hR9_l
    hcc5 hcc6 hcc8 hcc9 p hp q hq


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
private theorem p4_se_supercell_agree
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
