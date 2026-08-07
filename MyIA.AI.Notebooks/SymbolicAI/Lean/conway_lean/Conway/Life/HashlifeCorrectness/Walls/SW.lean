/-  # HashlifeCorrectness.Walls.SW

P4 SW quadrant: shift lemma + overlap wall + supercell agreement + membership arm (.mp)
and its reciprocal (.mpr). NW-SE reflection of NE.
-/

import Conway.Life.HashlifeCorrectness.Foundation

namespace Conway
namespace Life

open MacroCell


/-- Accord parent / `n7` translaté de `(2·2^k, 0)` sur `[2·2^k, 4·2^k) × [0, 2·2^k)`.
    `n7 = node sw_nw sw_ne sw_sw sw_se` est l'enfant SW du parent lui-même (comme
    `n3` est son enfant NE) : une seule décomposition suffit, les trois autres
    quadrants du parent s'excluent par leurs bornes. -/
private theorem p4_sw_parent_agree_n7 (k : Nat)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
      sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (hn1_l : (node nw_nw nw_ne nw_sw nw_se).level = k + 1)
    (hn1_w : (node nw_nw nw_ne nw_sw nw_se).wf = true)
    (x : Int × Int)
    (hx : (2 ^ k : Int) + (2 ^ k : Int) ≤ x.1 ∧
          x.1 < (2 ^ k : Int) + (2 ^ k : Int) + (2 ^ k : Int) + (2 ^ k : Int) ∧
          0 ≤ x.2 ∧ x.2 < (2 ^ k : Int) + (2 ^ k : Int)) :
    isAlive ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
        (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid (0, 0)) x
      = isAlive ((node sw_nw sw_ne sw_sw sw_se).toGrid
          ((2 ^ k : Int) + (2 ^ k : Int), 0)) x := by
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
    · obtain ⟨-, hc⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
    · exact h
    · obtain ⟨-, hc⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
  · intro h
    exact Or.inr (Or.inr (Or.inl h))


/-- Accord parent / `n8` translaté de `(2·2^k, 2^k)` sur `[2·2^k, 4·2^k) × [2^k, 3·2^k)`.
    Miroir transposé de `p4_ne_parent_agree_n6` : `n8 = node sw_ne se_nw sw_se se_sw`
    chevauche les enfants SW et SE du parent ; on décompose ces deux enfants et on
    exclut leurs colonnes hors-fenêtre. -/
private theorem p4_sw_parent_agree_n8 (k : Nat)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
      sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (hn1_l : (node nw_nw nw_ne nw_sw nw_se).level = k + 1)
    (hn1_w : (node nw_nw nw_ne nw_sw nw_se).wf = true)
    (hn3_l : (node ne_nw ne_ne ne_sw ne_se).level = k + 1)
    (hn3_w : (node ne_nw ne_ne ne_sw ne_se).wf = true)
    (hn7_l : (node sw_nw sw_ne sw_sw sw_se).level = k + 1)
    (hn7_w : (node sw_nw sw_ne sw_sw sw_se).wf = true)
    (hn8_l : (node sw_ne se_nw sw_se se_sw).level = k + 1)
    (hn8_w : (node sw_ne se_nw sw_se se_sw).wf = true)
    (x : Int × Int)
    (hx : (2 ^ k : Int) + (2 ^ k : Int) ≤ x.1 ∧
          x.1 < (2 ^ k : Int) + (2 ^ k : Int) + (2 ^ k : Int) + (2 ^ k : Int) ∧
          (2 ^ k : Int) ≤ x.2 ∧ x.2 < (2 ^ k : Int) + (2 ^ k : Int) + (2 ^ k : Int)) :
    isAlive ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
        (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid (0, 0)) x
      = isAlive ((node sw_ne se_nw sw_se se_sw).toGrid
          ((2 ^ k : Int) + (2 ^ k : Int), (2 ^ k : Int))) x := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hl_swnw, hl_swne, hl_swsw, -, hw_swnw, -, hw_swsw, -⟩ :=
    wf_node_quad_level hn7_l hn7_w
  obtain ⟨-, hl_senw, -, -, -, -, -, -⟩ :=
    wf_node_quad_level hn8_l hn8_w
  apply p4_bool_eq_of_iff
  rw [isAlive_true_iff_mem_local, isAlive_true_iff_mem_local]
  have hBB : (2 ^ (k + 1) : Int) = (2 ^ k : Int) + (2 ^ k : Int) := by
    rw [pow_succ]; ring
  rw [mem_toGrid_node (nw := sw_ne) (ne := se_nw) (sw := sw_se) (se := se_sw), hl_swne]
  rw [mem_toGrid_node (nw := node nw_nw nw_ne nw_sw nw_se), hn1_l, hBB]
  rw [mem_toGrid_node (nw := sw_nw) (ne := sw_ne) (sw := sw_sw) (se := sw_se), hl_swnw]
  rw [mem_toGrid_node (nw := se_nw) (ne := se_ne) (sw := se_sw) (se := se_se), hl_senw]
  simp only [Int.zero_add, Int.add_zero]
  constructor
  · rintro (h | h | (h | h | h | h) | (h | h | h | h))
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_lt _ _ _ x hn1_w h
      rw [hn1_l, hBB] at hr
      exfalso; omega
    · obtain ⟨hr, -⟩ := p4_mem_toGrid_lt _ _ _ x hn3_w h
      rw [hn3_l, hBB] at hr
      exfalso; omega
    · obtain ⟨-, hc⟩ := p4_mem_toGrid_lt _ _ _ x hw_swnw h
      rw [hl_swnw] at hc
      exfalso; omega
    · exact Or.inl h
    · obtain ⟨-, hc⟩ := p4_mem_toGrid_lt _ _ _ x hw_swsw h
      rw [hl_swsw] at hc
      exfalso; omega
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · obtain ⟨-, hc⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
    · exact Or.inr (Or.inr (Or.inr h))
    · obtain ⟨-, hc⟩ := p4_mem_toGrid_origin_le _ _ _ x h
      exfalso; omega
  · rintro (h | h | h | h)
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))


/-- **P4.4 SW-quadrant shift lemma (factorisé, c.552 — rebase de #6944 sur main post-#6955).**
    Symétrique au `p4_ne_shift_lemma` pour l'offset SW OUTER `(2^k + 2^k, 2^k) = (2^(k+1), 2^k)`.
    Convention uniforme avec NE/NW (c.8122) : les 4 shift lemmas sont au niveau
    OUTER (la super-cellule dans la fenêtre centrée du parent), pas au niveau
    QUADRANT intérieur. Le bug de convention c.552 (offset `(2^k + 2^(k-1), ...)`)
    a été corrigé pour matcher l'offset du `p4_sw_membership_arm` après bridge
    `2^out_nw.level = 2^k`. Sorry-free. -/
private theorem p4_sw_shift_lemma
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
          ((2^k + (2^k : Int), (2^k : Int))) ↔
      isAlive (evolve (2^(k - 1)) ((node r1 r2 r4 r5).toGrid (0, 0)))
        (p.1 - ((2^k + (2^k : Int))) + (2^(k - 1) : Int),
         p.2 - (2^k : Int) + (2^(k - 1) : Int)) = true ∧
      ((2^k + (2^k : Int))) ≤ p.1 ∧
        p.1 < ((2^k + (2^k : Int))) + 2^((k - 1) + 1) ∧
      (2^k : Int) ≤ p.2 ∧ p.2 < (2^k : Int) + 2^((k - 1) + 1) := by
  have hcc : centralCorrect (node r1 r2 r4 r5) (k - 1) :=
    p4_wave2_ih_step k hk1 r1 r2 r4 r5
      hr1_l hr2_l hr4_l hr5_l hr1_w hr2_w hr4_w hr5_w ih
  exact centralCorrect_mem_shift (node r1 r2 r4 r5) (k - 1)
    (2^k + (2^k : Int)) (2^k) p hcc


/-- **SW wave-1 overlap wall (PROUVÉ — miroir NW-SE de `p4_ne_overlap_wall`,
    indices `{4,5,7,8}`).**
    Le mur SW : la grille parent une-fois half-steppée coïncide, sur la boîte
    Chebyshev `2^(k-1)` autour de tout point `p` de la fenêtre SW, avec le
    supercell wave-1 SW `node R4 R5 R7 R8` lu au point local SW-ancré
    `(q.1 - (2^k + 2^(k-1)), q.2 - 2^(k-1))`.

    **Renforcement d'énoncé (même verdict que le mur NE — la forme libre
    `∀ r ∈ lightCone p (2^k)` avec `p` non contraint était FAUSSE, réfutable
    hors de la fenêtre SW).** L'énoncé porte désormais : (1) la fenêtre `hp` —
    la forme EXACTE des bornes produites par `p4_sw_shift_lemma` (`hsup.2`
    dans `p4_sw_membership_arm`, zéro friction de câblage) ; (2) les
    hypothèses structurelles `hn1..hn5, hn7, hn8` (niveau `k+1` + `wf` des
    nœuds de recombinaison ET des enfants du parent touchés par les
    exclusions de bornes). Assemblage identique au mur NE : fenêtre →
    quadrant (`by_cases` sur le point recentré) → localité Chebyshev
    (`evolve_box_agree_local`) sur le nœud de recombinaison du quadrant
    (`p4_nw_parent_agree_n4/n5`, `p4_sw_parent_agree_n7/n8`) →
    caractérisation `p4_nw_rside_char_*` (paramétrique, réutilisée telle
    quelle sur le quadruple `(R4, R5, R7, R8)`). Ferme le sorry résiduel SW
    de #6724 (S3). -/
private theorem p4_sw_overlap_wall
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R4 R5 R7 R8 : MacroCell)
    (hR4 : R4 = hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
    (hR5 : R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
    (hR7 : R7 = hashlifeResultAux (k + 1) (node sw_nw sw_ne sw_sw sw_se))
    (hR8 : R8 = hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
    (hn1_l : (node nw_nw nw_ne nw_sw nw_se).level = k + 1)
    (hn2_l : (node nw_ne ne_nw nw_se ne_sw).level = k + 1)
    (hn3_l : (node ne_nw ne_ne ne_sw ne_se).level = k + 1)
    (hn4_l : (node nw_sw nw_se sw_nw sw_ne).level = k + 1)
    (hn5_l : (node nw_se ne_sw sw_ne se_nw).level = k + 1)
    (hn7_l : (node sw_nw sw_ne sw_sw sw_se).level = k + 1)
    (hn8_l : (node sw_ne se_nw sw_se se_sw).level = k + 1)
    (hn1_w : (node nw_nw nw_ne nw_sw nw_se).wf = true)
    (hn2_w : (node nw_ne ne_nw nw_se ne_sw).wf = true)
    (hn3_w : (node ne_nw ne_ne ne_sw ne_se).wf = true)
    (hn4_w : (node nw_sw nw_se sw_nw sw_ne).wf = true)
    (hn5_w : (node nw_se ne_sw sw_ne se_nw).wf = true)
    (hn7_w : (node sw_nw sw_ne sw_sw sw_se).wf = true)
    (hn8_w : (node sw_ne se_nw sw_se se_sw).wf = true)
    (hR4_l : R4.level = k) (hR5_l : R5.level = k)
    (hR7_l : R7.level = k) (hR8_l : R8.level = k)
    (hcc4 : centralCorrect (node nw_sw nw_se sw_nw sw_ne) (k - 1))
    (hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1))
    (hcc7 : centralCorrect (node sw_nw sw_ne sw_sw sw_se) (k - 1))
    (hcc8 : centralCorrect (node sw_ne se_nw sw_se se_sw) (k - 1))
    (p : Int × Int)
    (hp : ((2^k + (2^k : Int))) ≤ p.1 ∧
          p.1 < ((2^k + (2^k : Int))) + 2^((k - 1) + 1) ∧
          (2^k : Int) ≤ p.2 ∧ p.2 < (2^k : Int) + 2^((k - 1) + 1)) :
    ∀ q, chebDist p q ≤ 2^(k - 1) →
      isAlive (evolve (2^(k - 1))
          ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
                 (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
            (0, 0))) q
        = isAlive ((node R4 R5 R7 R8).toGrid (0, 0))
            (q.1 - ((2^k : Int) + (2^(k - 1) : Int)), q.2 - (2^(k - 1) : Int)) := by
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
    by_cases hcx2 : q.2 - (2 ^ (k - 1) : Int) < (2 ^ k : Int)
  · -- Quadrant NO du supercell : `n4`, translaté `(2^k, 0)`.
    have hbox : ∀ r, chebDist q r ≤ 2 ^ (k - 1) →
        isAlive ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
            (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid (0, 0)) r
          = isAlive (shift ((2 ^ k : Int), (0 : Int))
              ((node nw_sw nw_se sw_nw sw_ne).toGrid (0, 0))) r := by
      intro r hr
      obtain ⟨hr1, hr2⟩ := coord_bound_of_chebDist_le q r _ hr
      rw [isAlive_shift, ← p4_isAlive_toGrid_shift]
      exact p4_nw_parent_agree_n4 k nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se hn1_l hn1_w hn4_l hn4_w r
        ⟨by omega, by omega, by omega, by omega⟩
    have hL := evolve_box_agree_local (2 ^ (k - 1)) _ _ q hbox
    rw [hL, ← evolve_shift, isAlive_shift]
    have hx' : 0 ≤ q.1 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) ∧
        q.1 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) < (2 ^ k : Int) ∧
        0 ≤ q.2 - (2 ^ (k - 1) : Int) ∧ q.2 - (2 ^ (k - 1) : Int) < (2 ^ k : Int) :=
      ⟨by omega, by omega, by omega, by omega⟩
    rw [p4_nw_rside_char_nw k hk1 _ _ _ _ R4 R5 R7 R8 hR4 hR5 hR7 hR8 hR4_l
        hcc4 hcc5 hcc7 hcc8
        (q.1 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)), q.2 - (2 ^ (k - 1) : Int)) hx']
    congr 1
    ext <;> (try dsimp only) <;> omega
  · -- Quadrant NE du supercell : `n5` (nœud centre, PARTAGÉ avec les murs NW/NE),
    -- translaté `(2^k, 2^k)`. Réutilisation directe de `p4_nw_parent_agree_n5`.
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
        (2 ^ k : Int) ≤ q.2 - (2 ^ (k - 1) : Int) ∧
        q.2 - (2 ^ (k - 1) : Int) < (2 ^ k : Int) + (2 ^ k : Int) :=
      ⟨by omega, by omega, by omega, by omega⟩
    rw [p4_nw_rside_char_ne k hk1 _ _ _ _ R4 R5 R7 R8 hR4 hR5 hR7 hR8 hR4_l
        hcc4 hcc5 hcc7 hcc8
        (q.1 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)), q.2 - (2 ^ (k - 1) : Int)) hx']
    congr 1
    ext <;> (try dsimp only) <;> omega
  · -- Quadrant SO du supercell : `n7` (l'enfant SW du parent), translaté `(2·2^k, 0)`.
    have hbox : ∀ r, chebDist q r ≤ 2 ^ (k - 1) →
        isAlive ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
            (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid (0, 0)) r
          = isAlive (shift ((2 ^ k : Int) + (2 ^ k : Int), (0 : Int))
              ((node sw_nw sw_ne sw_sw sw_se).toGrid (0, 0))) r := by
      intro r hr
      obtain ⟨hr1, hr2⟩ := coord_bound_of_chebDist_le q r _ hr
      rw [isAlive_shift, ← p4_isAlive_toGrid_shift]
      exact p4_sw_parent_agree_n7 k nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se hn1_l hn1_w r
        ⟨by omega, by omega, by omega, by omega⟩
    have hL := evolve_box_agree_local (2 ^ (k - 1)) _ _ q hbox
    rw [hL, ← evolve_shift, isAlive_shift]
    have hx' : (2 ^ k : Int) ≤ q.1 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) ∧
        q.1 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) < (2 ^ k : Int) + (2 ^ k : Int) ∧
        0 ≤ q.2 - (2 ^ (k - 1) : Int) ∧ q.2 - (2 ^ (k - 1) : Int) < (2 ^ k : Int) :=
      ⟨by omega, by omega, by omega, by omega⟩
    rw [p4_nw_rside_char_sw k hk1 _ _ _ _ R4 R5 R7 R8 hR4 hR5 hR7 hR8 hR4_l
        hcc4 hcc5 hcc7 hcc8
        (q.1 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)), q.2 - (2 ^ (k - 1) : Int)) hx']
    congr 1
    ext <;> (try dsimp only) <;> omega
  · -- Quadrant SE du supercell : `n8`, translaté `(2·2^k, 2^k)`.
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
        (2 ^ k : Int) ≤ q.2 - (2 ^ (k - 1) : Int) ∧
        q.2 - (2 ^ (k - 1) : Int) < (2 ^ k : Int) + (2 ^ k : Int) :=
      ⟨by omega, by omega, by omega, by omega⟩
    rw [p4_nw_rside_char_se k hk1 _ _ _ _ R4 R5 R7 R8 hR4 hR5 hR7 hR8 hR4_l
        hcc4 hcc5 hcc7 hcc8
        (q.1 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)), q.2 - (2 ^ (k - 1) : Int)) hx']
    congr 1
    ext <;> (try dsimp only) <;> omega


/-- **Bridge G3 SW (miroir de `p4_ne_g3_bridge`).** Décharge la moitié
    outer-locality : le double half-step du parent, évalué au point recentré
    du supercell SW, se transporte par `evolve_shift` + `evolve_box_agree_local`
    sur le mur `p4_sw_overlap_wall`. Le vecteur de shift est
    `(2^k + 2^(k-1), 2^(k-1))` (l'ancre du supercell SW dans le parent). -/
private theorem p4_sw_g3_bridge
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R4 R5 R7 R8 : MacroCell)
    (hR4 : R4 = hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
    (hR5 : R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
    (hR7 : R7 = hashlifeResultAux (k + 1) (node sw_nw sw_ne sw_sw sw_se))
    (hR8 : R8 = hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
    (hn1_l : (node nw_nw nw_ne nw_sw nw_se).level = k + 1)
    (hn2_l : (node nw_ne ne_nw nw_se ne_sw).level = k + 1)
    (hn3_l : (node ne_nw ne_ne ne_sw ne_se).level = k + 1)
    (hn4_l : (node nw_sw nw_se sw_nw sw_ne).level = k + 1)
    (hn5_l : (node nw_se ne_sw sw_ne se_nw).level = k + 1)
    (hn7_l : (node sw_nw sw_ne sw_sw sw_se).level = k + 1)
    (hn8_l : (node sw_ne se_nw sw_se se_sw).level = k + 1)
    (hn1_w : (node nw_nw nw_ne nw_sw nw_se).wf = true)
    (hn2_w : (node nw_ne ne_nw nw_se ne_sw).wf = true)
    (hn3_w : (node ne_nw ne_ne ne_sw ne_se).wf = true)
    (hn4_w : (node nw_sw nw_se sw_nw sw_ne).wf = true)
    (hn5_w : (node nw_se ne_sw sw_ne se_nw).wf = true)
    (hn7_w : (node sw_nw sw_ne sw_sw sw_se).wf = true)
    (hn8_w : (node sw_ne se_nw sw_se se_sw).wf = true)
    (hR4_l : R4.level = k) (hR5_l : R5.level = k)
    (hR7_l : R7.level = k) (hR8_l : R8.level = k)
    (hcc4 : centralCorrect (node nw_sw nw_se sw_nw sw_ne) (k - 1))
    (hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1))
    (hcc7 : centralCorrect (node sw_nw sw_ne sw_sw sw_se) (k - 1))
    (hcc8 : centralCorrect (node sw_ne se_nw sw_se se_sw) (k - 1))
    (p : Int × Int)
    (hp : ((2^k + (2^k : Int))) ≤ p.1 ∧
          p.1 < ((2^k + (2^k : Int))) + 2^((k - 1) + 1) ∧
          (2^k : Int) ≤ p.2 ∧ p.2 < (2^k : Int) + 2^((k - 1) + 1)) :
    isAlive (evolve (2^k)
        ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
          (0, 0))) p
      = isAlive (evolve (2^(k - 1)) ((node R4 R5 R7 R8).toGrid (0, 0)))
          (p.1 - ((2^k + (2^k : Int)) : Int) + (2^(k - 1) : Int),
           p.2 - (2^k : Int) + (2^(k - 1) : Int)) := by
  rw [evolve_half_step k hk1]
  have h2k : (2^k : Int) = (2^(k - 1) : Int) + (2^(k - 1) : Int) := by
    have hn : 2^k = 2^(k - 1) + 2^(k - 1) := by
      set m := k - 1 with hm
      have hkm : k = m + 1 := by omega
      rw [hkm, Nat.pow_succ]; ring
    exact_mod_cast hn
  have hpt1 : p.1 - ((2^k + (2^k : Int)) : Int) + (2^(k - 1) : Int)
      = p.1 - ((2^k : Int) + (2^(k - 1) : Int)) := by omega
  have hpt2 : p.2 - (2^k : Int) + (2^(k - 1) : Int) = p.2 - (2^(k - 1) : Int) := by omega
  rw [hpt1, hpt2]
  have hR : isAlive (evolve (2^(k - 1)) ((node R4 R5 R7 R8).toGrid (0, 0)))
        (p.1 - ((2^k : Int) + (2^(k - 1) : Int)), p.2 - (2^(k - 1) : Int))
      = isAlive (evolve (2^(k - 1))
          (shift ((2^k : Int) + (2^(k - 1) : Int), (2^(k - 1) : Int))
            ((node R4 R5 R7 R8).toGrid (0, 0)))) p := by
    rw [← evolve_shift, isAlive_shift]
  rw [hR]
  apply evolve_box_agree_local
  intro q hq
  rw [isAlive_shift]
  exact p4_sw_overlap_wall k hk1
    nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
    sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
    R4 R5 R7 R8 hR4 hR5 hR7 hR8
    hn1_l hn2_l hn3_l hn4_l hn5_l hn7_l hn8_l
    hn1_w hn2_w hn3_w hn4_w hn5_w hn7_w hn8_w
    hR4_l hR5_l hR7_l hR8_l
    hcc4 hcc5 hcc7 hcc8 p hp q hq


/-- **SW-quadrant supercell agreement (PROUVÉ — miroir de
    `p4_ne_supercell_agree`, NW-SE reflection).**
    Le double half-step du parent coïncide, au point recentré SW, avec le
    half-step du supercell wave-1 `node R4 R5 R7 R8`. Preuve : fold LHS
    `evolve 2^k = evolve 2^(k-1) ∘ evolve 2^(k-1)` (`evolve_half_step`,
    sorry-free) puis délégation intégrale à `p4_sw_g3_bridge` (qui décharge
    l'outer-locality sur le mur `p4_sw_overlap_wall`, désormais PROUVÉ).

    L'énoncé est *renforcé* comme le mur : fenêtre `hp` (forme exacte des
    bornes du `p4_sw_shift_lemma`, `hsup.2` dans l'arm) + hypothèses
    structurelles `hn*` (niveau/wf des nœuds de recombinaison). Le point
    d'évaluation est l'analogue SW de la forme NE : SW est à l'offset outer
    `(2^k + 2^k, 2^k)`, d'où `(p.1 - (2^k + 2^k) + 2^(k-1),
    p.2 - 2^k + 2^(k-1))`. Ferme le sorry SW résiduel de #6724 (S3). -/
private theorem p4_sw_supercell_agree
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R4 R5 R7 R8 : MacroCell)
    (hR4 : R4 = hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
    (hR5 : R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
    (hR7 : R7 = hashlifeResultAux (k + 1) (node sw_nw sw_ne sw_sw sw_se))
    (hR8 : R8 = hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
    (hn1_l : (node nw_nw nw_ne nw_sw nw_se).level = k + 1)
    (hn2_l : (node nw_ne ne_nw nw_se ne_sw).level = k + 1)
    (hn3_l : (node ne_nw ne_ne ne_sw ne_se).level = k + 1)
    (hn4_l : (node nw_sw nw_se sw_nw sw_ne).level = k + 1)
    (hn5_l : (node nw_se ne_sw sw_ne se_nw).level = k + 1)
    (hn7_l : (node sw_nw sw_ne sw_sw sw_se).level = k + 1)
    (hn8_l : (node sw_ne se_nw sw_se se_sw).level = k + 1)
    (hn1_w : (node nw_nw nw_ne nw_sw nw_se).wf = true)
    (hn2_w : (node nw_ne ne_nw nw_se ne_sw).wf = true)
    (hn3_w : (node ne_nw ne_ne ne_sw ne_se).wf = true)
    (hn4_w : (node nw_sw nw_se sw_nw sw_ne).wf = true)
    (hn5_w : (node nw_se ne_sw sw_ne se_nw).wf = true)
    (hn7_w : (node sw_nw sw_ne sw_sw sw_se).wf = true)
    (hn8_w : (node sw_ne se_nw sw_se se_sw).wf = true)
    (hR4_l : R4.level = k) (hR5_l : R5.level = k)
    (hR7_l : R7.level = k) (hR8_l : R8.level = k)
    (hcc4 : centralCorrect (node nw_sw nw_se sw_nw sw_ne) (k - 1))
    (hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1))
    (hcc7 : centralCorrect (node sw_nw sw_ne sw_sw sw_se) (k - 1))
    (hcc8 : centralCorrect (node sw_ne se_nw sw_se se_sw) (k - 1))
    (p : Int × Int)
    (hp : ((2^k + (2^k : Int))) ≤ p.1 ∧
          p.1 < ((2^k + (2^k : Int))) + 2^((k - 1) + 1) ∧
          (2^k : Int) ≤ p.2 ∧ p.2 < (2^k : Int) + 2^((k - 1) + 1)) :
    isAlive (evolve (2^(k - 1)) (evolve (2^(k - 1))
        ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
          (0, 0)))) p
      = isAlive (evolve (2^(k - 1)) ((node R4 R5 R7 R8).toGrid (0, 0)))
          (p.1 - ((2^k + (2^k : Int)) : Int) + (2^(k - 1) : Int),
           p.2 - (2^k : Int) + (2^(k - 1) : Int)) := by
  rw [← evolve_half_step k hk1]
  exact p4_sw_g3_bridge k hk1
    nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
    sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
    R4 R5 R7 R8 hR4 hR5 hR7 hR8
    hn1_l hn2_l hn3_l hn4_l hn5_l hn7_l hn8_l
    hn1_w hn2_w hn3_w hn4_w hn5_w hn7_w hn8_w
    hR4_l hR5_l hR7_l hR8_l
    hcc4 hcc5 hcc7 hcc8 p hp


set_option maxHeartbeats 4000000 in
/-- **c.NNNN §3 — SW membership arm (opaque-binder, sorry-free wiring — c.NNNN
    mirror of NE arm L3409, NW-SE reflection).**
    Discharges the SW quadrant of `p4_succ_membership` over OPAQUE wave-1
    results `R4 R5 R7 R8` (SW supercell wave-1 sub-cells), so this declaration
    gets a fresh heartbeat budget (4M, same as the NE arm precedent). The `p4_succ_membership` call site
    merely *applies* this arm with `R_j := hashlifeResultAux (k+1) n_j`
    (pure substitution, no whnf). `p4_sw_supercell_agree` is now fully
    proven (windowed SW wall, mirror of the NE precedent) — this arm is
    sorry-free at the axiom level.

    Chain: `p4_sw_shift_lemma.mp` (supercell isAlive at `p'` + window bounds
    at SW offset `(2^k + 2^(k-1), 2^k)`) → `mem_restrictGridTo` →
    `isAlive_true_iff_mem` + `evolve_half_step` + `p4_sw_supercell_agree`
    fold the membership into `hsup.1`; the four coordinate bounds discharge
    from the shift window (`2^((k-1)+1) = 2^k ≤ 2^(k+1)`) by omega.

    Same `hout_nw` opaque-binder pattern as the NE arm: the SW outer offset
    `(2^k + 2^k, 2^k)` is anchored on `2^out_nw.level` (the outer NW
    supercell's level — the same reference for all four quadrants). -/
theorem p4_sw_membership_arm
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R4 R5 R7 R8 : MacroCell)
    (hR4 : R4 = hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
    (hR5 : R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
    (hR7 : R7 = hashlifeResultAux (k + 1) (node sw_nw sw_ne sw_sw sw_se))
    (hR8 : R8 = hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
    (hn1_l : (node nw_nw nw_ne nw_sw nw_se).level = k + 1)
    (hn2_l : (node nw_ne ne_nw nw_se ne_sw).level = k + 1)
    (hn3_l : (node ne_nw ne_ne ne_sw ne_se).level = k + 1)
    (hn4_l : (node nw_sw nw_se sw_nw sw_ne).level = k + 1)
    (hn5_l : (node nw_se ne_sw sw_ne se_nw).level = k + 1)
    (hn7_l : (node sw_nw sw_ne sw_sw sw_se).level = k + 1)
    (hn8_l : (node sw_ne se_nw sw_se se_sw).level = k + 1)
    (hn1_w : (node nw_nw nw_ne nw_sw nw_se).wf = true)
    (hn2_w : (node nw_ne ne_nw nw_se ne_sw).wf = true)
    (hn3_w : (node ne_nw ne_ne ne_sw ne_se).wf = true)
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
  -- hsup.2 : (2^k + 2^k) ≤ p.1 ∧ p.1 < (2^k + 2^k) + 2^((k-1)+1) ∧
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
          hn1_l hn2_l hn3_l hn4_l hn5_l hn7_l hn8_l
          hn1_w hn2_w hn3_w hn4_w hn5_w hn7_w hn8_w
          hR4_l hR5_l hR7_l hR8_l hcc4 hcc5 hcc7 hcc8 p hsup.2]
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


set_option maxHeartbeats 1000000 in
/-- **SW membership arm, reciprocal direction (mpr assembly — mirror of
    `p4_sw_membership_arm`, NW-SE reflection of the NE rev arm).**
    `p4_sw_supercell_agree` is now fully proven (windowed SW wall, mirror
    of the NE precedent) — this arm is sorry-free at the axiom level. -/
theorem p4_sw_membership_arm_rev
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R4 R5 R7 R8 : MacroCell)
    (hR4 : R4 = hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
    (hR5 : R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
    (hR7 : R7 = hashlifeResultAux (k + 1) (node sw_nw sw_ne sw_sw sw_se))
    (hR8 : R8 = hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
    (hn1_l : (node nw_nw nw_ne nw_sw nw_se).level = k + 1)
    (hn2_l : (node nw_ne ne_nw nw_se ne_sw).level = k + 1)
    (hn3_l : (node ne_nw ne_ne ne_sw ne_se).level = k + 1)
    (hn4_l : (node nw_sw nw_se sw_nw sw_ne).level = k + 1)
    (hn5_l : (node nw_se ne_sw sw_ne se_nw).level = k + 1)
    (hn7_l : (node sw_nw sw_ne sw_sw sw_se).level = k + 1)
    (hn8_l : (node sw_ne se_nw sw_se se_sw).level = k + 1)
    (hn1_w : (node nw_nw nw_ne nw_sw nw_se).wf = true)
    (hn2_w : (node nw_ne ne_nw nw_se ne_sw).wf = true)
    (hn3_w : (node ne_nw ne_ne ne_sw ne_se).wf = true)
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
        hn1_l hn2_l hn3_l hn4_l hn5_l hn7_l hn8_l
        hn1_w hn2_w hn3_w hn4_w hn5_w hn7_w hn8_w
        hR4_l hR5_l hR7_l hR8_l hcc4 hcc5 hcc7 hcc8 p hw]
  rw [← evolve_half_step k hk1]
  rw [isAlive_true_iff_mem_local]
  exact hmem


end Life
end Conway
