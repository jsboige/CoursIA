/-  # HashlifeCorrectness.Walls.NE

P4 NE quadrant: overlap wall + G3 bridge + supercell agreement + shift lemma +
membership arm (.mp) and its reciprocal (.mpr). Mirror of NW.
-/

import Conway.Life.HashlifeCorrectness.Foundation

namespace Conway
namespace Life

open MacroCell

/-- **Mur de chevauchement NE (P4 (a), miroir de `p4_nw_overlap_wall`).**
    Même géométrie que le mur NW — fenêtre centrale, boîte Chebyshev de rayon
    `2^(k-1)`, hypothèses structurelles `hn*` — mais pour le supercell NE
    `node R2 R3 R5 R6` ancré à `(2^(k-1), 2^k + 2^(k-1))` dans le parent.
    Les quatre quadrants du supercell correspondent aux recombinaisons
    `n2` (NO, translatée `(0, 2^k)`), `n3` (NE, `(0, 2·2^k)` — l'enfant NE
    du parent), `n5` (SO, `(2^k, 2^k)` — LE MÊME nœud centre que le mur NW,
    `p4_nw_parent_agree_n5` est réutilisé tel quel) et `n6` (SE,
    `(2^k, 2·2^k)`). L'ensemble d'hypothèses structurelles s'élargit à
    `{n1..n7}` : `n1`/`n4`/`n7` n'ont pas de `hcc` (purement structurels,
    pour les exclusions de bornes des lemmes d'accord parent). -/
private theorem p4_ne_overlap_wall
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R2 R3 R5 R6 : MacroCell)
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
    (hR2_l : R2.level = k) (hR3_l : R3.level = k)
    (hR5_l : R5.level = k) (hR6_l : R6.level = k)
    (hcc2 : centralCorrect (node nw_ne ne_nw nw_se ne_sw) (k - 1))
    (hcc3 : centralCorrect (node ne_nw ne_ne ne_sw ne_se) (k - 1))
    (hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1))
    (hcc6 : centralCorrect (node ne_sw ne_se se_nw se_ne) (k - 1))
    (p : Int × Int)
    (hp : (2^k : Int) ≤ p.1 ∧ p.1 < (2^k : Int) + 2^((k - 1) + 1) ∧
          ((2^k + (2^k : Int))) ≤ p.2 ∧
          p.2 < ((2^k + (2^k : Int))) + 2^((k - 1) + 1)) :
    ∀ q, chebDist p q ≤ 2^(k - 1) →
      isAlive (evolve (2^(k - 1))
          ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
                 (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
            (0, 0))) q
        = isAlive ((node R2 R3 R5 R6).toGrid (0, 0))
            (q.1 - (2^(k - 1) : Int), q.2 - ((2^k : Int) + (2^(k - 1) : Int))) := by
  -- Assemblage miroir du mur NW : fenêtre → quadrant → localité Chebyshev
  -- (`evolve_box_agree_local`) sur le nœud de recombinaison du quadrant →
  -- caractérisation `p4_nw_rside_char_*` (paramétrique) du supernœud résultat.
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
  by_cases hcx1 : q.1 - (2 ^ (k - 1) : Int) < (2 ^ k : Int) <;>
    by_cases hcx2 : q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) < (2 ^ k : Int)
  · -- Quadrant NO du supercell : `n2`, translaté `(0, 2^k)`.
    have hbox : ∀ r, chebDist q r ≤ 2 ^ (k - 1) →
        isAlive ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
            (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid (0, 0)) r
          = isAlive (shift ((0 : Int), (2 ^ k : Int))
              ((node nw_ne ne_nw nw_se ne_sw).toGrid (0, 0))) r := by
      intro r hr
      obtain ⟨hr1, hr2⟩ := coord_bound_of_chebDist_le q r _ hr
      rw [isAlive_shift, ← p4_isAlive_toGrid_shift]
      exact p4_nw_parent_agree_n2 k nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se hn1_l hn1_w hn2_l hn2_w r
        ⟨by omega, by omega, by omega, by omega⟩
    have hL := evolve_box_agree_local (2 ^ (k - 1)) _ _ q hbox
    rw [hL, ← evolve_shift, isAlive_shift]
    have hx' : 0 ≤ q.1 - (2 ^ (k - 1) : Int) ∧ q.1 - (2 ^ (k - 1) : Int) < (2 ^ k : Int) ∧
        0 ≤ q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) ∧
        q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) < (2 ^ k : Int) :=
      ⟨by omega, by omega, by omega, by omega⟩
    rw [p4_nw_rside_char_nw k hk1 _ _ _ _ R2 R3 R5 R6 hR2 hR3 hR5 hR6 hR2_l
        hcc2 hcc3 hcc5 hcc6
        (q.1 - (2 ^ (k - 1) : Int), q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int))) hx']
    congr 1
    ext <;> (try dsimp only) <;> omega
  · -- Quadrant NE du supercell : `n3` (l'enfant NE du parent), translaté `(0, 2·2^k)`.
    have hbox : ∀ r, chebDist q r ≤ 2 ^ (k - 1) →
        isAlive ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
            (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid (0, 0)) r
          = isAlive (shift ((0 : Int), (2 ^ k : Int) + (2 ^ k : Int))
              ((node ne_nw ne_ne ne_sw ne_se).toGrid (0, 0))) r := by
      intro r hr
      obtain ⟨hr1, hr2⟩ := coord_bound_of_chebDist_le q r _ hr
      rw [isAlive_shift, ← p4_isAlive_toGrid_shift]
      exact p4_ne_parent_agree_n3 k nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se hn1_l hn1_w r
        ⟨by omega, by omega, by omega, by omega⟩
    have hL := evolve_box_agree_local (2 ^ (k - 1)) _ _ q hbox
    rw [hL, ← evolve_shift, isAlive_shift]
    have hx' : 0 ≤ q.1 - (2 ^ (k - 1) : Int) ∧ q.1 - (2 ^ (k - 1) : Int) < (2 ^ k : Int) ∧
        (2 ^ k : Int) ≤ q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) ∧
        q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) < (2 ^ k : Int) + (2 ^ k : Int) :=
      ⟨by omega, by omega, by omega, by omega⟩
    rw [p4_nw_rside_char_ne k hk1 _ _ _ _ R2 R3 R5 R6 hR2 hR3 hR5 hR6 hR2_l
        hcc2 hcc3 hcc5 hcc6
        (q.1 - (2 ^ (k - 1) : Int), q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int))) hx']
    congr 1
    ext <;> (try dsimp only) <;> omega
  · -- Quadrant SO du supercell : `n5` (nœud centre, PARTAGÉ avec le mur NW),
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
    have hx' : (2 ^ k : Int) ≤ q.1 - (2 ^ (k - 1) : Int) ∧
        q.1 - (2 ^ (k - 1) : Int) < (2 ^ k : Int) + (2 ^ k : Int) ∧
        0 ≤ q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) ∧
        q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) < (2 ^ k : Int) :=
      ⟨by omega, by omega, by omega, by omega⟩
    rw [p4_nw_rside_char_sw k hk1 _ _ _ _ R2 R3 R5 R6 hR2 hR3 hR5 hR6 hR2_l
        hcc2 hcc3 hcc5 hcc6
        (q.1 - (2 ^ (k - 1) : Int), q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int))) hx']
    congr 1
    ext <;> (try dsimp only) <;> omega
  · -- Quadrant SE du supercell : `n6`, translaté `(2^k, 2·2^k)`.
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
    have hx' : (2 ^ k : Int) ≤ q.1 - (2 ^ (k - 1) : Int) ∧
        q.1 - (2 ^ (k - 1) : Int) < (2 ^ k : Int) + (2 ^ k : Int) ∧
        (2 ^ k : Int) ≤ q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) ∧
        q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int)) < (2 ^ k : Int) + (2 ^ k : Int) :=
      ⟨by omega, by omega, by omega, by omega⟩
    rw [p4_nw_rside_char_se k hk1 _ _ _ _ R2 R3 R5 R6 hR2 hR3 hR5 hR6 hR2_l
        hcc2 hcc3 hcc5 hcc6
        (q.1 - (2 ^ (k - 1) : Int), q.2 - ((2 ^ k : Int) + (2 ^ (k - 1) : Int))) hx']
    congr 1
    ext <;> (try dsimp only) <;> omega

/-- **Bridge G3 NE (miroir de `p4_nw_g3_bridge`).** Décharge la moitié (b)
    outer-locality : le double half-step du parent, évalué au point recentré du
    supercell NE, se transporte par `evolve_shift` + `evolve_box_agree_local`
    sur le mur `p4_ne_overlap_wall`. Le vecteur de shift est
    `(2^(k-1), 2^k + 2^(k-1))` (l'ancre du supercell NE dans le parent). -/
private theorem p4_ne_g3_bridge
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R2 R3 R5 R6 : MacroCell)
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
    (hR2_l : R2.level = k) (hR3_l : R3.level = k)
    (hR5_l : R5.level = k) (hR6_l : R6.level = k)
    (hcc2 : centralCorrect (node nw_ne ne_nw nw_se ne_sw) (k - 1))
    (hcc3 : centralCorrect (node ne_nw ne_ne ne_sw ne_se) (k - 1))
    (hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1))
    (hcc6 : centralCorrect (node ne_sw ne_se se_nw se_ne) (k - 1))
    (p : Int × Int)
    (hp : (2^k : Int) ≤ p.1 ∧ p.1 < (2^k : Int) + 2^((k - 1) + 1) ∧
          ((2^k + (2^k : Int))) ≤ p.2 ∧
          p.2 < ((2^k + (2^k : Int))) + 2^((k - 1) + 1)) :
    isAlive (evolve (2^k)
        ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
          (0, 0))) p
      = isAlive (evolve (2^(k - 1)) ((node R2 R3 R5 R6).toGrid (0, 0)))
          (p.1 - (2^k : Int) + (2^(k - 1) : Int),
           p.2 - ((2^k + (2^k : Int)) : Int) + (2^(k - 1) : Int)) := by
  rw [evolve_half_step k hk1]
  have h2k : (2^k : Int) = (2^(k - 1) : Int) + (2^(k - 1) : Int) := by
    have hn : 2^k = 2^(k - 1) + 2^(k - 1) := by
      set m := k - 1 with hm
      have hkm : k = m + 1 := by omega
      rw [hkm, Nat.pow_succ]; ring
    exact_mod_cast hn
  have hpt1 : p.1 - (2^k : Int) + (2^(k - 1) : Int) = p.1 - (2^(k - 1) : Int) := by omega
  have hpt2 : p.2 - ((2^k + (2^k : Int)) : Int) + (2^(k - 1) : Int)
      = p.2 - ((2^k : Int) + (2^(k - 1) : Int)) := by omega
  rw [hpt1, hpt2]
  have hR : isAlive (evolve (2^(k - 1)) ((node R2 R3 R5 R6).toGrid (0, 0)))
        (p.1 - (2^(k - 1) : Int), p.2 - ((2^k : Int) + (2^(k - 1) : Int)))
      = isAlive (evolve (2^(k - 1))
          (shift ((2^(k - 1) : Int), (2^k : Int) + (2^(k - 1) : Int))
            ((node R2 R3 R5 R6).toGrid (0, 0)))) p := by
    rw [← evolve_shift, isAlive_shift]
  rw [hR]
  apply evolve_box_agree_local
  intro q hq
  rw [isAlive_shift]
  exact p4_ne_overlap_wall k hk1
    nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
    sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
    R2 R3 R5 R6 hR2 hR3 hR5 hR6
    hn1_l hn2_l hn3_l hn4_l hn5_l hn6_l hn7_l
    hn1_w hn2_w hn3_w hn4_w hn5_w hn6_w hn7_w
    hR2_l hR3_l hR5_l hR6_l
    hcc2 hcc3 hcc5 hcc6 p hp q hq

/-- **NE super-cell agreement (P4, G3 pour le quadrant NE) — PROUVÉ (miroir c.94).**
    Symétrique de `p4_nw_supercell_agree` pour le supercell NE
    `node R2 R3 R5 R6` (recombinaisons `n2 n3 n5 n6`, chacune de niveau `k+1`,
    G2 au niveau `k-1` via `ih`). Compare le double half-step du parent à `p`
    contre le résultat wave-0 du supercell NE au point recentré
    `p - (2^k, 2·2^k) + (2^(k-1), 2^(k-1))`.

    **Renforcement d'énoncé (verdict prover BG DEMO — la forme libre était
    FAUSSE)** : comme pour le mur NW (c.91-c.93), le quantificateur `p` libre
    rendait l'énoncé réfutable (le point d'évaluation n'était pas contraint à
    la fenêtre que le supercell représente). L'énoncé porte désormais :
    (1) la fenêtre `hp` — la forme EXACTE des bornes produites par
    `p4_ne_shift_lemma` (`hsup.2` dans `p4_ne_membership_arm`, zéro friction
    de câblage) ; (2) les hypothèses structurelles `hn1..hn7` (niveau `k+1` +
    `wf` des recombinaisons ET des enfants du parent touchés par les
    exclusions de bornes — le mur NE en requiert 7 là où le mur NW en
    requiert 4, car ses quadrants chevauchent les enfants NE/SE/SO du parent).
    La preuve est le miroir exact de la chaîne NW :
    `← evolve_half_step` → `p4_ne_g3_bridge` → `p4_ne_overlap_wall`. -/
private theorem p4_ne_supercell_agree
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R2 R3 R5 R6 : MacroCell)
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
    (hR2_l : R2.level = k) (hR3_l : R3.level = k)
    (hR5_l : R5.level = k) (hR6_l : R6.level = k)
    (hcc2 : centralCorrect (node nw_ne ne_nw nw_se ne_sw) (k - 1))
    (hcc3 : centralCorrect (node ne_nw ne_ne ne_sw ne_se) (k - 1))
    (hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1))
    (hcc6 : centralCorrect (node ne_sw ne_se se_nw se_ne) (k - 1))
    (p : Int × Int)
    (hp : (2^k : Int) ≤ p.1 ∧ p.1 < (2^k : Int) + 2^((k - 1) + 1) ∧
          ((2^k + (2^k : Int))) ≤ p.2 ∧
          p.2 < ((2^k + (2^k : Int))) + 2^((k - 1) + 1)) :
    isAlive (evolve (2^(k - 1)) (evolve (2^(k - 1))
        ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
          (0, 0)))) p
      = isAlive (evolve (2^(k - 1)) ((node R2 R3 R5 R6).toGrid (0, 0)))
          (p.1 - (2^k : Int) + (2^(k - 1) : Int),
           p.2 - ((2^k + (2^k : Int)) : Int) + (2^(k - 1) : Int)) := by
  rw [← evolve_half_step k hk1]
  exact p4_ne_g3_bridge k hk1
    nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
    sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
    R2 R3 R5 R6 hR2 hR3 hR5 hR6
    hn1_l hn2_l hn3_l hn4_l hn5_l hn6_l hn7_l
    hn1_w hn2_w hn3_w hn4_w hn5_w hn6_w hn7_w
    hR2_l hR3_l hR5_l hR6_l
    hcc2 hcc3 hcc5 hcc6 p hp

/-- **P4.4 NE-quadrant shift lemma (c.8122, defensive factorization).**
    Caractérise l'appartenance pointwise `p ∈ (hashlifeResultAux (k+1) q_ne).toGrid (2^k, 2^k + 2^k)`
    du quadrant NE (offset `(2^k, 2^k + 2^k)` après `push_cast` au call-site
    L3711-3713 — `2^k + 2^(k-1) = 2^k` par simplification `omega`) en une
    conjonction `isAlive ... ∧ bounds`. La super-cellule opaque `q_ne` =
    `hashlifeResultAux (k+1) (node ...)` (level `k`) passe par
    `p4_wave2_ih_step` (ih sur la super-cellule) puis
    `centralCorrect_mem_shift` pour réancrer l'offset `(2^k, 2^k + 2^k)`.

    NOTE (c.8122) — le quadrant NE d'un grid `2^(k+2) × 2^(k+2)` centré
    sur `(2^k, 2^k)` occupe `[2^k, 3·2^k) × [2^k, 3·2^k)`. La `toGrid` du
    quadrant NE a offset `(2^k, 2^k + 2^(k-1))` au call-site (avant
    `push_cast`), qui se réduit à `(2^k, 2^k)` par `omega`. Le lemme était
    jamais consommé avant ce grain ; la correction est purement locale.
    Pattern cohérent avec `p4_nw_shift_lemma` (c.488) — seul l'offset `(a, b)`
    change. Sorry-free. -/
private theorem p4_ne_shift_lemma
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
          ((2^k : Int), (2^k + (2^k : Int))) ↔
      isAlive (evolve (2^(k - 1)) ((node r1 r2 r4 r5).toGrid (0, 0)))
        (p.1 - (2^k : Int) + (2^(k - 1) : Int),
         p.2 - ((2^k + (2^k : Int))) + (2^(k - 1) : Int)) = true ∧
      (2^k : Int) ≤ p.1 ∧ p.1 < (2^k : Int) + 2^((k - 1) + 1) ∧
      ((2^k + (2^k : Int))) ≤ p.2 ∧
        p.2 < ((2^k + (2^k : Int))) + 2^((k - 1) + 1) := by
  have hcc : centralCorrect (node r1 r2 r4 r5) (k - 1) :=
    p4_wave2_ih_step k hk1 r1 r2 r4 r5
      hr1_l hr2_l hr4_l hr5_l hr1_w hr2_w hr4_w hr5_w ih
  exact centralCorrect_mem_shift (node r1 r2 r4 r5) (k - 1)
    (2^k) (2^k + (2^k : Int)) p hcc

set_option maxHeartbeats 4000000 in
/-- **NE membership arm (opaque-binder, sorry-free wiring — c.8122 mirror of NW).**
    Discharges the NE quadrant of `p4_succ_membership` over OPAQUE wave-1
    results `R2 R3 R5 R6` (NE supercell wave-1 sub-cells), so this declaration
    gets a fresh 200000-heartbeat budget. The `p4_succ_membership` call site
    merely *applies* this arm with `R_j := hashlifeResultAux (k+1) n_j`
    (pure substitution, no whnf). `p4_ne_supercell_agree` is now PROVED
    (strengthened with the `hp` window + `hn1..hn7` structural hypotheses,
    mirror of the NW chain); the arm feeds it `hsup.2` — the shift-lemma
    window — as `hp`, zero wiring friction.

    Chain: `p4_ne_shift_lemma.mp` (supercell isAlive at `p'` + window bounds
    at NE offset `(2^k, 2^k + 2^(k-1))`) → `mem_restrictGridTo` →
    `isAlive_true_iff_mem` + `evolve_half_step` + `p4_ne_supercell_agree`
    fold the membership into `hsup.1`; the four coordinate bounds discharge
    from the shift window (`2^((k-1)+1) = 2^k ≤ 2^(k+1)`) by omega. -/
private theorem p4_ne_membership_arm
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
    -- Geometric offset: NE supercell `(node R2 R3 R5 R6)` lives at outer
    -- offset `(2^k, 2^k + 2^out_nw.level)` per `mem_toGrid_node`, where
    -- `out_nw` is the OUTER NW quadrant (after `hashlifeResultAux_succ_node`,
    -- it has level k, but its definition keeps it opaque). The arm takes
    -- `hout_nw_l : out_nw.level = k` and bridges `2^out_nw.level = 2^k` via
    -- `congrArg` through `HPow.hPow` (Lean 4's `2^x` is `HPow.hPow 2 x`, not
    -- a projection — plain `rw` cannot rewrite under it). Cf. c.8122.
    (hout_nw : MacroCell)
    (hout_nw_l : hout_nw.level = k)
    (hne : p ∈ (hashlifeResultAux (k + 1) (node R2 R3 R5 R6)).toGrid
            ((2^k : Int), (2^k + (2^hout_nw.level : Int)))) :
    p ∈ restrictGridTo (evolve (2^k)
        ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
          (0, 0)))
        (2^k : Int) (2^(k+1)) := by
  -- Fuel-align (k+1) → (k-1)+2 on the OPAQUE-node membership, then bridge the
  -- NE offset `2^hout_nw.level` to literal `2^k` via `congrArg`. The bridge
  -- consumes `hout_nw_l : hout_nw.level = k`. Then the NE shift lemma's `.mp`
  -- is whnf-clean over opaque `R_j` (fresh budget).
  rw [show (k + 1) = (k - 1) + 2 from by omega] at hne
  -- Inline bridge (no residual context equations: leftover `hpow`/`hbridge`
  -- hypotheses with `2^hout_nw.level` atoms poison every downstream `omega`
  -- preprocessing pass — cumulative heartbeat exhaustion, cf. build c.8122-NE).
  rw [show (2^k + (2^hout_nw.level : Int)) = (2^k + (2^k : Int)) from by
    rw [congrArg (fun n => (2^n : Int)) hout_nw_l]] at hne
  have hsup := (p4_ne_shift_lemma k hk1 R2 R3 R5 R6
      hR2_l hR3_l hR5_l hR6_l hR2_w hR3_w hR5_w hR6_w ih p).mp hne
  -- hsup.1 : isAlive (evolve 2^(k-1) ((node R2 R3 R5 R6).toGrid 0)) p' = true
  -- hsup.2 : 2^k ≤ p.1 ∧ p.1 < 2^k + 2^((k-1)+1) ∧
  --          (2^k + 2^(k-1)) ≤ p.2 ∧ p.2 < (2^k + 2^(k-1)) + 2^((k-1)+1)
  rw [mem_restrictGridTo]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- membership: fold `evolve 2^k` via half-step + NE supercell agreement into hsup.1
    rw [← isAlive_true_iff_mem_local]
    rw [evolve_half_step k hk1]
    -- The 4 wave-1 sub-cells of the NE supercell are n2/n3/n5/n6 (level k+1,
    -- G2 at level k-1). Each `centralCorrect n_j (k-1)` is the IH projection
    -- (j = k-1 < k by hk1, level j+2 = k+1 matches).
    have hcc2 : centralCorrect (node nw_ne ne_nw nw_se ne_sw) (k - 1) :=
      ih _ (k - 1) (by omega) hn2_w (by rw [hn2_l]; omega)
    have hcc3 : centralCorrect (node ne_nw ne_ne ne_sw ne_se) (k - 1) :=
      ih _ (k - 1) (by omega) hn3_w (by rw [hn3_l]; omega)
    have hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1) :=
      ih _ (k - 1) (by omega) hn5_w (by rw [hn5_l]; omega)
    have hcc6 : centralCorrect (node ne_sw ne_se se_nw se_ne) (k - 1) :=
      ih _ (k - 1) (by omega) hn6_w (by rw [hn6_l]; omega)
    rw [p4_ne_supercell_agree k hk1
          nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
          sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
          R2 R3 R5 R6 hR2 hR3 hR5 hR6
          hn1_l hn2_l hn3_l hn4_l hn5_l hn6_l hn7_l
          hn1_w hn2_w hn3_w hn4_w hn5_w hn6_w hn7_w
          hR2_l hR3_l hR5_l hR6_l hcc2 hcc3 hcc5 hcc6 p hsup.2]
    exact hsup.1
  · -- 2^k ≤ p.1
    exact hsup.2.1
  · -- p.1 < 2^k + 2^(k+1)
    have hb := hsup.2.2.1
    have he : (k - 1) + 1 = k := by omega
    rw [he] at hb
    have hbridge : ((2 ^ (k + 1) : Nat) : Int) = 2 ^ k + 2 ^ k := by
      push_cast; rw [pow_succ]; ring
    have hpos : (0 : Int) < 2 ^ k := pow_pos (by norm_num) k
    rw [hbridge]
    omega
  · -- 2^k ≤ p.2 (we have hsup.2.2.2.1 : (2^k + 2^k) ≤ p.2, which is strictly stronger)
    exact le_trans (by norm_num : (2^k : Int) ≤ 2^k + 2^k) hsup.2.2.2.1
  · -- p.2 < 2^k + 2^k + 2^k (= 2^k + 2^(k+1) = 3·2^k)
    have hb := hsup.2.2.2.2
    have he : (k - 1) + 1 = k := by omega
    rw [he] at hb
    have hbridge : ((2 ^ (k + 1) : Nat) : Int) = 2 ^ k + 2 ^ k := by
      push_cast; rw [pow_succ]; ring
    have hpos : (0 : Int) < 2 ^ k := pow_pos (by norm_num) k
    rw [hbridge]
    omega

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

end Life
end Conway
