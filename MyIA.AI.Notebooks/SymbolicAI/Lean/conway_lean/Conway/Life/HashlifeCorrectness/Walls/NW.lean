/-  # HashlifeCorrectness.Walls.NW

P4 (a) overlap wall + counterexamples + G3 bridge + supercell agreement +
membership arm (.mp) and its reciprocal (.mpr). Contains the original crux (a).
-/

import Conway.Life.HashlifeCorrectness.Foundation

namespace Conway
namespace Life

open MacroCell

/-! ## P4 (a) — the named overlap wall

The bridge `p4_nw_g3_bridge` decomposes (c.764) into a sorry-free **(b) outer-
locality** transport (proven in the bridge via `evolve_shift` + `evolve_cone_agree`)
and the residual **(a) inner-agreement** — the double-nine overlap wall. This is
that wall, extracted as a NAMED lemma so the obstruction has a single, compiler-
checked statement (the bridge's `exact p4_nw_overlap_wall …` proves the statement
is strong enough for the (b) reduction; it does NOT prove the wall holds). -/

/-- **crux (a) inner-agreement — the named overlap wall (#6724).** The residual
    obstruction once (b) outer-locality is discharged: the `evolve 2^(k-1)`d parent
    grid agrees, pointwise on `lightCone p (2^k)`, with the wave-1 supercell
    `(node R1 R2 R4 R5)` evaluated at the supercell-local point
    `r - (2^(k-1), 2^(k-1))`. This is the **double-nine overlap realignment**
    (see `p4_nw_g3_bridge` docstring): reconciling the parent's four
    NON-overlapping quadrants against the wave-1 `R2`/`R4`/`R5` recombinations that
    STRADDLE the NW/NE, NW/SW and central boundaries. `centralCorrect` (the
    `hcc_j`) gives quadrant-centre correctness; this lemma is the lift from those
    centres to the full cone.

    **Cycle c.8124 obstruction characterization (per ai-01 DM
    `msg-20260725T165407`: option D = "caractériser l'obstruction" — what term
    fails to reduce, what tactic blocks, where whnf explodes).** This is the
    load-bearing investigation; the bridge's `exact p4_nw_overlap_wall …` proves
    the statement is well-formed, but the wall does NOT resolve.

    **Map of the attempted attack (c.8124 probe, just before this commit).**
    The membership route:
      1. Decompose RHS via `p4_nw_offset_decomp` L2886 → 4 disjuncts (R1.toGrid
         (0,0) / R2.toGrid (0,2^k) / R4.toGrid (2^k,0) / R5.toGrid (2^k,2^k)).
      2. Each R_j folds to `evolve (2^(k-1)) n_j.toGrid (0,0)` via
         `centralCorrect_mem_shift` L2443 on `hR_j : R_j = hashlifeResultAux (k+1) n_j`.
      3. Re-anchor RHS to LHS via `evolve_shift` (#8797, sorry-free) +
         `mem_toGrid_shift` L1437 + `toGrid_shift_between` L1453.
      4. Decompose LHS via `mem_toGrid_node` L1478 on parent →
         (n1.toGrid (0,0)) ∨ (n3.toGrid (0,2^k)) ∨ (n7.toGrid (2^k,0)) ∨
         (n9.toGrid (2^k,2^k)) (the parent's 4 NON-overlapping quadrants).
      5. Equate the two tilings.

    **The obstruction, in three pieces:**

    *A. RHS expansion needs FOUR R_j-membership facts, one per R_j quadrant,
    each using `centralCorrect_mem_shift` on its own `hcc_j`. But `hcc_3` and
    `hcc_7` and `hcc_9` (which would match R2 and R4 and R5 to the **parent's**
    quadrants, not the wave-1 input's quadrants) are NOT hypotheses here —
    `p4_nw_overlap_wall` only has `hcc_1/hcc_2/hcc_4/hcc_5` because R1/R2/R4/R5
    are the wave-1 results of n1/n2/n4/n5, not n3/n7/n9. The bridge assumes the
    parent's grid is read off `n1/n3/n7/n9` (the clean quadrants), but the wave-1
    result tiles the central region with `R1/R2/R4/R5` (the overlapping
    recombinations). The two tilings DO agree on the central window (by the
    geometric identity the wall asserts), but proving this requires either:
      (α) decomposing the LHS grid into the overlapping-recombination grid via
          `p4_double_nine_shape` style gymnastics (it doesn't — `evolve
          (2^(k-1)) parent.toGrid` doesn't remember the wave-1 sub-cells), OR
      (β) re-deriving the wave-1 inputs from `n1/n3/n7/n9` to get the missing
          `hcc_*` for the central quadrant. Neither path is structural.

    *B. The point `r - (2^(k-1), 2^(k-1))` evaluated against `(node R1 R2 R4
    R5).toGrid (0,0)` lands in **shifted** quadrants, not the canonical
    `(0,0)`/`(0,2^k)`/`(2^k,0)`/`(2^k,2^k)` offsets. The shift is precisely
    `(2^(k-1), 2^(k-1))` — the canonical `centralCorrect` re-anchoring. So each
    R_j-membership needs `toGrid_shift_between` (already available, sorry-free
    L1453) BEFORE `centralCorrect_mem_shift` applies. Composing two translations
    on the same grid is `omega`-clean BUT the OR-of-4 disjuncts splits across
    them differently per quadrant — the `r - 2^(k-1)` shift maps NW→-ve, NE→+0,
    SW→-ve, SE→+0 in the column-axis, so the disjointness of the 4 R_j quadrants
    in the shifted coordinates does NOT line up with the disjointness of the 4
    parent quadrants in the original coordinates. This is the "geometric half of
    P4.1" flagged OPEN at L2104-2108.

    *C. Even *if* (A) and (B) resolve at the membership level, the equality is
    pointwise on the light cone, not on the full `[0, 2^k) × [0, 2^k)` grid. The
    `isAlive (evolve (2^(k-1)) parent.toGrid (0,0)) r` term is an `evolve`
    evaluated at r, but `parent.toGrid (0,0)` only has values in `[0, 2^k) ×
    [0, 2^k)` — outside this window, the `evolve` reads undefined grid points
    (returns `false`). On the central light cone (r ∈ [p.1 - 2^k, p.1 + 2^k] ×
    same-col, with `p ∈ central window`), the reads are well-defined; off-centre,
    they bleed off the edge. `lightCone` membership supplies the boundary
    condition, but a clean proof would need a separate "inside `[0, 2^k)`" case
    analysis that interacts badly with the 4-disjunct decomposition.

    **Verdict (RÉVISÉ c.91, #6724) — la forme LIBRE était FAUSSE, pas seulement
    difficile.** Le verdict c.8124 antérieur (« the wall IS provable ») avait été
    RETIRÉ : le quantificateur `p : Int × Int` était **libre** — rien ne
    contraignait le point d'évaluation à la fenêtre centrale que le supercell
    représente — et l'obstruction (C) ci-dessus (« off-centre, they bleed off
    the edge ») était le *symptôme* de cette fausseté, pas une difficulté de
    preuve. Réfutation machine-checkée : `p4_nw_overlap_wall_counterexample`
    (bloc de réfutation après le `sorry`) — `k = 1`, bloc au coin absolu,
    `p = r = (0,0)`, LHS `true` / RHS `false`, toutes les hypothèses
    satisfaites. Le test `exact` du bridge ne prouvait que la SUFFISANCE de
    l'énoncé, jamais sa satisfaisabilité.

    **Redesign borné APPLIQUÉ (c.92, #6724) — puis renforcé structurellement
    (c.93).** Trois changements par rapport à la forme libre réfutée (1-2 :
    c.92 ; 3 : c.93) :

    1. **Fenêtre centrale** : l'hypothèse `hp` borne `p` à la sous-fenêtre NW
       de la région centrale du parent, `[2^k, 2^k + 2^((k-1)+1))²` =
       `[2^k, 2^(k+1))²` — la forme EXACTE des bornes que
       `p4_nw_shift_lemma` (L2841) produit au site d'appel (`hsup.2` dans
       `p4_nw_membership_arm`), donc zéro friction de câblage. Le
       contre-exemple c.91 (`p = (0,0)`) est hors fenêtre : il ne
       s'instancie plus (cf. le crible kernel-checké
       `cexBlockNWcorner2_cells_outside_central`, `AdversarialBattery`).
    2. **Boîte Chebyshev étroite** : le quantificateur `∀ r ∈ lightCone p (2^k)`
       (cône Manhattan, rayon 2·u — le facteur 2 de `evolve_cone_agree`)
       est remplacé par `∀ q, chebDist p q ≤ 2^(k-1)` (miroir
       `evolve_box_agree_local`, L2896-zone). Géométrie du fit exact : pour
       `p ∈ [2^k, 2^(k+1))² = [2·2^(k-1), 4·2^(k-1))²`, la boîte
       `[p - 2^(k-1), p + 2^(k-1)]` reste dans `[2^(k-1), 5·2^(k-1))²`,
       qui est EXACTEMENT la fenêtre du supercell shifté
       (`(node R1 R2 R4 R5).toGrid` occupe `[0, 2^(k+1))² = [0, 4·2^(k-1))²`,
       shifté de `+2^(k-1)`) — là où le cône Manhattan `2^k` atteignait des
       points (p.ex. colonne 0) hors fenêtre, où le RHS est mort mais le LHS
       peut vivre (la géométrie même du contre-exemple).
    3. **Hypothèses structurelles `hn*_l`/`hn*_w` (c.93, adjudication DEMO 63,
       #6724)** : la forme bornée c.92 restait FAUSSE sur des MacroCells MAL
       FORMÉES (niveaux mélangés) — contre-exemple découvert par le prover
       multi-agent (BG run DEMO 63) et CONFIRMÉ par le noyau
       (`p4_nw_overlap_wall_c92_counterexample`, bloc de réfutation) :
       `toCellsAux` calcule `half = 2^nw.level` PAR NŒUD, donc un quadrant
       parent de niveau k+1 logé dans un slot k+2 tasse ses cellules vivantes
       DANS la boîte du mur, là où le supercell — construit sur des
       recombinaisons mortes aux `hcc` vacuistes — est vide. Réparation : les
       8 hypothèses `hn*_l` (niveau `k+1`) et `hn*_w` (`wf`) des QUATRE nœuds
       de recombinaison — exactement les faits que `p4_nw_membership_arm`
       tient déjà et passe désormais tels quels (signature de l'arm
       inchangée). Suffisance géométrique : `wf` contraint les 9
       petits-enfants de la région NW (niveau k, bien formés) ; les 7 restants
       (ne_ne, ne_se, sw_sw, sw_se, se_ne, se_sw, se_se) ont des origines
       `toCellsAux` à ligne OU colonne ≥ 6·2^(k-1) (les offsets de
       `toCellsAux` ne font que croître), STRICTEMENT hors de la région de
       dépendance de la boîte (`chebDist ≤ 2^(k-1)` autour de
       `[2^(k-1), 5·2^(k-1))²` ⊂ `[0, 6·2^(k-1))²`) — fit exact au bord du
       light cone, une fois de plus.

    Le `sorry` résiduel est désormais l'obligation HONNÊTE et (conjecturalement)
    satisfaisable : sur la boîte, chaque quadrant du supercell se replie via
    `centralCorrect_mem_shift` (hcc_j) + `p4_nw_offset_decomp`, et l'accord
    parent↔recombinaison se transporte par `evolve_box_agree_local` — la boîte
    de rayon `2^(k-1)` autour d'un point de la fenêtre centrale d'une
    recombinaison (côté `2^(k+1)`) tient EXACTEMENT dans son empreinte. La
    carte (A)/(B)/(C) reste le guide de la route membership. -/
private theorem p4_nw_overlap_wall
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R1 R2 R4 R5 : MacroCell)
    (hR1 : R1 = hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
    (hR2 : R2 = hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
    (hR4 : R4 = hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
    (hR5 : R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
    (hn1_l : (node nw_nw nw_ne nw_sw nw_se).level = k + 1)
    (hn2_l : (node nw_ne ne_nw nw_se ne_sw).level = k + 1)
    (hn4_l : (node nw_sw nw_se sw_nw sw_ne).level = k + 1)
    (hn5_l : (node nw_se ne_sw sw_ne se_nw).level = k + 1)
    (hn1_w : (node nw_nw nw_ne nw_sw nw_se).wf = true)
    (hn2_w : (node nw_ne ne_nw nw_se ne_sw).wf = true)
    (hn4_w : (node nw_sw nw_se sw_nw sw_ne).wf = true)
    (hn5_w : (node nw_se ne_sw sw_ne se_nw).wf = true)
    (hR1_l : R1.level = k) (hR2_l : R2.level = k)
    (hR4_l : R4.level = k) (hR5_l : R5.level = k)
    (hcc1 : centralCorrect (node nw_nw nw_ne nw_sw nw_se) (k - 1))
    (hcc2 : centralCorrect (node nw_ne ne_nw nw_se ne_sw) (k - 1))
    (hcc4 : centralCorrect (node nw_sw nw_se sw_nw sw_ne) (k - 1))
    (hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1))
    (p : Int × Int)
    (hp : (2^k : Int) ≤ p.1 ∧ p.1 < (2^k : Int) + 2^((k - 1) + 1) ∧
          (2^k : Int) ≤ p.2 ∧ p.2 < (2^k : Int) + 2^((k - 1) + 1)) :
    ∀ q, chebDist p q ≤ 2^(k - 1) →
      isAlive (evolve (2^(k - 1))
          ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
                 (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
            (0, 0))) q
        = isAlive ((node R1 R2 R4 R5).toGrid (0, 0))
            (q.1 - (2^(k - 1) : Int), q.2 - (2^(k - 1) : Int)) := by
  -- Assemblage (étapes 3-5 du plan c.94) : fenêtre → quadrant → localité
  -- Chebyshev (`evolve_box_agree_local`) sur le nœud de recombinaison du
  -- quadrant → caractérisation `p4_nw_rside_char_*` du supernœud résultat.
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
    by_cases hcx2 : q.2 - (2 ^ (k - 1) : Int) < (2 ^ k : Int)
  · -- Quadrant NW : `n1`, non translaté.
    have hbox : ∀ r, chebDist q r ≤ 2 ^ (k - 1) →
        isAlive ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
            (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid (0, 0)) r
          = isAlive ((node nw_nw nw_ne nw_sw nw_se).toGrid (0, 0)) r := by
      intro r hr
      obtain ⟨hr1, hr2⟩ := coord_bound_of_chebDist_le q r _ hr
      exact p4_nw_parent_agree_n1 k nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se hn1_l r
        ⟨by omega, by omega, by omega, by omega⟩
    have hL := evolve_box_agree_local (2 ^ (k - 1)) _ _ q hbox
    rw [hL]
    have hx' : 0 ≤ q.1 - (2 ^ (k - 1) : Int) ∧ q.1 - (2 ^ (k - 1) : Int) < (2 ^ k : Int) ∧
        0 ≤ q.2 - (2 ^ (k - 1) : Int) ∧ q.2 - (2 ^ (k - 1) : Int) < (2 ^ k : Int) :=
      ⟨by omega, by omega, by omega, by omega⟩
    rw [p4_nw_rside_char_nw k hk1 _ _ _ _ R1 R2 R4 R5 hR1 hR2 hR4 hR5 hR1_l
        hcc1 hcc2 hcc4 hcc5 (q.1 - (2 ^ (k - 1) : Int), q.2 - (2 ^ (k - 1) : Int)) hx']
    congr 1
    ext <;> (try dsimp only) <;> omega
  · -- Quadrant NE : `n2`, translaté `(0, 2^k)`.
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
        (2 ^ k : Int) ≤ q.2 - (2 ^ (k - 1) : Int) ∧
        q.2 - (2 ^ (k - 1) : Int) < (2 ^ k : Int) + (2 ^ k : Int) :=
      ⟨by omega, by omega, by omega, by omega⟩
    rw [p4_nw_rside_char_ne k hk1 _ _ _ _ R1 R2 R4 R5 hR1 hR2 hR4 hR5 hR1_l
        hcc1 hcc2 hcc4 hcc5 (q.1 - (2 ^ (k - 1) : Int), q.2 - (2 ^ (k - 1) : Int)) hx']
    congr 1
    ext <;> (try dsimp only) <;> omega
  · -- Quadrant SW : `n4`, translaté `(2^k, 0)`.
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
    have hx' : (2 ^ k : Int) ≤ q.1 - (2 ^ (k - 1) : Int) ∧
        q.1 - (2 ^ (k - 1) : Int) < (2 ^ k : Int) + (2 ^ k : Int) ∧
        0 ≤ q.2 - (2 ^ (k - 1) : Int) ∧ q.2 - (2 ^ (k - 1) : Int) < (2 ^ k : Int) :=
      ⟨by omega, by omega, by omega, by omega⟩
    rw [p4_nw_rside_char_sw k hk1 _ _ _ _ R1 R2 R4 R5 hR1 hR2 hR4 hR5 hR1_l
        hcc1 hcc2 hcc4 hcc5 (q.1 - (2 ^ (k - 1) : Int), q.2 - (2 ^ (k - 1) : Int)) hx']
    congr 1
    ext <;> (try dsimp only) <;> omega
  · -- Quadrant SE : `n5`, translaté `(2^k, 2^k)`.
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
        (2 ^ k : Int) ≤ q.2 - (2 ^ (k - 1) : Int) ∧
        q.2 - (2 ^ (k - 1) : Int) < (2 ^ k : Int) + (2 ^ k : Int) :=
      ⟨by omega, by omega, by omega, by omega⟩
    rw [p4_nw_rside_char_se k hk1 _ _ _ _ R1 R2 R4 R5 hR1 hR2 hR4 hR5 hR1_l
        hcc1 hcc2 hcc4 hcc5 (q.1 - (2 ^ (k - 1) : Int), q.2 - (2 ^ (k - 1) : Int)) hx']
    congr 1
    ext <;> (try dsimp only) <;> omega

/-! ### Réfutation : la forme LIBRE (pré-c.92) du mur et du bridge était FAUSSE (#6724, c.91)

**Statut (c.92)** : les théorèmes nommés `p4_nw_overlap_wall`, `p4_nw_g3_bridge`
et `p4_nw_supercell_agree` portent désormais l'hypothèse de fenêtre `hp` et (pour
le mur) le quantificateur boîte-Chebyshev — le redesign borné prescrit ci-dessous
est APPLIQUÉ. Les contre-exemples de ce bloc réfutent la **forme libre pré-c.92**
(quantificateur `p : Int × Int` libre, cône Manhattan) ; ils sont conservés comme
garde-fous : toute tentative de retirer la borne ou d'élargir la boîte re-tombe
dessus. Énoncés en forme fermée `¬ (∀ …)`, ils compilent indépendamment des
théorèmes nommés.

**Statut (c.93)** : un QUATRIÈME garde-fou clôt le bloc
(`p4_nw_overlap_wall_c92_counterexample`) : la forme bornée c.92 SANS hypothèses
structurelles restait fausse sur des MacroCells mal formées (niveaux mélangés) —
contre-exemple découvert par le prover multi-agent (BG run DEMO 63,
`HASHLIFE_P4_NW_OVERLAP_WALL`) et confirmé par le noyau. Les théorèmes nommés
portent depuis les 8 hypothèses `hn*_l`/`hn*_w` (niveau `k+1` + `wf` des quatre
nœuds de recombinaison), qui bloquent l'instanciation (le nœud mixte
`node E1 z E1 z` n'est pas `wf`).

Le quantificateur `p : Int × Int` était **libre** dans la forme pré-c.92 : rien
ne contraignait `p` (ni `r`) à la fenêtre centrale que le supercell représente.
C'est le piège c.19 **un niveau au-dessus** : l'énoncé passe le test de
suffisance (`exact` au site d'appel) mais est insatisfiable. L'« obstruction C »
de la carte c.8124 (« off-centre, they bleed off the edge ») était le symptôme
de la fausseté, pas une difficulté de preuve.

**Contre-exemple (k = 1, bloc au coin absolu).** `nw_nw` = bloc plein niveau 1,
les 15 autres petits-enfants vides. Le parent porte un bloc (nature morte) sur
`{(0,0),(0,1),(1,0),(1,1)}`. En `p = r = (0,0)` :
- LHS mur : `isAlive (evolve 1 parent.toGrid) (0,0) = true` (le bloc persiste) ;
- RHS mur : `isAlive supercell.toGrid (-1,-1) = false` — `toGrid (0,0)` n'émet
  que des coordonnées non négatives, `(-1,-1)` est structurellement hors fenêtre.
Toutes les hypothèses (`hR_j` par `rfl`, niveaux et `hcc_j` par `decide`) sont
satisfaites : aucune preuve de la forme libre ne peut exister. Même
instanciation pour le bridge (`evolve 2` vs `evolve 1`, RHS à `(-1,-1)`).
Avec la borne c.92, `p = (0,0)` est hors fenêtre (`[2, 4)²` à `k = 1`) :
l'instanciation est bloquée — cf. le crible `AdversarialBattery`
(`cexBlockNWcorner2_cells_outside_central`, kernel-checké).

**Réparation appliquée (c.92)** : borner `p` à la fenêtre centrale du parent
(`2^k ≤ p.i < 2^(k+1)`, forme syntaxique `p4_nw_shift_lemma`) et transporter par
le lemme de localité **Chebyshev** (`evolve_box_agree_local` : accord sur la
boîte de rayon `u` ⇒ accord de `evolve u` au point), car le cône Manhattan `2·u`
de `evolve_cone_agree` déborde la fenêtre du supercell même pour `p` central,
alors que la boîte Chebyshev `[p - u, p + u]` y tient exactement
(`[2^(k-1), 5·2^(k-1))` = fenêtre du supercell). Les bornes SONT disponibles au
niveau de `p4_succ_membership` : `p4_nw_membership_arm` les tient dans `hsup.2`
(sortie de `p4_nw_shift_lemma`) et les passe telles quelles. Précédent de
réparation : c.19 (énoncé renforcé, sorry count FLAT, anti-régression §D non
applicable). -/

/-- Cellule niveau 1 vide (témoin du contre-exemple #6724). -/
private def p4CexEmpty1 : MacroCell :=
  node (leaf false) (leaf false) (leaf false) (leaf false)

/-- Cellule niveau 1 pleine — un bloc 2×2, nature morte de Life
    (témoin du contre-exemple #6724). -/
private def p4CexBlock1 : MacroCell :=
  node (leaf true) (leaf true) (leaf true) (leaf true)

/-- **La forme LIBRE (pré-c.92) de `p4_nw_overlap_wall` est fausse.**
    Instanciation : `k = 1`, `nw_nw` = bloc plein, les 15 autres petits-enfants
    vides, `p = r = (0,0)`. LHS `true` (bloc = nature morte), RHS `false`
    (`(-1,-1)` hors de la fenêtre non-négative de `toGrid`). Certifié par le
    noyau (`decide`, zéro axiome — réductible depuis la réécriture `ceilLog2`
    #9536). C'est ce théorème qui a imposé le redesign borné c.92 : le mur nommé
    porte désormais `hp` (fenêtre `[2^k, 2^(k+1))²`, qui exclut `p = (0,0)`) et
    la boîte Chebyshev. Gardé comme garde-fou anti-régression d'énoncé.
    Précédent in-file : `p4_unrestricted_counterexample`. -/
theorem p4_nw_overlap_wall_counterexample :
    ¬ (∀ (k : Nat), 1 ≤ k →
       ∀ (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
          sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
          R1 R2 R4 R5 : MacroCell),
       R1 = hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se) →
       R2 = hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw) →
       R4 = hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne) →
       R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw) →
       R1.level = k → R2.level = k → R4.level = k → R5.level = k →
       centralCorrect (node nw_nw nw_ne nw_sw nw_se) (k - 1) →
       centralCorrect (node nw_ne ne_nw nw_se ne_sw) (k - 1) →
       centralCorrect (node nw_sw nw_se sw_nw sw_ne) (k - 1) →
       centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1) →
       ∀ (p : Int × Int), ∀ r ∈ lightCone p (2^k),
         isAlive (evolve (2^(k - 1))
             ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
                    (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
               (0, 0))) r
           = isAlive ((node R1 R2 R4 R5).toGrid (0, 0))
               (r.1 - (2^(k - 1) : Int), r.2 - (2^(k - 1) : Int))) := by
  intro h
  have hinst := h 1 (by decide)
      p4CexBlock1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1
      p4CexEmpty1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1
      p4CexEmpty1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1
      p4CexEmpty1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1
      (hashlifeResultAux 2 (node p4CexBlock1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1))
      (hashlifeResultAux 2 (node p4CexEmpty1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1))
      (hashlifeResultAux 2 (node p4CexEmpty1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1))
      (hashlifeResultAux 2 (node p4CexEmpty1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1))
      rfl rfl rfl rfl
      (by decide) (by decide) (by decide) (by decide)
      (by unfold centralCorrect; decide) (by unfold centralCorrect; decide)
      (by unfold centralCorrect; decide) (by unfold centralCorrect; decide)
      (0, 0) (0, 0) (self_mem_lightCone (0, 0) (2^1))
  exact absurd hinst (by decide)

/-- **La forme LIBRE (pré-c.92) de `p4_nw_g3_bridge` est fausse** — même
    instanciation que `p4_nw_overlap_wall_counterexample` (le bridge hérite la
    fausseté du mur par sa forme, mais la réfutation directe ne dépend pas de la
    décomposition (a)/(b)). LHS `evolve 2` du bloc à `(0,0)` = `true` ; RHS
    `evolve 1` de `[(0,0)]` (la cellule isolée meurt) évalué à `(-1,-1)` =
    `false`. Le bridge nommé porte désormais `hp` (c.92). -/
theorem p4_nw_g3_bridge_counterexample :
    ¬ (∀ (k : Nat), 1 ≤ k →
       ∀ (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
          sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
          R1 R2 R4 R5 : MacroCell),
       R1 = hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se) →
       R2 = hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw) →
       R4 = hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne) →
       R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw) →
       R1.level = k → R2.level = k → R4.level = k → R5.level = k →
       centralCorrect (node nw_nw nw_ne nw_sw nw_se) (k - 1) →
       centralCorrect (node nw_ne ne_nw nw_se ne_sw) (k - 1) →
       centralCorrect (node nw_sw nw_se sw_nw sw_ne) (k - 1) →
       centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1) →
       ∀ (p : Int × Int),
         isAlive (evolve (2^k)
             ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
                    (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
               (0, 0))) p
           = isAlive (evolve (2^(k - 1)) ((node R1 R2 R4 R5).toGrid (0, 0)))
               (p.1 - (2^k : Int) + (2^(k - 1) : Int),
                p.2 - (2^k : Int) + (2^(k - 1) : Int))) := by
  intro h
  have hinst := h 1 (by decide)
      p4CexBlock1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1
      p4CexEmpty1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1
      p4CexEmpty1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1
      p4CexEmpty1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1
      (hashlifeResultAux 2 (node p4CexBlock1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1))
      (hashlifeResultAux 2 (node p4CexEmpty1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1))
      (hashlifeResultAux 2 (node p4CexEmpty1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1))
      (hashlifeResultAux 2 (node p4CexEmpty1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1))
      rfl rfl rfl rfl
      (by decide) (by decide) (by decide) (by decide)
      (by unfold centralCorrect; decide) (by unfold centralCorrect; decide)
      (by unfold centralCorrect; decide) (by unfold centralCorrect; decide)
      (0, 0)
  exact absurd hinst (by decide)

/-- **`p4_nw_supercell_agree` est FAUX tel qu'énoncé** — même instanciation.
    C'est la réfutation **décisionnelle** : les grains « porter supercell_agree
    aux quadrants NE/SW » (miroirs de la même forme) viseraient des énoncés
    insatisfiables ; ils sont annulés au profit du redesign borné. Le LHS est la
    forme double demi-pas `evolve 2^(k-1) ∘ evolve 2^(k-1)` (= `evolve 2` ici),
    `true` en `(0,0)` ; RHS `false` en `(-1,-1)`. -/
theorem p4_nw_supercell_agree_counterexample :
    ¬ (∀ (k : Nat), 1 ≤ k →
       ∀ (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
          sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
          R1 R2 R4 R5 : MacroCell),
       R1 = hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se) →
       R2 = hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw) →
       R4 = hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne) →
       R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw) →
       R1.level = k → R2.level = k → R4.level = k → R5.level = k →
       centralCorrect (node nw_nw nw_ne nw_sw nw_se) (k - 1) →
       centralCorrect (node nw_ne ne_nw nw_se ne_sw) (k - 1) →
       centralCorrect (node nw_sw nw_se sw_nw sw_ne) (k - 1) →
       centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1) →
       ∀ (p : Int × Int),
         isAlive (evolve (2^(k - 1)) (evolve (2^(k - 1))
             ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
                    (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
               (0, 0)))) p
           = isAlive (evolve (2^(k - 1)) ((node R1 R2 R4 R5).toGrid (0, 0)))
               (p.1 - (2^k : Int) + (2^(k - 1) : Int),
                p.2 - (2^k : Int) + (2^(k - 1) : Int))) := by
  intro h
  have hinst := h 1 (by decide)
      p4CexBlock1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1
      p4CexEmpty1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1
      p4CexEmpty1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1
      p4CexEmpty1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1
      (hashlifeResultAux 2 (node p4CexBlock1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1))
      (hashlifeResultAux 2 (node p4CexEmpty1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1))
      (hashlifeResultAux 2 (node p4CexEmpty1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1))
      (hashlifeResultAux 2 (node p4CexEmpty1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1))
      rfl rfl rfl rfl
      (by decide) (by decide) (by decide) (by decide)
      (by unfold centralCorrect; decide) (by unfold centralCorrect; decide)
      (by unfold centralCorrect; decide) (by unfold centralCorrect; decide)
      (0, 0)
  exact absurd hinst (by decide)

set_option maxHeartbeats 4000000 in
/-- **La forme bornée c.92 SANS hypothèses structurelles était ENCORE fausse**
    — sur des MacroCells MAL FORMÉES (niveaux mélangés). Contre-exemple découvert
    par le prover multi-agent (BG run DEMO 63, `HASHLIFE_P4_NW_OVERLAP_WALL` :
    le TacticAgent a refusé de soumettre une preuve et produit cette
    instanciation), adjugé et certifié par le noyau (ai-01, `decide`).

    Mécanisme : `toCellsAux` calcule `half = 2^nw.level` PAR NŒUD — un quadrant
    parent de niveau 1 logé dans un slot de niveau 2 tasse ses cellules vivantes
    près de l'origine de son slot, DANS la boîte du mur. Instanciation (`k = 1`) :
    `nw_*` = `p4CexEmpty1` (vide, niveau 1) ; `ne_*`, `sw_*`, `se_nw` =
    `leaf false` ; `se_ne = se_sw = se_se = leaf true`. Le quadrant SE parent
    `node z o o o` (niveau 1, slot 2) place ses vivantes en (4,5),(5,4),(5,5) →
    naissance Conway en (4,4). Les recombinaisons `n2/n4/n5` (mixtes niveau 1/0,
    p.ex. `node E1 z E1 z`) sont MORTES : `hashlifeResultAux` retombe sur la
    branche malformée (`emptyOfLevel`), les `hcc` sont vacuistes, le supercell
    est vide. En `p = (3,3)` (fenêtre `[2,4)²`), `q = (4,4)`
    (`chebDist = 1 ≤ 2^0`) : LHS `true` / RHS `false`.

    C'est CE théorème qui a imposé le renforcement c.93 : les nœuds mixtes ne
    sont pas `wf`, donc les 8 hypothèses `hn*_l`/`hn*_w` du mur bloquent
    l'instanciation. Gardé comme garde-fou anti-régression d'énoncé : toute
    tentative de retirer les hypothèses structurelles re-tombe dessus.
    Précédents in-file : `p4_nw_overlap_wall_counterexample` (forme libre),
    `p4_unrestricted_counterexample`. -/
theorem p4_nw_overlap_wall_c92_counterexample :
    ¬ (∀ (k : Nat), 1 ≤ k →
       ∀ (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
          sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
          R1 R2 R4 R5 : MacroCell),
       R1 = hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se) →
       R2 = hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw) →
       R4 = hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne) →
       R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw) →
       R1.level = k → R2.level = k → R4.level = k → R5.level = k →
       centralCorrect (node nw_nw nw_ne nw_sw nw_se) (k - 1) →
       centralCorrect (node nw_ne ne_nw nw_se ne_sw) (k - 1) →
       centralCorrect (node nw_sw nw_se sw_nw sw_ne) (k - 1) →
       centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1) →
       ∀ (p : Int × Int),
         ((2^k : Int) ≤ p.1 ∧ p.1 < (2^k : Int) + 2^((k - 1) + 1) ∧
          (2^k : Int) ≤ p.2 ∧ p.2 < (2^k : Int) + 2^((k - 1) + 1)) →
       ∀ q, chebDist p q ≤ 2^(k - 1) →
         isAlive (evolve (2^(k - 1))
             ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
                    (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
               (0, 0))) q
           = isAlive ((node R1 R2 R4 R5).toGrid (0, 0))
               (q.1 - (2^(k - 1) : Int), q.2 - (2^(k - 1) : Int))) := by
  intro h
  have hinst := h 1 (by decide)
      p4CexEmpty1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1
      (leaf false) (leaf false) (leaf false) (leaf false)
      (leaf false) (leaf false) (leaf false) (leaf false)
      (leaf false) (leaf true) (leaf true) (leaf true)
      (hashlifeResultAux 2 (node p4CexEmpty1 p4CexEmpty1 p4CexEmpty1 p4CexEmpty1))
      (hashlifeResultAux 2 (node p4CexEmpty1 (leaf false) p4CexEmpty1 (leaf false)))
      (hashlifeResultAux 2 (node p4CexEmpty1 p4CexEmpty1 (leaf false) (leaf false)))
      (hashlifeResultAux 2 (node p4CexEmpty1 (leaf false) (leaf false) (leaf false)))
      rfl rfl rfl rfl
      (by decide) (by decide) (by decide) (by decide)
      (by unfold centralCorrect; decide) (by unfold centralCorrect; decide)
      (by unfold centralCorrect; decide) (by unfold centralCorrect; decide)
      (3, 3) (by decide)
      (4, 4) (by decide)
  exact absurd hinst (by decide)

/-- **G3 wave-assembly bridge (named extraction, #6724 c.745).** The research
    heart of `p4_nw_supercell_agree`, extracted as a NAMED lemma carrying ALL
    the call-site hypotheses — per the ai-01 extraction protocol (DM
    `msg-20260729T000329-m5ly00`: "isoler un sorry sans transporter les
    hypothèses du site d'appel FABRIQUE un énoncé faux"). The signature mirrors
    `p4_nw_supercell_agree` exactly (16 grandchildren, R1..R5 + hR1..5,
    hcc1/2/4/5, p); the conclusion is the POST-`evolve_half_step` residual goal
    (`evolve (2^k)` on the LHS). The specialization check — does
    `exact p4_nw_g3_bridge ...` (called from the root) close the root's residual
    goal? — IS the protocol's correctness test: if it compiles, the signature is
    right (transports every call-site hypothesis); if not, the extraction is wrong.

    **The body decomposes into two halves** (attack plan for the next cycle):
    (a) **First-half-step toGrid agreement** (THE WALL): show that
        `evolve (2^(k-1)) parent.toGrid` and `(node R1 R2 R4 R5).toGrid` agree on
        the central light cone. This assembles the four `centralCorrect_mem_shift`
        facts (hcc1/2/4/5 → R_j centre = evolve (2^(k-1)) n_j on the central
        window) via `mem_toGrid_node` (node→4-quadrant decomposition, sorry-free
        L1478). The quadrant-offset arithmetic (NW at (0,0), NE at (0, 2^level),
        etc.) and the `2^level` half-size shifts are the assembly glue. **The
        offset half is now armed (c.749):** the signature carries
        `hR1_l … hR5_l : R_j.level = k` (transported from the call site, which
        derives them via the proven `hashlifeResultAux_level_cellWf`), and the
        named sorry-free lemma `p4_nw_offset_decomp` (just below `isAlive_true_iff_mem_local`)
        pins `(node R1 R2 R4 R5).toGrid`'s quadrant offsets to concrete `2^k`.

        **Firsthand map of the unbridged half (c.750) — the wall is the
        DOUBLE-NINE OVERLAP realignment, not generic "agreement".** The
        wave-1 sub-cells R_j are built from the parent's grandchildren, but
        ONLY `R1` (from `node nw_nw nw_ne nw_sw nw_se`) is a clean parent
        quadrant (the NW grandchild `n1`). `R2` (from `node nw_ne ne_nw nw_se
        ne_sw`) straddles the NW/NE boundary, `R4` straddles NW/SW, and `R5`
        (from `node nw_se ne_sw sw_ne se_nw`) is the centre straddling all four.
        The parent decomposes via `mem_toGrid_node` into FOUR NON-OVERLAPPING
        quadrants (`n1`/`n3`/`n7`/`n9`, offsets `(0,0)`/`(0,2^k)`/`(2^k,0)`/
        `(2^k,2^k)`), while `(node R1 R2 R4 R5)` tiles the same central region
        with these OVERLAPPING recombinations. Pointwise agreement between the
        two grids on the central window therefore requires reconciling a
        non-overlapping quadrant tiling against an overlapping double-nine
        tiling — the level-dependent offset realignment of grandchildren that
        belong to different parent quadrants. This IS the "geometric half of
        P4.1" flagged OPEN at L2104-2108 ("genuinely non-structural … queueable
        behind the `step_light_cone` P2 machinery"); that P2 precondition
        (locality: `step_light_cone`/`evolve_cone_agree`/`quadrant_cone_agree`,
        all sorry-free PROVEN) is now satisfied, so the overlap lemma is
        attackable as a named multi-cycle target. The three composition pieces:
        (i) `p4_nw_offset_decomp` — R-side quadrant offsets (ARMED, sorry-free);
        (ii) `centralCorrect_mem_shift` L2443 — R_j ↔ evolve n_j membership
        (AVAILABLE, sorry-free); (iii) the MISSING grid-level overlap lemma
        relating `parent.toGrid` to the overlapping `n_j.toGrid` on the central
        window (assembled from two `mem_toGrid_node` passes + `mem_toGrid_shift`
        L1437 / `toGrid_shift_between` L1453, but non-trivial due to the
        cross-quadrant grandchild realignment).
    (b) **Second-half-step locality** (PROVEN SORRY-FREE, c.764): the outer
        `evolve (2^(k-1))` transport is now a theorem in the bridge body. The
        RHS eval point `p' = p - 2^k + 2^(k-1) = p - 2^(k-1)` is aligned onto
        `p` via `evolve_shift` + `isAlive_shift` (the supercell's shifted origin
        rewritten to the parent's), then `evolve_cone_agree (t := 0)` transports
        the agreement through the outer evolve. The (b) machinery (translation
        invariance `evolve_shift`, #8797) this was waiting on has landed; the
        residual is exactly (a).

    Sorry count FLAT (8 → 8) but the PROVEN share grows: the (b) transport is
    now a sorry-free theorem (previously implicit inside the opaque sorry), and
    the residual (a) is the NAMED lemma `p4_nw_overlap_wall` just above — a
    single, compiler-checked statement the next attacker opens, instead of
    re-discovering the obstruction inside the bridge's `sorry`. The bridge body
    itself is sorry-free; its only sorry-dependency is `p4_nw_overlap_wall`. See #6724.

    **Correction (c.91, #6724)** : le test de spécialisation `exact` ci-dessus prouve
    la SUFFISANCE de l'énoncé du mur, PAS sa satisfaisabilité — la forme LIBRE
    (`p` non borné) du mur ET de ce bridge était fausse : voir
    `p4_nw_g3_bridge_counterexample` (bloc de réfutation après le mur).

    **Redesign borné APPLIQUÉ (c.92, #6724)** : ce bridge porte désormais `hp`
    (`p` dans la fenêtre centrale NW `[2^k, 2^(k+1))²` — la forme syntaxique
    exacte de `hsup.2` produite par `p4_nw_shift_lemma` dans l'arm), et le
    transport (b) utilise `evolve_box_agree_local` (boîte Chebyshev, rayon
    `2^(k-1)`) au lieu du cône Manhattan `evolve_cone_agree` (rayon `2^k`,
    qui débordait de la fenêtre du supercell — géométrie du contre-exemple).

    **Renforcement structurel (c.93, #6724)** : les 8 hypothèses `hn*_l`/`hn*_w`
    (niveau + `wf` des quatre nœuds de recombinaison) sont transmises au mur —
    sans elles la forme bornée restait fausse sur des cellules mal formées
    (cf. `p4_nw_overlap_wall_c92_counterexample`, découverte DEMO 63). -/
private theorem p4_nw_g3_bridge
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R1 R2 R4 R5 : MacroCell)
    (hR1 : R1 = hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
    (hR2 : R2 = hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
    (hR4 : R4 = hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
    (hR5 : R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
    (hn1_l : (node nw_nw nw_ne nw_sw nw_se).level = k + 1)
    (hn2_l : (node nw_ne ne_nw nw_se ne_sw).level = k + 1)
    (hn4_l : (node nw_sw nw_se sw_nw sw_ne).level = k + 1)
    (hn5_l : (node nw_se ne_sw sw_ne se_nw).level = k + 1)
    (hn1_w : (node nw_nw nw_ne nw_sw nw_se).wf = true)
    (hn2_w : (node nw_ne ne_nw nw_se ne_sw).wf = true)
    (hn4_w : (node nw_sw nw_se sw_nw sw_ne).wf = true)
    (hn5_w : (node nw_se ne_sw sw_ne se_nw).wf = true)
    (hR1_l : R1.level = k) (hR2_l : R2.level = k)
    (hR4_l : R4.level = k) (hR5_l : R5.level = k)
    (hcc1 : centralCorrect (node nw_nw nw_ne nw_sw nw_se) (k - 1))
    (hcc2 : centralCorrect (node nw_ne ne_nw nw_se ne_sw) (k - 1))
    (hcc4 : centralCorrect (node nw_sw nw_se sw_nw sw_ne) (k - 1))
    (hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1))
    (p : Int × Int)
    (hp : (2^k : Int) ≤ p.1 ∧ p.1 < (2^k : Int) + 2^((k - 1) + 1) ∧
          (2^k : Int) ≤ p.2 ∧ p.2 < (2^k : Int) + 2^((k - 1) + 1)) :
    isAlive (evolve (2^k)
        ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
          (0, 0))) p
      = isAlive (evolve (2^(k - 1)) ((node R1 R2 R4 R5).toGrid (0, 0)))
          (p.1 - (2^k : Int) + (2^(k - 1) : Int),
           p.2 - (2^k : Int) + (2^(k - 1) : Int)) := by
  -- Expose the **symmetric half-step form** (c.750→c.751 structural step): both
  -- sides now carry an outer `evolve (2^(k-1))`, which is the locality-ready shape
  -- for `evolve_cone_agree` (proven sorry-free, L963). The goal at the `sorry` is
  -- the (a)/(b) decomposition site:
  --
  --   (a) **inner agreement** — `evolve (2^(k-1)) parent.toGrid` agrees (pointwise,
  --       on the central light cone) with `(node R1 R2 R4 R5).toGrid`, assembled
  --       from the 4 `hcc_j` (`centralCorrect_mem_shift`, L2443) + the armed
  --       offset decomp `p4_nw_offset_decomp` (#8768). This is the **double-nine
  --       overlap wall** (see docstring + L2104-2108): non-overlapping parent
  --       quadrants vs overlapping wave-1 recombinations R2/R4/R5.
  --   (b) **outer locality** — once (a) holds, `evolve_cone_agree (2^(k-1))
  --       (2^(k-1))` transports the agreement through the outer evolve. The
  --       subtlety (not a single apply): LHS evaluates at `p`, RHS at
  --       `p' = p - 2^k + 2^(k-1)` (NW correspondence — the goal's offset at the
  --       theorem statement, not `p - 2^(k-1)`), so the locality step needs the
  --       point-shift alignment between the parent's central window (origin
  --       `(0,0)`) and the supercell `(node R1 R2 R4 R5)`'s shifted origin. That
  --       alignment is now directly attackable: `evolve_shift` (translation-
  --       invariance capstone, sorry-free, on `main` via #8797 —
  --       `shift v (evolve n g) = evolve n (shift v g)`) lets the supercell's
  --       shifted origin be rewritten to match the parent's before
  --       `evolve_cone_agree` applies. The residual obstruction is (a), not (b).
  --
  -- **Extraction-test caveat** (ai-01 #8766 review): the `exact p4_nw_g3_bridge
  --   ...` at the call site (`p4_nw_supercell_agree`, below) proves the bridge is
  --   SUFFICIENT to close the root goal — the compiler re-checks this each build,
  --   so it IS the faithful-extraction test (#8763). It does NOT prove the bridge
  --   is SATISFIABLE (provable): an over-general or under-hypothesized statement
  --   passes `exact` and remains a dead-end. The `R_j.level = k` hypotheses
  --   (added #8768) are load-bearing precisely here — drop them and the offsets
  --   `2^R_j.level` in `mem_toGrid_node` stay opaque, leaving the bridge
  --   under-hypothesized (the c.19 trap: a statement that type-checks at the call
  --   site but cannot be proven). With them, the bridge is correctly-stated
  --   (offsets pinned to `2^k`); it is still UNPROVEN — the (a) overlap wall
  --   above is the obstruction, not a malformed statement.
  rw [evolve_half_step k hk1]
  -- **(b) outer locality — proven sorry-free (c.764, resserré c.92).** Both sides
  -- carry an outer `evolve (2^(k-1))`. The RHS evaluates at `p' = p - 2^k + 2^(k-1)`,
  -- which simplifies to `p - 2^(k-1)` (since `2^k = 2·2^(k-1)`). We shift the RHS
  -- grid by `(2^(k-1), 2^(k-1))` so both sides eval at `p`, then transport agreement
  -- through the outer evolve with `evolve_box_agree_local` (Chebyshev box, radius
  -- `2^(k-1)` — the c.92 tightening: the Manhattan cone of `evolve_cone_agree` had
  -- radius `2^k` and escaped the supercell window, which is why the free-form wall
  -- was refutable). The residual is exactly the (a) inner-agreement
  -- `p4_nw_overlap_wall` (bounded form).
  have h2k : (2^k : Int) = (2^(k - 1) : Int) + (2^(k - 1) : Int) := by
    have hn : 2^k = 2^(k - 1) + 2^(k - 1) := by
      set m := k - 1 with hm
      have hkm : k = m + 1 := by omega
      rw [hkm, Nat.pow_succ]; ring
    exact mod_cast hn
  have hpt1 : p.1 - (2^k : Int) + (2^(k - 1) : Int) = p.1 - (2^(k - 1) : Int) := by omega
  have hpt2 : p.2 - (2^k : Int) + (2^(k - 1) : Int) = p.2 - (2^(k - 1) : Int) := by omega
  rw [hpt1, hpt2]
  -- RHS now evals at `(p - 2^(k-1))`; rewrite to eval at `p` on a shifted grid.
  have hR : isAlive (evolve (2^(k - 1)) ((node R1 R2 R4 R5).toGrid (0, 0)))
        (p.1 - (2^(k - 1) : Int), p.2 - (2^(k - 1) : Int))
      = isAlive (evolve (2^(k - 1))
          (shift ((2^(k - 1) : Int), (2^(k - 1) : Int)) ((node R1 R2 R4 R5).toGrid (0, 0)))) p := by
    rw [← evolve_shift, isAlive_shift]
  rw [hR]
  -- Both sides eval at `p`. Transport through the outer `evolve (2^(k-1))` via the
  -- Chebyshev-box mirror: the box `[p ± 2^(k-1)]` fits exactly inside the shifted
  -- supercell window `[2^(k-1), 5·2^(k-1))²` when `p` satisfies `hp`.
  apply evolve_box_agree_local
  intro q hq
  rw [isAlive_shift]
  exact p4_nw_overlap_wall k hk1
    nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
    sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
    R1 R2 R4 R5 hR1 hR2 hR4 hR5
    hn1_l hn2_l hn4_l hn5_l hn1_w hn2_w hn4_w hn5_w
    hR1_l hR2_l hR4_l hR5_l
    hcc1 hcc2 hcc4 hcc5 p hp q hq

/-- **S4 nw supercell agreement (the residual `sorry`, ai-01's proof target).**
    The wave-1/wave-2 correspondence for the nw quadrant, stated at the
    `evolve`-level so the arm lemma below wires it with a single `rw`. Reads:
    "the twice-`evolve 2^(k-1)`d parent grid at `p` equals the once-`evolve
    2^(k-1)`d wave-1 supercell `node R1 R2 R4 R5` at the supercell-local point
    `p' = (p.1 - 2^k + 2^(k-1), …)`." The `hR_i` link the (opaque, so the arm
    stays whnf-free) supercell children to the concrete wave-1 results.

    **Correction de l'énoncé (c.19) — l'isolation d'origine était SOUS-HYPOTHÉSÉE,
    donc FAUSSE, et non pas seulement « difficile ».** La version antérieure ne
    prenait que les 16 sous-cellules *arbitraires*, les `R_i` et leurs équations
    de définition : aucune hypothèse de `wf`/`level`, aucune `ih`. Or
    `hashlifeResultAux` n'est reliée à `evolve` que sur des entrées bien formées —
    sur une entrée malformée elle retombe sur la branche `| _ + 1, c` de
    `Hashlife.lean` (L202-205) et renvoie `emptyOfLevel (c.level - 1)`, c.-à-d.
    une cellule *toute morte*.

    **Contre-exemple** (réfutation de l'ancien énoncé) : `k = 1`, les 16
    sous-cellules toutes égales à `leaf true`. Alors chaque `n_i = node (leaf …)
    (leaf …) (leaf …) (leaf …)` est un nœud *de feuilles*, qui ne filtre pas le
    motif « nœud de nœuds » ; `hashlifeResultAux 2 n_i` tombe donc sur la branche
    malformée et vaut `emptyOfLevel 0` (morte). Le membre de droite est alors
    `isAlive` d'une grille vide = `false` partout, tandis que le membre de gauche
    est la vraie évolution du bloc plein 4×4 du parent, non vide à la génération
    2. Les deux membres diffèrent : l'énoncé n'était pas un théorème. Aucune
    itération de prover ne pouvait le fermer — ce qui explique les cycles
    dépensés dessus depuis #6875.

    **Réparation** : on ajoute les quatre `centralCorrect n_i (k-1)` — exactement
    l'information sémantique manquante (« chaque résultat wave-1 calcule bien le
    demi-pas `evolve 2^(k-1)` de son propre nœud »). Elles sont *déjà disponibles*
    en amont : le site d'appel `p4_succ_membership` calcule `hn1`/`hn2`/`hn4`/`hn5`
    (L3159-3173) et dispose de `ih` ; le bras les dérive et les transmet ici. Le
    contenu résiduel de S4 est ainsi réduit à sa substance propre — translation de
    repère + accord de cône de lumière (`evolve_cone_agree` / `quadrant_cone_agree`
    par-dessus le découpage `evolve_half_step`) — sans plomberie `ih`.

    Sorry count FLAT (8 → 8) : aucune preuve supprimée, l'énoncé est *renforcé*
    (anti-régression §D ne s'applique pas). ai-01 en garde la preuve (tree-lock
    #6875) ; la frontière reste au niveau `evolve` pour la compilabilité du
    câblage.

    **Correction (c.91, #6724)** : la réparation c.19 (ajout des `hcc_j`) était
    NÉCESSAIRE mais PAS SUFFISANTE — le piège c.19 se reproduit un niveau
    au-dessus : `p` reste libre alors que le supercell ne représente que la
    fenêtre centrale du parent. Réfutation machine-checkée :
    `p4_nw_supercell_agree_counterexample` (bloc de réfutation après le mur).
    Les grains « porter supercell_agree aux quadrants NE/SW » (même forme non
    bornée, cf. `p4_se_overlap_wall` c.90) sont annulés ; la voie est le
    redesign borné (fenêtre centrale + localité Chebyshev, bloc de section
    après le mur).

    **Redesign borné APPLIQUÉ (c.92, #6724)** : ce théorème porte désormais `hp`
    (fenêtre centrale NW `[2^k, 2^(k+1))²`), transmis tel quel au bridge. Le
    site d'appel (`p4_nw_membership_arm`) fournit `hsup.2` — la forme
    syntaxique EXACTE de `hp` issue de `p4_nw_shift_lemma` — sans conversion.

    **Renforcement structurel (c.93, #6724)** : les 8 hypothèses `hn*_l`/`hn*_w`
    (niveau + `wf` des quatre nœuds de recombinaison — les faits mêmes que l'arm
    tient de son site d'appel, L3625-3632 pré-c.93) sont ajoutées ici et
    transmises au bridge : sans elles la chaîne bornée c.92 restait fausse sur
    des MacroCells mal formées (`p4_nw_overlap_wall_c92_counterexample`). -/
private theorem p4_nw_supercell_agree
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R1 R2 R4 R5 : MacroCell)
    (hR1 : R1 = hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
    (hR2 : R2 = hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
    (hR4 : R4 = hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
    (hR5 : R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
    (hn1_l : (node nw_nw nw_ne nw_sw nw_se).level = k + 1)
    (hn2_l : (node nw_ne ne_nw nw_se ne_sw).level = k + 1)
    (hn4_l : (node nw_sw nw_se sw_nw sw_ne).level = k + 1)
    (hn5_l : (node nw_se ne_sw sw_ne se_nw).level = k + 1)
    (hn1_w : (node nw_nw nw_ne nw_sw nw_se).wf = true)
    (hn2_w : (node nw_ne ne_nw nw_se ne_sw).wf = true)
    (hn4_w : (node nw_sw nw_se sw_nw sw_ne).wf = true)
    (hn5_w : (node nw_se ne_sw sw_ne se_nw).wf = true)
    (hR1_l : R1.level = k) (hR2_l : R2.level = k)
    (hR4_l : R4.level = k) (hR5_l : R5.level = k)
    (hcc1 : centralCorrect (node nw_nw nw_ne nw_sw nw_se) (k - 1))
    (hcc2 : centralCorrect (node nw_ne ne_nw nw_se ne_sw) (k - 1))
    (hcc4 : centralCorrect (node nw_sw nw_se sw_nw sw_ne) (k - 1))
    (hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1))
    (p : Int × Int)
    (hp : (2^k : Int) ≤ p.1 ∧ p.1 < (2^k : Int) + 2^((k - 1) + 1) ∧
          (2^k : Int) ≤ p.2 ∧ p.2 < (2^k : Int) + 2^((k - 1) + 1)) :
    isAlive (evolve (2^(k - 1)) (evolve (2^(k - 1))
        ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
          (0, 0)))) p
      = isAlive (evolve (2^(k - 1)) ((node R1 R2 R4 R5).toGrid (0, 0)))
          (p.1 - (2^k : Int) + (2^(k - 1) : Int),
           p.2 - (2^k : Int) + (2^(k - 1) : Int)) := by
  -- Step 1 (mechanical, proven): fold the LHS double half-step `2^(k-1) ∘ 2^(k-1)`
  -- into a single `evolve 2^k` over the parent grid. `evolve_half_step` is proven
  -- sorry-free (L2738); this is the trivial half of the agreement.
  rw [← evolve_half_step k hk1]
  -- Discharge the residual G3 goal via the named bridge `p4_nw_g3_bridge`
  -- (extraction #6724 c.745). The `exact` IS the specialization test (ai-01
  -- extraction protocol, DM msg-20260729T000329-m5ly00): it type-checks only
  -- because the bridge transports every call-site hypothesis — a false
  -- extraction (dropped hypothesis) would not close this goal.
  exact p4_nw_g3_bridge k hk1
    nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
    sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
    R1 R2 R4 R5 hR1 hR2 hR4 hR5
    hn1_l hn2_l hn4_l hn5_l hn1_w hn2_w hn4_w hn5_w
    hR1_l hR2_l hR4_l hR5_l hcc1 hcc2 hcc4 hcc5 p hp

/-- **nw membership arm (opaque-binder, sorry-free wiring — ai-01 option-a).**
    Discharges the nw quadrant of `p4_succ_membership` over OPAQUE wave-1
    results `R1..R5`, so this declaration gets a fresh 200000-heartbeat budget
    and the `p4_nw_shift_lemma.mp` fuel-align abstracts only the outer fuel
    (whnf-clean — proven by the `p4_nw_shift_consume_probe` crux, LAKE_EXIT=0).
    The `p4_succ_membership` call site then merely *applies* this arm with
    `R_i := hashlifeResultAux (k+1) n_i` (pure substitution, no whnf). The one
    residual sorry lives in `p4_nw_supercell_agree`; here everything is wired.

    Chain: `p4_nw_shift_lemma.mp` (supercell isAlive at `p'` + window bounds)
    → `mem_restrictGridTo` → `isAlive_true_iff_mem` + `evolve_half_step`
    (`2^k = 2^(k-1) ∘ 2^(k-1)`) + `p4_nw_supercell_agree` fold the membership
    into `hsup.1`; the four coordinate bounds discharge from the shift window
    (`2^((k-1)+1) = 2^k ≤ 2^(k+1)`) by omega. -/
private theorem p4_nw_membership_arm
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R1 R2 R4 R5 : MacroCell)
    (hR1 : R1 = hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
    (hR2 : R2 = hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
    (hR4 : R4 = hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
    (hR5 : R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
    (hn1_l : (node nw_nw nw_ne nw_sw nw_se).level = k + 1)
    (hn2_l : (node nw_ne ne_nw nw_se ne_sw).level = k + 1)
    (hn4_l : (node nw_sw nw_se sw_nw sw_ne).level = k + 1)
    (hn5_l : (node nw_se ne_sw sw_ne se_nw).level = k + 1)
    (hn1_w : (node nw_nw nw_ne nw_sw nw_se).wf = true)
    (hn2_w : (node nw_ne ne_nw nw_se ne_sw).wf = true)
    (hn4_w : (node nw_sw nw_se sw_nw sw_ne).wf = true)
    (hn5_w : (node nw_se ne_sw sw_ne se_nw).wf = true)
    (hR1_l : R1.level = k) (hR2_l : R2.level = k)
    (hR4_l : R4.level = k) (hR5_l : R5.level = k)
    (hR1_w : R1.wf = true) (hR2_w : R2.wf = true)
    (hR4_w : R4.wf = true) (hR5_w : R5.wf = true)
    (ih : ∀ (c' : MacroCell) (j : Nat), j < k → c'.wf = true → c'.level = j + 2 →
      centralCorrect c' j)
    (p : Int × Int)
    (hnw : p ∈ (hashlifeResultAux (k + 1) (node R1 R2 R4 R5)).toGrid
            ((2^k : Int), (2^k : Int))) :
    p ∈ restrictGridTo (evolve (2^k)
        ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
          (0, 0)))
        (2^k : Int) (2^(k+1)) := by
  -- Fuel-align (k+1) → (k-1)+2 on the OPAQUE-node membership, then consume the
  -- shift lemma's `.mp` (whnf-clean over opaque `R_i` — the probe-proven crux).
  rw [show (k + 1) = (k - 1) + 2 from by omega] at hnw
  have hsup := (p4_nw_shift_lemma k hk1 R1 R2 R4 R5
      hR1_l hR2_l hR4_l hR5_l hR1_w hR2_w hR4_w hR5_w ih p).mp hnw
  -- hsup.1 : isAlive (evolve 2^(k-1) ((node R1 R2 R4 R5).toGrid 0)) p' = true
  -- hsup.2 : 2^k ≤ p.1 ∧ p.1 < 2^k + 2^((k-1)+1) ∧ 2^k ≤ p.2 ∧ p.2 < 2^k + 2^((k-1)+1)
  rw [mem_restrictGridTo]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- membership: fold `evolve 2^k` via half-step + supercell agreement into hsup.1
    rw [← isAlive_true_iff_mem_local]
    rw [evolve_half_step k hk1]
    -- S4 exige que chaque résultat wave-1 calcule bien le demi-pas de SON nœud :
    -- c'est `centralCorrect n_i (k-1)`, obtenu de `ih` (niveau `k+1 = (k-1)+2`,
    -- `k-1 < k` par `hk1`). Sans ces quatre faits l'énoncé de S4 est faux — cf.
    -- le contre-exemple `emptyOfLevel` documenté sur `p4_nw_supercell_agree`.
    have hcc1 : centralCorrect (node nw_nw nw_ne nw_sw nw_se) (k - 1) :=
      ih _ (k - 1) (by omega) hn1_w (by rw [hn1_l]; omega)
    have hcc2 : centralCorrect (node nw_ne ne_nw nw_se ne_sw) (k - 1) :=
      ih _ (k - 1) (by omega) hn2_w (by rw [hn2_l]; omega)
    have hcc4 : centralCorrect (node nw_sw nw_se sw_nw sw_ne) (k - 1) :=
      ih _ (k - 1) (by omega) hn4_w (by rw [hn4_l]; omega)
    have hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1) :=
      ih _ (k - 1) (by omega) hn5_w (by rw [hn5_l]; omega)
    rw [p4_nw_supercell_agree k hk1
          nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
          sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
          R1 R2 R4 R5 hR1 hR2 hR4 hR5
          hn1_l hn2_l hn4_l hn5_l hn1_w hn2_w hn4_w hn5_w
          hR1_l hR2_l hR4_l hR5_l hcc1 hcc2 hcc4 hcc5 p hsup.2]
    exact hsup.1
  · -- 2^k ≤ p.1
    exact hsup.2.1
  · -- p.1 < 2^k + 2^(k+1)  (from shift window p.1 < 2^k + 2^k, and 2^k ≤ 2^(k+1))
    have hb := hsup.2.2.1
    have he : (k - 1) + 1 = k := by omega
    rw [he] at hb
    have hbridge : ((2 ^ (k + 1) : Nat) : Int) = 2 ^ k + 2 ^ k := by
      push_cast; rw [pow_succ]; ring
    have hpos : (0 : Int) < 2 ^ k := pow_pos (by norm_num) k
    rw [hbridge]
    omega
  · -- 2^k ≤ p.2
    exact hsup.2.2.2.1
  · -- p.2 < 2^k + 2^(k+1)
    have hb := hsup.2.2.2.2
    have he : (k - 1) + 1 = k := by omega
    rw [he] at hb
    have hbridge : ((2 ^ (k + 1) : Nat) : Int) = 2 ^ k + 2 ^ k := by
      push_cast; rw [pow_succ]; ring
    have hpos : (0 : Int) < 2 ^ k := pow_pos (by norm_num) k
    rw [hbridge]
    omega

/-- **NW membership arm, reciprocal direction (mpr assembly).**
    Mirror of `p4_nw_membership_arm` for the `mpr` case of
    `p4_succ_membership`: FROM the global cell-state `hmem` (the RHS
    membership under `evolve 2^k`) plus the NW-quadrant router bounds
    `hp1..hp4` (from `quad_partition_bounds`), TO the node-quadrant
    membership at anchor `(2^k, 2^k)`. All ingredients are the mp arm's,
    consumed backwards: `p4_nw_shift_lemma.mpr` needs (a) the shift window
    (from `hp1..hp4`, since `2^((k-1)+1) = 2^k`) and (b) the supercell
    `isAlive` at the shifted point — obtained from `hmem` by folding
    `evolve 2^k` into the double half-step (`evolve_half_step`) and crossing
    `p4_nw_supercell_agree` RIGHT-to-LEFT (`rw [← …]`; the agreement is a
    Bool equation, hence reversible — a sorried agreement stays usable in
    `rw`, so this wiring is textually sorry-free for all four quadrants). -/
private theorem p4_nw_membership_arm_rev
    (k : Nat) (hk1 : 1 ≤ k)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
     sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (R1 R2 R4 R5 : MacroCell)
    (hR1 : R1 = hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
    (hR2 : R2 = hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
    (hR4 : R4 = hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
    (hR5 : R5 = hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
    (hn1_l : (node nw_nw nw_ne nw_sw nw_se).level = k + 1)
    (hn2_l : (node nw_ne ne_nw nw_se ne_sw).level = k + 1)
    (hn4_l : (node nw_sw nw_se sw_nw sw_ne).level = k + 1)
    (hn5_l : (node nw_se ne_sw sw_ne se_nw).level = k + 1)
    (hn1_w : (node nw_nw nw_ne nw_sw nw_se).wf = true)
    (hn2_w : (node nw_ne ne_nw nw_se ne_sw).wf = true)
    (hn4_w : (node nw_sw nw_se sw_nw sw_ne).wf = true)
    (hn5_w : (node nw_se ne_sw sw_ne se_nw).wf = true)
    (hR1_l : R1.level = k) (hR2_l : R2.level = k)
    (hR4_l : R4.level = k) (hR5_l : R5.level = k)
    (hR1_w : R1.wf = true) (hR2_w : R2.wf = true)
    (hR4_w : R4.wf = true) (hR5_w : R5.wf = true)
    (ih : ∀ (c' : MacroCell) (j : Nat), j < k → c'.wf = true → c'.level = j + 2 →
      centralCorrect c' j)
    (p : Int × Int)
    (hmem : p ∈ evolve (2^k)
        ((node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
               (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).toGrid
          (0, 0)))
    (hp1 : (2^k : Int) ≤ p.1) (hp2 : p.1 < (2^k : Int) + 2^k)
    (hp3 : (2^k : Int) ≤ p.2) (hp4 : p.2 < (2^k : Int) + 2^k) :
    p ∈ (hashlifeResultAux (k + 1) (node R1 R2 R4 R5)).toGrid
        ((2^k : Int), (2^k : Int)) := by
  -- Fuel-align (k+1) → (k-1)+2 on the GOAL, then enter through the shift
  -- lemma's `.mpr` (whnf-clean over opaque `R_i`, fresh budget).
  rw [show (k + 1) = (k - 1) + 2 from by omega]
  have he : (k - 1) + 1 = k := by omega
  have hw : (2^k : Int) ≤ p.1 ∧ p.1 < (2^k : Int) + 2^((k - 1) + 1) ∧
            (2^k : Int) ≤ p.2 ∧ p.2 < (2^k : Int) + 2^((k - 1) + 1) := by
    rw [he]
    exact ⟨hp1, by omega, hp3, by omega⟩
  refine (p4_nw_shift_lemma k hk1 R1 R2 R4 R5
      hR1_l hR2_l hR4_l hR5_l hR1_w hR2_w hR4_w hR5_w ih p).mpr ⟨?_, hw⟩
  -- Residual: the supercell isAlive at the shifted point. Fold it back into
  -- `hmem` via the supercell agreement (Bool equation, consumed R-to-L) +
  -- the half-step composition, then the isAlive/mem bridge.
  have hcc1 : centralCorrect (node nw_nw nw_ne nw_sw nw_se) (k - 1) :=
    ih _ (k - 1) (by omega) hn1_w (by rw [hn1_l]; omega)
  have hcc2 : centralCorrect (node nw_ne ne_nw nw_se ne_sw) (k - 1) :=
    ih _ (k - 1) (by omega) hn2_w (by rw [hn2_l]; omega)
  have hcc4 : centralCorrect (node nw_sw nw_se sw_nw sw_ne) (k - 1) :=
    ih _ (k - 1) (by omega) hn4_w (by rw [hn4_l]; omega)
  have hcc5 : centralCorrect (node nw_se ne_sw sw_ne se_nw) (k - 1) :=
    ih _ (k - 1) (by omega) hn5_w (by rw [hn5_l]; omega)
  rw [← p4_nw_supercell_agree k hk1
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
        R1 R2 R4 R5 hR1 hR2 hR4 hR5
        hn1_l hn2_l hn4_l hn5_l hn1_w hn2_w hn4_w hn5_w
        hR1_l hR2_l hR4_l hR5_l hcc1 hcc2 hcc4 hcc5 p hw]
  rw [← evolve_half_step k hk1]
  rw [isAlive_true_iff_mem_local]
  exact hmem

end Life
end Conway
