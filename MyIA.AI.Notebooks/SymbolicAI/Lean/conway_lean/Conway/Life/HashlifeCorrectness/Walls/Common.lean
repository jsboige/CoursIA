/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Conway.Life.HashlifeCorrectness.Walls.Common

Sub-module of `Conway.Life.HashlifeCorrectness`. Phase 3b multi-agent
prover targets (Epic #1453). Scope: /-! ## P4 (a) — the named overlap wall
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

end Life
end Conway
