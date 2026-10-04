/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Gabriel Dahia
Adapté à `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

Le source Dahia original vit dans le dépôt `gdahia/Komlos` (module
`Komlos/Split.lean`, toolchain v4.34.0, cadre `Finsupp` sur `E →₀ ℝ`). Dans
le cadre `Finsupp` du papier, la « borne du support » n'existe pas : une
fonction est nulle hors de son support, et toute ré-indexation par
translation est exacte sans hypothèse.

L'adaptation **Finset explicite** du lake a remplacé cette gratuité par des
hypothèses d'**invariance** du support (`S.image (fun x => x + u) = S`) dans
les briques k1.2, k1.4, k1.5 et k1.6. Ce module **démontre que ce choix est
insatisfiable** : sur un `Finset` non vide de `ℤ^d` (groupe sans torsion),
l'invariance par un décalage non nul est impossible (`eq_zero_of_image_add_eq_self`,
par argument d'orbite et tirage de pigeon). Les lemmes des briques k1.* sont
donc *vrais* mais **inutilisables aux décalages non nuls** — précisément ceux
que le Lemme 1.4 consomme (`6 • v i`, `3 • v (Fin.last n)`).

**Portée de ce commit** (brique k1.7, `lake build SUCCESS` requis, 0
`sorry`) :

L'hypothèse **satisfiable** qui remplace l'invariance : la **contention de
support** `SupportContained S P A` — `S` contient le support de `P` et tous
ses translatés par les décalages de `A`. Le module redémontre sous cette
hypothèse les quatre identités consommées par k2 : la ré-indexation par
translation (`sum_comp_add_eq_sum_of_support`), la préservation de la masse
par la scission (`split_mass_of_support`), l'identité pivot
(`overlap_translate_eq_one_sub_shiftDistance_of_support`) et le Claim 3.2
(`shiftDistanceProd_split_le_of_support`). Le module démontre aussi la
**non-vacuité** de la nouvelle hypothèse (`supportContained_biUnion`).

Les briques k1.2/k1.4/k1.5/k1.6 restent en place (leurs énoncés sont vrais) ;
ce module **ajoute** les énoncés consommables. L'état détaillé vit dans
`FORMAL_STATUS.md`.
-/

import Discrepancy.Komlos.SplitBit
import Discrepancy.Komlos.SplitDistance

/-!
# Contention de support : l'hypothèse consommable des identités k1

Ce module remplace l'hypothèse d'invariance du support des briques k1.2–k1.6
— satisfiable seulement au décalage nul sur un `Finset` de `ℤ^d` — par la
**contention de support** : `S` contient le support de `P` et les translatés
pertinents de celui-ci. Sous cette hypothèse, les sommes de `P` et de ses
translatées sur `S` valent toutes la masse de `P`, et les identités des
briques k1 se redémontrent sans invariance.

C'est la forme adaptée du papier : sur le réseau entier, la décroissance
hors-support remplace la contention ; dans le cadre `Finset` explicite du
lake, c'est `S` qui doit contenir tous les translatés utiles.
-/

namespace Discrepancy.Komlos

/-- **Contention de support** : `S` contient le support de `P` et tous ses
translatés par les décalages de `A`. C'est l'hypothèse **satisfiable** qui
remplace l'invariance `S.image (fun x => x + u) = S` des briques k1.2–k1.6
— insatisfiable pour `u ≠ 0` sur un `Finset` non vide de `ℤ^d`, cf
`eq_zero_of_image_add_eq_self`. -/
def SupportContained {d : ℕ} (S : Finset (Fin d → ℤ)) (P : (Fin d → ℤ) → ℝ)
    (A : Finset (Fin d → ℤ)) : Prop :=
  ∀ z, P z ≠ 0 → ∀ w ∈ A, z + w ∈ S

/-- **Le défaut d'hypothèse, démontré** : sur un `Finset` non vide de `ℤ^d`,
l'invariance `S.image (fun x => x + u) = S` force `u = 0`. La preuve est
l'argument d'orbite — `x`, `x + u`, `x + 2u`, … restent dans `S` — clos par
tirage de pigeon sur `S.card + 1` termes, puis annulation dans le groupe
sans torsion. Conséquence : les hypothèses d'invariance portées par k1.2
(`split_mass`), k1.4 (pivot), k1.5 (Claim 3.2) et k1.6 (`splitBit_eq`) ne
sont satisfiables qu'au décalage nul, alors que le Lemme 1.4 les instancie
à `6 • v i` et `3 • v (Fin.last n)`. -/
theorem eq_zero_of_image_add_eq_self {d : ℕ} {S : Finset (Fin d → ℤ)}
    {u : Fin d → ℤ} (hS : S.image (fun x => x + u) = S) (hne : S.Nonempty) :
    u = 0 := by
  obtain ⟨x, hx⟩ := hne
  -- L'orbite `x + k • u` reste dans `S`.
  have horbit : ∀ k : ℕ, x + (k : ℤ) • u ∈ S := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      have hmem : x + (k : ℤ) • u + u ∈ S.image (fun y => y + u) :=
        Finset.mem_image.mpr ⟨x + (k : ℤ) • u, ih, rfl⟩
      rw [hS] at hmem
      have hstep : ((k + 1 : ℕ) : ℤ) • u = (k : ℤ) • u + u := by
        rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
      rw [hstep]
      simpa [add_assoc] using hmem
  -- Tirage de pigeon : deux indices distincts donnent le même point.
  obtain ⟨i, _, j, _, hij, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := (Finset.univ : Finset (Fin (S.card + 1)))) (t := S)
      (f := fun k : Fin (S.card + 1) => x + (k : ℤ) • u)
      (by rw [Finset.card_univ, Fintype.card_fin]; exact Nat.lt_succ_self _)
      (fun k _ => horbit k)
  have hcancel : (i : ℤ) • u = (j : ℤ) • u := add_left_cancel heq
  have hsub : ((i : ℤ) - (j : ℤ)) • u = 0 := by
    rw [sub_smul, hcancel, sub_self]
  have hne' : (i : ℤ) - (j : ℤ) ≠ 0 := by
    intro h0
    refine hij (Fin.ext ?_)
    exact_mod_cast (sub_eq_zero.mp h0)
  -- Groupe sans torsion : le coefficient non nul force `u = 0`, coordonnée par coordonnée.
  funext i'
  have hcoord : ((i : ℤ) - (j : ℤ)) * u i' = 0 := by
    have := congrFun hsub i'
    simpa using this
  rcases mul_eq_zero.mp hcoord with h | h
  · exact absurd h hne'
  · exact h

/-- **Non-vacuité de la contention** : toute fonction admettant un support fini
`S₀` admet un `S` qui contient le support et ses translatés par `A` — l'union
de `S₀` et de ses translatés. C'est le contrôle positif qui manquait aux
hypothèses d'invariance de k1.*. -/
theorem supportContained_biUnion {d : ℕ} {P : (Fin d → ℤ) → ℝ}
    {S₀ : Finset (Fin d → ℤ)} {A : Finset (Fin d → ℤ)}
    (h : ∀ z, P z ≠ 0 → z ∈ S₀) :
    SupportContained (S₀ ∪ A.biUnion (fun w => S₀.image (fun z => z + w))) P A := by
  intro z hz w hw
  exact Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_image.mpr ⟨z, h z hz, rfl⟩⟩)

/-- **Ré-indexation par translation sous contention** : si `S` contient le
support de `P` et de `P ∘ (· + v)`, alors `∑ x ∈ S, P (x + v) = ∑ x ∈ S, P x`
(both equal the mass of `P`). C'est le remplacement satisfiable de
`sum_translate_image` (k1.2) : les trois sommes — sur l'image translatée, sur
l'intersection et sur `S` — coïncident parce que les termes hors support
s'annulent. -/
theorem sum_comp_add_eq_sum_of_support {d : ℕ} {P : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)} {v : Fin d → ℤ}
    (hsp : ∀ z, P z ≠ 0 → z ∈ S) (hsm : ∀ z, P z ≠ 0 → z - v ∈ S) :
    ∑ x ∈ S, P (x + v) = ∑ x ∈ S, P x := by
  have hinj : ∀ a ∈ S, ∀ b ∈ S, a + v = b + v → a = b :=
    fun a _ b _ hab => add_right_cancel hab
  have h1 : ∑ y ∈ S ∩ S.image (fun x => x + v), P y
      = ∑ y ∈ S.image (fun x => x + v), P y := by
    apply Finset.sum_subset Finset.inter_subset_right
    intro y hy hyi
    by_contra hz
    exact hyi (Finset.mem_inter.mpr ⟨hsp y hz, hy⟩)
  have h2 : ∑ y ∈ S ∩ S.image (fun x => x + v), P y = ∑ y ∈ S, P y := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro y hy hyi
    by_contra hz
    refine hyi (Finset.mem_inter.mpr ⟨hy, ?_⟩)
    exact Finset.mem_image.mpr ⟨y - v, hsm y hz, by simp⟩
  calc ∑ x ∈ S, P (x + v)
      = ∑ y ∈ S.image (fun x => x + v), P y := (Finset.sum_image hinj).symm
    _ = ∑ y ∈ S ∩ S.image (fun x => x + v), P y := h1.symm
    _ = ∑ x ∈ S, P x := h2

/-- Monotonie de la contention en l'ensemble de décalages : un `S` qui contient
les translatés par `A` les contient par toute partie de `A`. -/
lemma SupportContained.mono {d : ℕ} {S : Finset (Fin d → ℤ)} {P : (Fin d → ℤ) → ℝ}
    {A B : Finset (Fin d → ℤ)} (h : SupportContained S P B) (hAB : A ⊆ B) :
    SupportContained S P A :=
  fun z hz w hw => h z hz w (hAB hw)

/-- **Ré-indexation produit sous contention** : la version k1.5 de
`sum_comp_add_eq_sum_of_support` — pour `Q` sur `S × Bool` dont le support et
son translaté de première coordonnée sont contenus dans `S`, la somme de
`Q ∘ (· + (u, 0))` sur `S × univ` vaut celle de `Q`. -/
theorem sum_prodSnd_eq_sum_of_support {d : ℕ} {Q : (Fin d → ℤ) × Bool → ℝ}
    {S : Finset (Fin d → ℤ)} {u : Fin d → ℤ}
    (hsp : ∀ y, Q y ≠ 0 → y.1 ∈ S) (hsm : ∀ y, Q y ≠ 0 → y.1 - u ∈ S) :
    ∑ y ∈ S ×ˢ (Finset.univ : Finset Bool), Q (y.1 + u, y.2)
      = ∑ y ∈ S ×ˢ (Finset.univ : Finset Bool), Q y := by
  have hinj : ∀ a ∈ S ×ˢ (Finset.univ : Finset Bool),
      ∀ b ∈ S ×ˢ (Finset.univ : Finset Bool),
      (a.1 + u, a.2) = (b.1 + u, b.2) → a = b := by
    intro a _ b _ hab
    rw [Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    rw [Prod.mk.injEq]
    exact ⟨add_right_cancel h1, h2⟩
  have h1 : ∑ z ∈ (S ×ˢ (Finset.univ : Finset Bool))
        ∩ (S ×ˢ (Finset.univ : Finset Bool)).image (fun y => (y.1 + u, y.2)), Q z
      = ∑ z ∈ (S ×ˢ (Finset.univ : Finset Bool)).image (fun y => (y.1 + u, y.2)), Q z := by
    apply Finset.sum_subset Finset.inter_subset_right
    intro z hz hzi
    by_contra hz0
    exact hzi (Finset.mem_inter.mpr ⟨Finset.mem_product.mpr
      ⟨hsp z hz0, Finset.mem_univ _⟩, hz⟩)
  have h2 : ∑ z ∈ (S ×ˢ (Finset.univ : Finset Bool))
        ∩ (S ×ˢ (Finset.univ : Finset Bool)).image (fun y => (y.1 + u, y.2)), Q z
      = ∑ z ∈ S ×ˢ (Finset.univ : Finset Bool), Q z := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro z hz hzi
    by_contra hz0
    refine hzi (Finset.mem_inter.mpr ⟨hz, ?_⟩)
    exact Finset.mem_image.mpr ⟨(z.1 - u, z.2), Finset.mem_product.mpr
      ⟨hsm z hz0, Finset.mem_univ _⟩, by simp⟩
  calc ∑ y ∈ S ×ˢ (Finset.univ : Finset Bool), Q (y.1 + u, y.2)
      = ∑ z ∈ (S ×ˢ (Finset.univ : Finset Bool)).image (fun y => (y.1 + u, y.2)), Q z :=
        (Finset.sum_image hinj).symm
    _ = ∑ z ∈ (S ×ˢ (Finset.univ : Finset Bool))
          ∩ (S ×ˢ (Finset.univ : Finset Bool)).image (fun y => (y.1 + u, y.2)), Q z :=
        h1.symm
    _ = ∑ y ∈ S ×ˢ (Finset.univ : Finset Bool), Q y := h2

/-- **Identité pivot produit sous masses** : la forme k1.5, avec les deux masses
en hypothèses au lieu de l'invariance du support — `Δ(Q, (u, 0)) = 1 −`
recouvrement avec la translatée, dès que `Q` et sa translatée ont masse 1. -/
theorem shiftDistanceProd_eq_one_sub_overlap_of_mass {d : ℕ}
    {Q : (Fin d → ℤ) × Bool → ℝ} {T : Finset ((Fin d → ℤ) × Bool)}
    (hmass : ∑ y ∈ T, Q y = 1) {u : Fin d → ℤ}
    (htr : ∑ y ∈ T, Q (y.1 + u, y.2) = 1) :
    shiftDistanceProd T Q u = 1 - overlapProd Q (fun y => Q (y.1 + u, y.2)) T := by
  have hmin : ∀ y ∈ T, min (Q y) (Q (y.1 + u, y.2))
      = (1 / 2 : ℝ) * (Q y + Q (y.1 + u, y.2) - |Q (y.1 + u, y.2) - Q y|) := by
    intro y _
    rw [min_eq_half_add_sub_abs, abs_sub_comm]
  have hsum : ∑ y ∈ T, (Q y + Q (y.1 + u, y.2) - |Q (y.1 + u, y.2) - Q y|)
      = (∑ y ∈ T, Q y) + (∑ y ∈ T, Q (y.1 + u, y.2)) - ∑ y ∈ T, |Q (y.1 + u, y.2) - Q y| := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  unfold overlapProd shiftDistanceProd
  rw [Finset.sum_congr rfl hmin, ← Finset.mul_sum, hsum, hmass, htr]
  ring

/-- **Préservation de la masse par la scission, sous contention** : la version
consommable de `split_mass` (k1.2) — `S` doit contenir le support de `P` et ses
translatés par `±v`, l'invariance `S.image (· ± v) = S` étant insatisfiable
pour `v ≠ 0` (`eq_zero_of_image_add_eq_self`). -/
theorem split_mass_of_support {d : ℕ} (v : Fin d → ℤ) {P : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)}
    (hS : SupportContained S P ({0, v, -v} : Finset (Fin d → ℤ))) :
    ∑ y ∈ S ×ˢ (Finset.univ : Finset Bool), split v P y = ∑ x ∈ S, P x := by
  have key : ∀ x ∈ S, split v P (x, false) + split v P (x, true)
      = (P (x + v) + P (x - v)) * (1 / 2 : ℝ) := by
    intro x _
    rw [split_apply_zero, split_apply_one, ← mul_add, max_add_min, mul_comm]
  have hbool : ∀ x ∈ S, ∑ y ∈ (Finset.univ : Finset Bool), split v P (x, y)
      = split v P (x, false) + split v P (x, true) := by
    intro x _
    simp
    ac_rfl
  have hpv : ∑ x ∈ S, P (x + v) = ∑ x ∈ S, P x :=
    sum_comp_add_eq_sum_of_support (P := P) (v := v)
      (fun z hz => by simpa using hS z hz 0 (by simp))
      (fun z hz => by
        have := hS z hz (-v) (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
        simpa [sub_eq_add_neg] using this)
  have hmv : ∑ x ∈ S, P (x - v) = ∑ x ∈ S, P x :=
    sum_comp_add_eq_sum_of_support (P := P) (v := -v)
      (fun z hz => by simpa using hS z hz 0 (by simp))
      (fun z hz => by
        have := hS z hz v (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
        simpa [sub_neg_eq_add] using this)
  rw [Finset.sum_product, Finset.sum_congr rfl hbool,
    Finset.sum_congr rfl key, ← Finset.sum_mul, Finset.sum_add_distrib, hpv, hmv]
  linarith

/-- **Identité pivot sous contention** : la version consommable de
`overlap_translate_eq_one_sub_shiftDistance` (k1.4) — masse 1 et `S`
contenant le support de `P` et son translaté par `−u` suffisent : sous ces
hypothèses les deux masses valent 1 et l'identité ponctuelle du minimum
télescope comme dans k1.4. -/
theorem overlap_translate_eq_one_sub_shiftDistance_of_support {d : ℕ}
    {P : (Fin d → ℤ) → ℝ} {S : Finset (Fin d → ℤ)}
    (hmass : ∑ x ∈ S, P x = 1) {u : Fin d → ℤ}
    (hP : SupportContained S P ({0, -u} : Finset (Fin d → ℤ))) :
    overlap P (fun x => P (x + u)) S = 1 - shiftDistance S P u := by
  have htr : ∑ x ∈ S, P (x + u) = 1 := by
    rw [sum_comp_add_eq_sum_of_support (P := P) (v := u)
      (fun z hz => by simpa using hP z hz 0 (by simp))
      (fun z hz => by
        have := hP z hz (-u) (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
        simpa [sub_eq_add_neg] using this), hmass]
  have hmin : ∀ x ∈ S, min (P x) (P (x + u))
      = (1 / 2 : ℝ) * (P x + P (x + u) - |P (x + u) - P x|) := by
    intro x _
    rw [min_eq_half_add_sub_abs, abs_sub_comm]
  have hsum : ∑ x ∈ S, (P x + P (x + u) - |P (x + u) - P x|)
      = (∑ x ∈ S, P x) + (∑ x ∈ S, P (x + u)) - ∑ x ∈ S, |P (x + u) - P x| := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  unfold overlap shiftDistance
  rw [Finset.sum_congr rfl hmin, ← Finset.mul_sum, hsum, hmass, htr]
  ring

/-- Forme symétrique de l'identité pivot sous contention. -/
theorem shiftDistance_eq_one_sub_overlap_of_support {d : ℕ}
    {P : (Fin d → ℤ) → ℝ} {S : Finset (Fin d → ℤ)}
    (hmass : ∑ x ∈ S, P x = 1) {u : Fin d → ℤ}
    (hP : SupportContained S P ({0, -u} : Finset (Fin d → ℤ))) :
    shiftDistance S P u = 1 - overlap P (fun x => P (x + u)) S := by
  rw [overlap_translate_eq_one_sub_shiftDistance_of_support hmass hP]
  ring

/-- **Claim 3.2 sous contention** : la version consommable de
`shiftDistanceProd_split_le` (k1.5) — la scission ne fait pas croître la
distance de translation dans les directions de la base, sous masse 1,
positivité de `P` et contention par les six décalages
`0, ±v, −u, v−u, −v−u` (ceux du support et de son translaté, et de leurs
scissions). Les décalages `±v − u` sont ceux qui portent `supp T_v P − (u,0)`
dans `S` ; `−(v+v)` n'y figure pas : la scission ne le consomme pas. -/
theorem shiftDistanceProd_split_le_of_support {d : ℕ} (v u : Fin d → ℤ)
    {P : (Fin d → ℤ) → ℝ} {S : Finset (Fin d → ℤ)}
    (hP0 : ∀ x, 0 ≤ P x)
    (hmass : ∑ x ∈ S, P x = 1)
    (hP : SupportContained S P
      ({0, v, -v, -u, v - u, -v - u} : Finset (Fin d → ℤ))) :
    shiftDistanceProd (S ×ˢ (Finset.univ : Finset Bool)) (split v P) u
      ≤ shiftDistance S P u := by
  have mono3 : SupportContained S P ({0, v, -v} : Finset (Fin d → ℤ)) :=
    hP.mono (by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
      tauto)
  have hPiv : SupportContained S P ({0, -u} : Finset (Fin d → ℤ)) :=
    hP.mono (by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
      tauto)
  -- Le support de `T_v P` et celui de son translaté vivent dans `S × univ`.
  have hsupp : ∀ (x : Fin d → ℤ) (b : Bool), split v P (x, b) ≠ 0 →
      P (x + v) ≠ 0 ∨ P (x - v) ≠ 0 := by
    intro x b hy
    cases b with
    | false =>
      rw [split_apply_zero] at hy
      have hmax : max (P (x + v)) (P (x - v)) ≠ 0 :=
        fun h0 => hy (by rw [h0, mul_zero])
      by_contra h
      push_neg at h
      exact hmax (by rw [h.1, h.2, max_self])
    | true =>
      rw [split_apply_one] at hy
      have hmin : min (P (x + v)) (P (x - v)) ≠ 0 :=
        fun h0 => hy (by rw [h0, mul_zero])
      by_contra h
      push_neg at h
      exact hmin (by rw [h.1, h.2, min_self])
  have hQT : ∀ y, split v P y ≠ 0 → y.1 ∈ S := by
    intro y hy
    obtain ⟨x, b⟩ := y
    rcases hsupp x b hy with h | h
    · have := hP (x + v) h (-v)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      simpa [add_assoc, add_neg_cancel] using this
    · have := hP (x - v) h v
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      simpa [sub_eq_add_neg, add_assoc, add_neg_cancel] using this
  have hQTu : ∀ y, split v P y ≠ 0 → y.1 - u ∈ S := by
    intro y hy
    obtain ⟨x, b⟩ := y
    rcases hsupp x b hy with h | h
    · have := hP (x + v) h (-v - u)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      simpa [sub_eq_add_neg, add_assoc, add_neg_cancel] using this
    · have := hP (x - v) h (v - u)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      simpa [sub_eq_add_neg, add_assoc, add_neg_cancel] using this
  have hmassT : ∑ y ∈ S ×ˢ (Finset.univ : Finset Bool), split v P y = 1 := by
    rw [split_mass_of_support v mono3, hmass]
  have hmassTr : ∑ y ∈ S ×ˢ (Finset.univ : Finset Bool),
      split v P (y.1 + u, y.2) = 1 := by
    rw [sum_prodSnd_eq_sum_of_support hQT hQTu, hmassT]
  rw [shiftDistanceProd_eq_one_sub_overlap_of_mass hmassT hmassTr,
    shiftDistance_eq_one_sub_overlap_of_support hmass hPiv, ← split_tr v u P,
    sub_le_sub_iff_left]
  calc overlap P (fun x => P (x + u)) S
      = ∑ x ∈ S, min (P x) (P (x + u)) := rfl
    _ = ∑ y ∈ S ×ˢ (Finset.univ : Finset Bool),
          split v (fun x => min (P x) (P (x + u))) y :=
        (split_mass_of_support v (P := fun x => min (P x) (P (x + u)))
          (fun z hz w hw => hP z
            (fun h0 => hz (show min (P z) (P (z + u)) = 0 from by rw [h0, min_eq_left (hP0 (z + u))])) w
            (by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
              tauto))).symm
    _ ≤ overlapProd (split v P) (split v (fun x => P (x + u)))
          (S ×ˢ (Finset.univ : Finset Bool)) := by
        apply sum_le_overlap_prod
        · intro y _
          exact split_mono v (fun x => min_le_left (P x) (P (x + u))) y
        · intro y _
          exact split_mono v (fun x => min_le_right (P x) (P (x + u))) y

/-- **Identité du bit de scission sous contention** : la version consommable de
`splitBit_eq` (k1.6) — `splitBit v P S = ½(1 − Δ(P, 2v))` sous masse 1 et
contention par `0, ±v, −v−v` (les deux graphies `-v - v` et `-(v + v)` sont
portées : Lean ne les identifie pas syntaxiquement, et l'un des sites
consomme la première, le pivot la seconde). -/
lemma splitBit_eq_of_support {d : ℕ} (v : Fin d → ℤ) {P : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)} (hP0 : ∀ x, 0 ≤ P x)
    (hmass : ∑ x ∈ S, P x = 1)
    (hP : SupportContained S P
      ({0, v, -v, -v - v, -(v + v)} : Finset (Fin d → ℤ))) :
    splitBit v P S = (1 / 2 : ℝ) * (1 - shiftDistance S P (v + v)) := by
  have hPiv : SupportContained S P ({0, -(v + v)} : Finset (Fin d → ℤ)) :=
    fun z hz w hw => hP z hz w (by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
      tauto)
  have hf : ∀ z, min (P z) (P (z + (v + v))) ≠ 0 → z ∈ S := by
    intro z hz
    have hPz : P z ≠ 0 :=
      fun h0 => hz (by rw [h0, min_eq_left (hP0 (z + (v + v)))])
    simpa using hP z hPz 0 (by simp)
  have hfm : ∀ z, min (P z) (P (z + (v + v))) ≠ 0 → z - (-v) ∈ S := by
    intro z hz
    have hPz2 : P (z + (v + v)) ≠ 0 :=
      fun h0 => hz (by rw [h0, min_eq_right (hP0 z)])
    have hmem' := hP (z + (v + v)) hPz2 (-v)
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
    simpa [sub_neg_eq_add, add_assoc, add_neg_cancel] using hmem'
  have htr : overlap (fun x => P (x + v)) (fun x => P (x - v)) S
      = overlap P (fun x => P (x + (v + v))) S := by
    unfold overlap
    dsimp only
    rw [← sum_comp_add_eq_sum_of_support
      (P := fun x => min (P x) (P (x + (v + v)))) (v := -v) hf hfm]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h1 : x + -v + (v + v) = x + v := by abel
    rw [h1]
    exact min_comm _ _
  unfold splitBit
  rw [htr, overlap_translate_eq_one_sub_shiftDistance_of_support hmass hPiv]

end Discrepancy.Komlos
