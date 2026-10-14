/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Gabriel Dahia
Adapted to `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, i18n convention #4980.

The original Dahia source lives in the repository `gdahia/Komlos` (module
`Komlos/Split.lean`, toolchain v4.34.0, `Finsupp` framework over `E →₀ ℝ`). In
the paper's `Finsupp` framework there is no "support bound" : a function
vanishes outside its support, and every re-indexing by translation is exact
without any hypothesis.

The **explicit Finset** adaptation of the lake replaced that for free by
**invariance** hypotheses on the support (`S.image (fun x => x + u) = S`) in
bricks k1.2, k1.4, k1.5 and k1.6. This module **proves that this choice is
unsatisfiable** : on a nonempty `Finset` of `ℤ^d` (a torsion-free group),
invariance under a nonzero shift is impossible (`eq_zero_of_image_add_eq_self`,
by an orbit argument and a pigeonhole draw). The lemmas of the k1.* bricks are
therefore *true* but **unusable at nonzero shifts** — precisely those the
Lemma 1.4 consumes (`6 • v i`, `3 • v (Fin.last n)`).

**Scope of this commit** (brick k1.7, `lake build SUCCESS` required, 0
`sorry`) :

The **satisfiable** hypothesis replacing invariance : **support containment**
`SupportContained S P A` — `S` contains the support of `P` and all its
translates by the shifts of `A`. The module reproves under this hypothesis the
four identities consumed by k2 : the re-indexing by translation
(`sum_comp_add_eq_sum_of_support`), the preservation of mass by the splitting
(`split_mass_of_support`), the pivot identity
(`overlap_translate_eq_one_sub_shiftDistance_of_support`) and Claim 3.2
(`shiftDistanceProd_split_le_of_support`), plus the consumable form of the
splitting-bit identity (`splitBit_eq_of_support`). The module also proves the
**non-vacuity** of the new hypothesis (`supportContained_biUnion`).

Bricks k1.2/k1.4/k1.5/k1.6 remain in place (their statements are true) ; this
module **adds** the consumable statements. The detailed state lives in
`FORMAL_STATUS.md`.
-/

import Discrepancy.Komlos.SplitBit_en
import Discrepancy.Komlos.SplitDistance_en

/-!
# Support containment : the consumable hypothesis of the k1 identities

This module replaces the support-invariance hypothesis of bricks k1.2–k1.6 —
satisfiable only at the zero shift on a `Finset` of `ℤ^d` — by **support
containment** : `S` contains the support of `P` and the relevant translates of
it. Under this hypothesis the sums of `P` and of its translates over `S` all
equal the mass of `P`, and the identities of the k1 bricks are reproved without
invariance.

This is the adapted form of the paper : on the integer lattice, decay
off-support replaces containment ; in the explicit `Finset` framework of the
lake, it is `S` that must contain all the useful translates.
-/

namespace Discrepancy.Komlos_en

/-- **Support containment** : `S` contains the support of `P` and all its
translates by the shifts of `A`. This is the **satisfiable** hypothesis that
replaces the invariance `S.image (fun x => x + u) = S` of bricks k1.2–k1.6 —
unsatisfiable for `u ≠ 0` on a nonempty `Finset` of `ℤ^d`, cf
`eq_zero_of_image_add_eq_self`. -/
def SupportContained {d : ℕ} (S : Finset (Fin d → ℤ)) (P : (Fin d → ℤ) → ℝ)
    (A : Finset (Fin d → ℤ)) : Prop :=
  ∀ z, P z ≠ 0 → ∀ w ∈ A, z + w ∈ S

/-- **The hypothesis defect, proved** : on a nonempty `Finset` of `ℤ^d`, the
invariance `S.image (fun x => x + u) = S` forces `u = 0`. The proof is the
orbit argument — `x`, `x + u`, `x + 2u`, … stay in `S` — closed by a pigeonhole
draw on `S.card + 1` terms, then cancellation in the torsion-free group.
Consequence : the invariance hypotheses carried by k1.2 (`split_mass`), k1.4
(pivot), k1.5 (Claim 3.2) and k1.6 (`splitBit_eq`) are satisfiable only at the
zero shift, whereas Lemma 1.4 instantiates them at `6 • v i` and
`3 • v (Fin.last n)`. -/
theorem eq_zero_of_image_add_eq_self {d : ℕ} {S : Finset (Fin d → ℤ)}
    {u : Fin d → ℤ} (hS : S.image (fun x => x + u) = S) (hne : S.Nonempty) :
    u = 0 := by
  obtain ⟨x, hx⟩ := hne
  -- The orbit `x + k • u` stays in `S`.
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
  -- Pigeonhole : two distinct indices give the same point.
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
  -- Torsion-free group : the nonzero coefficient forces `u = 0`, coordinate by coordinate.
  funext i'
  have hcoord : ((i : ℤ) - (j : ℤ)) * u i' = 0 := by
    have := congrFun hsub i'
    simpa using this
  rcases mul_eq_zero.mp hcoord with h | h
  · exact absurd h hne'
  · exact h

/-- **Non-vacuity of containment** : every function admitting a finite support
`S₀` admits an `S` containing the support and its translates by `A` — the union
of `S₀` and of its translates. This is the positive control that the invariance
hypotheses of k1.* were missing. -/
theorem supportContained_biUnion {d : ℕ} {P : (Fin d → ℤ) → ℝ}
    {S₀ : Finset (Fin d → ℤ)} {A : Finset (Fin d → ℤ)}
    (h : ∀ z, P z ≠ 0 → z ∈ S₀) :
    SupportContained (S₀ ∪ A.biUnion (fun w => S₀.image (fun z => z + w))) P A := by
  intro z hz w hw
  exact Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_image.mpr ⟨z, h z hz, rfl⟩⟩)

/-- **Re-indexing by translation under containment** : if `S` contains the
support of `P` and of `P ∘ (· + v)`, then `∑ x ∈ S, P (x + v) = ∑ x ∈ S, P x`
(both equal the mass of `P`). This is the satisfiable replacement of
`sum_translate_image` (k1.2) : the three sums — over the translated image, over
the intersection and over `S` — coincide because the terms off-support vanish. -/
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

/-- Monotonicity of containment in the set of shifts : an `S` that contains the
translates by `A` contains them by any subset of `A`. -/
lemma SupportContained.mono {d : ℕ} {S : Finset (Fin d → ℤ)} {P : (Fin d → ℤ) → ℝ}
    {A B : Finset (Fin d → ℤ)} (h : SupportContained S P B) (hAB : A ⊆ B) :
    SupportContained S P A :=
  fun z hz w hw => h z hz w (hAB hw)

/-- **Product re-indexing under containment** : the k1.5 version of
`sum_comp_add_eq_sum_of_support` — for `Q` on `S × Bool` whose support and
first-coordinate translate are contained in `S`, the sum of `Q ∘ (· + (u, 0))`
over `S × univ` equals that of `Q`. -/
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

/-- **Product pivot identity under masses** : the k1.5 form, with the two masses
as hypotheses instead of the support invariance — `Δ(Q, (u, 0)) = 1 −` the
overlap with the translate, as soon as `Q` and its translate have mass 1. -/
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

/-- **Preservation of mass by the splitting, under containment** : the
consumable version of `split_mass` (k1.2) — `S` must contain the support of `P`
and its translates by `±v`, the invariance `S.image (· ± v) = S` being
unsatisfiable for `v ≠ 0` (`eq_zero_of_image_add_eq_self`). -/
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

/-- **Pivot identity under containment** : the consumable version of
`overlap_translate_eq_one_sub_shiftDistance` (k1.4) — mass 1 and `S` containing
the support of `P` and its translate by `−u` suffice : under these hypotheses
both masses equal 1 and the pointwise identity of the minimum telescopes as in
k1.4. -/
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

/-- Symmetric form of the pivot identity under containment. -/
theorem shiftDistance_eq_one_sub_overlap_of_support {d : ℕ}
    {P : (Fin d → ℤ) → ℝ} {S : Finset (Fin d → ℤ)}
    (hmass : ∑ x ∈ S, P x = 1) {u : Fin d → ℤ}
    (hP : SupportContained S P ({0, -u} : Finset (Fin d → ℤ))) :
    shiftDistance S P u = 1 - overlap P (fun x => P (x + u)) S := by
  rw [overlap_translate_eq_one_sub_shiftDistance_of_support hmass hP]
  ring

/-- **Claim 3.2 under containment** : the consumable version of
`shiftDistanceProd_split_le` (k1.5) — the splitting does not increase the
translation distance in the directions of the base, under mass 1, positivity of
`P` and containment by the six shifts `0, ±v, −u, v−u, −v−u` (those of the
support and of its translate, and of their splittings). The shifts `±v − u` are
those carrying `supp T_v P − (u,0)` into `S` ; `−(v+v)` does not appear there :
the splitting does not consume it. -/
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
  -- The support of `T_v P` and that of its translate live in `S × univ`.
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

/-- **Splitting-bit identity under containment** : the consumable version of
`splitBit_eq` (k1.6) — `splitBit v P S = ½(1 − Δ(P, 2v))` under mass 1 and
containment by `0, ±v, −v−v` (both spellings `-v - v` and `-(v + v)` are
carried : Lean does not identify them syntactically, and one of the sites
consumes the former while the pivot consumes the latter). -/
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

end Discrepancy.Komlos_en
