/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted to `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

The original Dahia source lives in `gdahia/Komlos` (module
`Komlos/ShiftDistance.lean`, toolchain v4.34.0, `Finsupp` framework over
`E →₀ ℝ`, `overlap P Q = mass (P ⊓ Q)` with `tvDist` and `shiftDist` in the
same module). The adaptation below follows the lake convention established
by brick k1.1 (`ShiftDistance.lean`) : **explicit Finset** framework
`P : (Fin d → ℤ) → ℝ` with the support `S` passed as an argument — the
Finsupp infimum becomes the pointwise `min`, the support becomes an explicit
argument, without `Finsupp` or dotted order.

**Scope of this commit** (brick k1.3, `lake build SUCCESS` required, 0
`sorry`) :

Bricks closed : `overlap` (overlap operator), `overlap_comm`, `overlap_self`
(the overlap of a function with itself is its mass), `overlap_nonneg`,
`overlap_mono`, `overlap_le_sum_left`, `overlap_le_sum_right` (the overlap
is dominated by each mass), `sum_le_overlap` (any function bounded above by
both arguments is dominated by the overlap — `mass_le_overlap` in Dahia),
`min_eq_half_add_sub_abs` (the pointwise identity
`min a b = ½ (a + b − |a − b|)` — the local brick of the pivot identity).

**Postponed to k1.4** : the pivot identity
`overlap P (P ∘ (· + u)) = 1 − Δ(P, u)` under mass 1 and invariance of the
support by `u` (requires the re-indexing `sum_translate_image` from k1.2 and
the forward convention of `ShiftDistance`) ; `overlap_tr` (invariance of
the overlap under a common translation, same path) ; Claim 3.2
(`Δ(T_v P, (u, 0)) ≤ Δ(P, u)`) and `split_tr` (both follow the pivot
identity). The detailed state lives in `FORMAL_STATUS.md`.
-/

import Discrepancy.Basic

/-!
# Overlap operator `overlap` (Karingula–Lovett)

`Discrepancy.Komlos_en.overlap P Q S` is the sum of the pointwise minima
`min (P x) (Q x)` over the explicit finite support `S` : the **common
mass** of `P` and `Q`. For two probability distributions the overlap
equals `1 − tvDist` (pivot identity postponed to k1.4) — it is the
quantity that the elementary proof of Komlós carries from `P` to its
translate, then controls through the splitting `split` (k1.2).

This brick only assumes `Discrepancy.Basic` (no dependency on
`ShiftDistance` or `Split` : it sits upstream of the pivot identity).
The Mathlib pin `db584cd6` is in the fleet cohort v4.32.1
(mutualisation #4363) ; the gap with the local toolchain v4.33.0 is
handled by `lake build`.
-/

namespace Discrepancy.Komlos_en

/-- Overlap operator : the sum of pointwise minima over the explicit
support `S`. This is Dahia's `Komlos.overlap P Q = mass (P ⊓ Q)`
transposed to the Finset framework of the lake — the common mass of `P`
and `Q`, without artificial `Finsupp`. -/
noncomputable def overlap {d : ℕ} (P Q : (Fin d → ℤ) → ℝ)
    (S : Finset (Fin d → ℤ)) : ℝ := ∑ x ∈ S, min (P x) (Q x)

/-- Symmetry of the overlap : `min` is commutative termwise. -/
lemma overlap_comm {d : ℕ} (P Q : (Fin d → ℤ) → ℝ)
    (S : Finset (Fin d → ℤ)) :
    overlap P Q S = overlap Q P S := by
  unfold overlap
  exact Finset.sum_congr rfl (fun x _ => min_comm (P x) (Q x))

/-- The overlap of a function with itself is its mass over `S`. -/
lemma overlap_self {d : ℕ} (P : (Fin d → ℤ) → ℝ)
    (S : Finset (Fin d → ℤ)) :
    overlap P P S = ∑ x ∈ S, P x := by
  unfold overlap
  exact Finset.sum_congr rfl (fun x _ => min_self (P x))

/-- Nonnegativity : the overlap of two nonnegative functions over `S` is
nonnegative. -/
lemma overlap_nonneg {d : ℕ} {P Q : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)}
    (hP : ∀ x ∈ S, 0 ≤ P x) (hQ : ∀ x ∈ S, 0 ≤ Q x) :
    0 ≤ overlap P Q S := by
  unfold overlap
  exact Finset.sum_nonneg (fun x hx => le_min (hP x hx) (hQ x hx))

/-- Monotonicity in both arguments : the overlap transports the pointwise
order. -/
lemma overlap_mono {d : ℕ} {P P' Q Q' : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)}
    (hP : ∀ x ∈ S, P x ≤ P' x) (hQ : ∀ x ∈ S, Q x ≤ Q' x) :
    overlap P Q S ≤ overlap P' Q' S := by
  unfold overlap
  exact Finset.sum_le_sum (fun x hx => min_le_min (hP x hx) (hQ x hx))

/-- The overlap is dominated by each mass. -/
lemma overlap_le_sum_left {d : ℕ} (P Q : (Fin d → ℤ) → ℝ)
    (S : Finset (Fin d → ℤ)) :
    overlap P Q S ≤ ∑ x ∈ S, P x := by
  unfold overlap
  exact Finset.sum_le_sum (fun x _ => min_le_left (P x) (Q x))

/-- Symmetric variant : the overlap is dominated by the second mass. -/
lemma overlap_le_sum_right {d : ℕ} (P Q : (Fin d → ℤ) → ℝ)
    (S : Finset (Fin d → ℤ)) :
    overlap P Q S ≤ ∑ x ∈ S, Q x := by
  unfold overlap
  exact Finset.sum_le_sum (fun x _ => min_le_right (P x) (Q x))

/-- Any function bounded above by both arguments is dominated by the
overlap (`mass_le_overlap` in Dahia) : the common mass majorates any
shared mass. This is the direction k1.4 will use to lower-bound the
overlap by the mass preserved through splitting. -/
lemma sum_le_overlap {d : ℕ} {R P Q : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)}
    (hRP : ∀ x ∈ S, R x ≤ P x) (hRQ : ∀ x ∈ S, R x ≤ Q x) :
    ∑ x ∈ S, R x ≤ overlap P Q S := by
  unfold overlap
  exact Finset.sum_le_sum (fun x hx => le_min (hRP x hx) (hRQ x hx))

/-- Pointwise identity for the minimum : `min a b = ½ (a + b − |a − b|)` —
the local brick of the pivot identity `overlap = 1 − tvDist` (k1.4) :
summed termwise, it connects the overlap and the translation distance. -/
lemma min_eq_half_add_sub_abs (a b : ℝ) :
    min a b = (1 / 2 : ℝ) * (a + b - |a - b|) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]
    ring

end Discrepancy.Komlos_en
