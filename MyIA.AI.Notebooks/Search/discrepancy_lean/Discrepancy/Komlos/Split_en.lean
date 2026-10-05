/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted to `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

The original Dahia source lives in `gdahia/Komlos` (module
`Komlos/Split.lean`, toolchain v4.34.0, `Finsupp` framework over
`E →₀ ℝ`, height `E × ℝ`). The adaptation below follows the lake
convention established by brick k1.1 (`ShiftDistance.lean`) : **explicit
Finset** framework `P : (Fin d → ℤ) → ℝ` with the support `S` passed as
an argument, and `Bool` height (`false` = slice 0, `true` = slice 1) —
faithful to the paper's « finite support », without artificial
`Fintype` or superfluous `Module` instances.

**Scope of this commit** (brick k1.2, `lake build SUCCESS` required, 0
`sorry`) :

Bricks closed : `split` (Def 3.1), `split_apply_zero`, `split_apply_one`,
`split_nonneg`, `sum_invariance_image` (re-indexing of a sum under
invariance `S.image f = S` for injective `f` — the reusable brick that
`shiftDistance_symm`, postponed from k1.1, was missing ; additive case
`sum_translate_image` for k1.3), `split_mass`
(splitting preserves mass — the structural property that makes `T_v` an
operation on distributions), `split_mono` (pointwise monotonicity).

**Postponed to k1.3+** : Claim 3.2 (`shiftDist_split_le` in Dahia :
`Δ(T_v P, (u, 0)) ≤ Δ(P, u)`) requires the identity `Δ = 1 − overlap`,
which itself requires the `overlap` operator — not yet distilled in this
lake ; the commutation `split_tr` (split ∘ translate) follows the same
path. The detailed state lives in `FORMAL_STATUS.md`.
-/

import Discrepancy.Komlos.ShiftDistance_en

/-!
# Splitting operator `T_v` (Def 3.1, Karingula–Lovett)

`Discrepancy.Komlos_en.split v P` is the split distribution on
`(Fin d → ℤ) × Bool` : at height `false` (slice 0) it assigns half the
**maximum** of `P (x + v)` and `P (x - v)`, at height `true` (slice 1)
half their **minimum**.

Splitting preserves mass (`split_mass`) : the high half and the low half
redistribute exactly `P (x + v) + P (x - v)`, and the re-indexing
`sum_invariance_image` telescopes both sums under the invariance
hypothesis of the support by `±v` — the exact hypothesis that k1.1
identified as necessary for the symmetric identities of `Δ`.

**Height convention** : `Bool` rather than `ℝ` (Dahia : slices
`E × {0, 1}`) — the two slices of the paper are the two Boolean values,
no computation on the height appears in the proof.

This brick only assumes `Komlos.ShiftDistance_en` (and transitively
`Discrepancy.Basic`). The Mathlib pin `db584cd6` is in the fleet cohort
v4.32.1 (mutualisation #4363) ; the gap with the local toolchain v4.33.0
is handled by `lake build`.
-/

namespace Discrepancy.Komlos_en

/-- Splitting operator `T_v` (Def 3.1) : at `(x, false)` half the
maximum of `P (x + v)` and `P (x - v)`, at `(x, true)` half their
minimum. This is the **finite** replacement for the continuous
rearrangement of Guo–Fang–Lu : it decouples the high/low masses without
ever leaving the finite-support distribution framework. -/
noncomputable def split {d : ℕ} (v : Fin d → ℤ)
    (P : (Fin d → ℤ) → ℝ) : ((Fin d → ℤ) × Bool) → ℝ := fun y =>
  if y.2 then (1 / 2 : ℝ) * min (P (y.1 + v)) (P (y.1 - v))
  else (1 / 2 : ℝ) * max (P (y.1 + v)) (P (y.1 - v))

/-- Slice 0 : `(T_v P)(x, false) = ½ · max{P (x + v), P (x - v)}`. -/
lemma split_apply_zero {d : ℕ} (v : Fin d → ℤ) (P : (Fin d → ℤ) → ℝ)
    (x : Fin d → ℤ) :
    split v P (x, false) = (1 / 2 : ℝ) * max (P (x + v)) (P (x - v)) := by
  simp [split]

/-- Slice 1 : `(T_v P)(x, true) = ½ · min{P (x + v), P (x - v)}`. -/
lemma split_apply_one {d : ℕ} (v : Fin d → ℤ) (P : (Fin d → ℤ) → ℝ)
    (x : Fin d → ℤ) :
    split v P (x, true) = (1 / 2 : ℝ) * min (P (x + v)) (P (x - v)) := by
  simp [split]

/-- Splitting a nonnegative function stays nonnegative : each slice
carries half of a max/min of nonnegative values. -/
lemma split_nonneg {d : ℕ} {P : (Fin d → ℤ) → ℝ} (hP : ∀ x, 0 ≤ P x)
    (v : Fin d → ℤ) (y : (Fin d → ℤ) × Bool) : 0 ≤ split v P y := by
  obtain ⟨x, b⟩ := y
  cases b with
  | false =>
    rw [split_apply_zero]
    exact mul_nonneg (by norm_num)
      ((hP (x + v)).trans (le_max_left (P (x + v)) (P (x - v))))
  | true =>
    rw [split_apply_one]
    exact mul_nonneg (by norm_num) (le_min (hP _) (hP _))

/-- Re-indexing of a sum under image invariance : if `f` is injective and
preserves the support (`S.image f = S`), summing `P (f x)` over `S`
amounts to summing `P` over `S`. This is the telescoping brick that
`shiftDistance_symm` (postponed from k1.1) was missing : support
invariance, not mere inclusion, is what makes the re-indexing exact for an
arbitrary `P`. Generic form — `sum_translate_image` is its additive case. -/
lemma sum_invariance_image {d : ℕ} {P : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)} {f : (Fin d → ℤ) → (Fin d → ℤ)}
    (hf : ∀ a b, f a = f b → a = b) (hS : S.image f = S) :
    ∑ x ∈ S, P (f x) = ∑ x ∈ S, P x := by
  have hinj : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b :=
    fun a _ b _ hab => hf a b hab
  calc ∑ x ∈ S, P (f x)
      = ∑ y ∈ S.image f, P y := (Finset.sum_image hinj).symm
    _ = ∑ y ∈ S, P y := by rw [hS]

/-- Additive case `f = (· + u)` : the form in which k1.3 will reuse the
re-indexing for the symmetric identities of `Δ`. -/
lemma sum_translate_image {d : ℕ} (u : Fin d → ℤ) {P : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)} (hS : S.image (fun x => x + u) = S) :
    ∑ x ∈ S, P (x + u) = ∑ x ∈ S, P x :=
  sum_invariance_image (f := fun x => x + u) (fun _ _ hab => add_right_cancel hab) hS

/-- Splitting preserves mass (implicit claim of the paper, `mass_split`
in Dahia) : under invariance of the support by `±v`, the total mass of
`T_v P` over `S × {false, true}` equals the mass of `P` over `S`. This
is the structural property that makes `T_v` an operation on
distributions rather than a mere function. -/
lemma split_mass {d : ℕ} (v : Fin d → ℤ) {P : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)}
    (hSv : S.image (fun x => x + v) = S)
    (hSvm : S.image (fun x => x - v) = S) :
    ∑ y ∈ S ×ˢ (Finset.univ : Finset Bool), split v P y = ∑ x ∈ S, P x := by
  have key : ∀ x ∈ S, split v P (x, false) + split v P (x, true)
      = (P (x + v) + P (x - v)) * (1 / 2 : ℝ) := by
    intro x _
    rw [split_apply_zero, split_apply_one, ← mul_add, max_add_min, mul_comm]
  have hbool : ∀ x ∈ S, ∑ y ∈ (Finset.univ : Finset Bool), split v P (x, y)
      = split v P (x, false) + split v P (x, true) := by
    intro x _
    simp; ac_rfl
  have hsub : ∀ a b : Fin d → ℤ, a - v = b - v → a = b := by
    intro a b hab
    have h2 : a - v + v = b - v + v := by rw [hab]
    simpa [sub_add_cancel] using h2
  rw [Finset.sum_product, Finset.sum_congr rfl hbool,
    Finset.sum_congr rfl key, ← Finset.sum_mul, Finset.sum_add_distrib,
    sum_invariance_image (f := fun x => x + v) (fun a b hab => add_right_cancel hab) hSv,
    sum_invariance_image (f := fun x => x - v) hsub hSvm]
  linarith

/-- Pointwise monotonicity of splitting (`split_mono` in Dahia) : if
`P ≤ Q` pointwise, then `T_v P ≤ T_v Q` pointwise — max and min
transport by monotonicity, the height is unchanged. -/
lemma split_mono {d : ℕ} (v : Fin d → ℤ) {P Q : (Fin d → ℤ) → ℝ}
    (h : ∀ x, P x ≤ Q x) (y : (Fin d → ℤ) × Bool) :
    split v P y ≤ split v Q y := by
  obtain ⟨x, b⟩ := y
  cases b with
  | false =>
    rw [split_apply_zero, split_apply_zero]
    exact mul_le_mul_of_nonneg_left (max_le_max (h _) (h _)) (by norm_num)
  | true =>
    rw [split_apply_one, split_apply_one]
    exact mul_le_mul_of_nonneg_left (min_le_min (h _) (h _)) (by norm_num)

end Discrepancy.Komlos_en
