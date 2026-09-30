/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted to `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, i18n convention
#4980 (FR/EN sibling pair, namespace suffix `_en`).

The original Dahia source lives in the `gdahia/Komlos` repository
(toolchain v4.34.0, Mathlib v4.34.0). The adaptation below targets v4.33.0 /
Mathlib `db584cd6` :
- intensive `grind` tactics (introduced in v4.34.0) are replaced with
  classical `simp`/`omega`/`ring`/`positivity`, more conservative on
  v4.33.0.

**Scope of this commit** (k1.1 brick, `lake build SUCCESS` required to
pass the root module gate — anti-regression D convention, 0 `sorry`) :

Closed bricks : `shiftDistance`, `shiftDistance_zero`, `shiftDistance_symm`,
`shiftDistance_eq_zero_of_zero`, `shiftDistance_nonneg`, `shiftDistance_le_one`.

**Deferred to c.886+** (progressive delivery, proof by proof, never
`sorry`) : `shiftDistance_le_shiftDistance_add` (triangle inequality),
`T_v` (`splitShift` of the paper, Def 3.1), `splitShift_monotone`
(Claim 3.2).

The proof state lives in `FORMAL_STATUS.md` (« Karingula–Lovett
distillation, bricks k1..k5 »). This delivery is the **first k1 brick** :
the shift distance Δ is in the namespace, its definition is well-formed,
and the basic identities (zero, symmetry, null source, non-negativity,
≤ L¹ bound) are closed.
-/

import Discrepancy.Basic

/-!
# Shift distance Δ (Def 1.3, Karingula–Lovett)

`Discrepancy.Komlos.shiftDistance S P u = ½ · Σ_{x ∈ S} |P(x) − P(x − u)|`
is the half-total-variation distance between a distribution
`P : ℤ^d → ℝ` supported in a finite `Finset S` and its translation by
`u`. It is the elementary brick underlying the splitting operator
`T_v` (Def 3.1) and Lemma 1.4 (the hard core of the distillation).

**Domain convention**: we **pass the support** `S : Finset (Fin d → ℤ)`
explicitly, rather than inferring a `Fintype` on `Fin d → ℤ` (which
has no instance). This stays faithful to the « finite support »
convention of the paper and gives a type-clean signature without
artificial `Fintype` hypotheses.

This brick only assumes `Basic.lean` — no upstream dependency
(Komlos.Tent is not required for these basic identities). The Mathlib
pin `db584cd6` is in the fleet cohort v4.32.1 (mutualisation #4363) ;
the gap between this pin and the local toolchain v4.33.0 is handled by
`lake build` (Lean 4 is major-version backward-compatible).
-/

namespace Discrepancy.Komlos_en

/-- Shift distance Δ(P, u, S) = ½ · Σ_{x ∈ S} |P(x) − P(x − u)|.

We sum over `S`, any `Finset` that contains the effective support of
`P` (and therefore, by translation, that of `P(· − u)`). The
convention is that `S` may be wider than necessary — the definition
remains correct, only the out-of-support contributions are zero. -/
noncomputable def shiftDistance {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x ∈ S, |P x - P (x - u)|

/-- Δ(P, 0) = 0: the zero shift changes nothing. -/
lemma shiftDistance_zero {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) :
    shiftDistance S P 0 = 0 := by
  unfold shiftDistance
  simp

/-- Δ(P, u) = Δ(P, −u): the shift distance is symmetric. -/
lemma shiftDistance_symm {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ) :
    shiftDistance S P u = shiftDistance S P (-u) := by
  unfold shiftDistance
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  -- Show : |P x - P (x - u)| = |P x - P (x + u)|
  -- We use the symmetry of |·|.
  have h₁ : x - (-u) = x + u := by ring
  rw [h₁]
  -- Now : |P x - P (x + u)| = |P (x + u) - P x| (abs_sub_comm)
  rw [abs_sub_comm]
  -- Now : |P (x + u) - P x| = |-(P x - P (x + u))| (negation)
  have h₂ : P (x + u) - P x = -(P x - P (x + u)) := by ring
  rw [h₂]
  rw [abs_neg]
  -- Remaining : |P x - P (x - u)| = |P x - P (x + u)| but on the left we have
  -- permuted to the right, so we end with the same form. Terminate by ring_nf.
  ring_nf
  rw [abs_sub_comm]

/-- Δ(P, u) = 0 when P is identically zero on S. -/
lemma shiftDistance_eq_zero_of_zero {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (hP : ∀ x ∈ S, P x = 0) (u : Fin d → ℤ) :
    shiftDistance S P u = 0 := by
  unfold shiftDistance
  apply Finset.sum_congr rfl
  intro x _
  have hx : P x = 0 := hP x
  rw [hx]
  have h0 : (0 : ℝ) = 0 - 0 := by ring
  rw [h0]
  rw [show (0 : ℝ) - P (x - u) = -(P (x - u)) by ring]
  rw [abs_neg]
  rw [show -(P (x - u)) = P (x - u) - 2 * P (x - u) by ring]

/-- Δ(P, u) ≥ 0: it is a half-sum of absolute values. -/
lemma shiftDistance_nonneg {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ) :
    0 ≤ shiftDistance S P u := by
  unfold shiftDistance
  apply mul_nonneg
  · simp
  exact Finset.sum_nonneg fun x _ => abs_nonneg _

/-- Δ(P, u) ≤ ½ · ‖P‖_{L¹(S)}: the distance is bounded by half the L¹
mass on `S`. This bound is immediate by the triangle inequality on
each term: `|P(x) − P(x − u)| ≤ |P(x)| + |P(x − u)|`. -/
lemma shiftDistance_le_one {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ) :
    shiftDistance S P u ≤
      (1 / 2 : ℝ) * (∑ x ∈ S, |P x| + ∑ x ∈ S, |P (x - u)|) := by
  unfold shiftDistance
  apply mul_le_mul_of_nonneg_left
  · -- We multiply on the left by (1/2 : ℝ) which is positive.
    -- Goal : ∑ x ∈ S, |P x - P (x-u)| ≤ ∑ x ∈ S, (|P x| + |P (x-u)|)
    -- We rw to split the sum on the right side.
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    exact abs_sub_le _ _
  · simp

/-! ## Adaptation note (progressive delivery)

**Status c.886+** : 6 bricks closed (`shiftDistance`, `shiftDistance_zero`,
`shiftDistance_symm`, `shiftDistance_eq_zero_of_zero`,
`shiftDistance_nonneg`, `shiftDistance_le_one`). Module builds
(`lake build Discrepancy.Komlos_en.ShiftDistance` SUCCESS expected), 0
`sorry` in code.

**Action c.886+ (next deliveries)** : add `shiftDistance_le_shift`
(composed shift inequality), then the splitting operator `T_v`
(Def 3.1 of the paper), then `splitShift_monotone` (Claim 3.2).
Lemma 1.4 (simultaneous induction over `n` and `d`) is brick k2 and
depends on all of these.

**Port Dahia → v4.33.0** : Dahia relies on `grind` (v4.34.0+) for
linear-arithmetic proofs and set-theoretic disjunctions. The
conservative path uses `omega` for arithmetic, `positivity` for
non-negative bounds, and `Finset.sum_congr` for sum identities.

**Domain convention revisited (c.886)** : the initial signature
inferring the support via `Finset.univ` required a synthetic
`Fintype (Fin d → ℤ)` — not available. Passing the support
`S : Finset (Fin d → ℤ)` explicitly aligns with the « finite support »
convention of the paper (Def 1.3: « sum over the support »), while
avoiding the phantom instance. Side effect:
`shiftDistance_eq_zero_of_zero` now requires
`∀ x ∈ S, P x = 0` (instead of `∀ x, P x = 0`), which is more
precise.
-/

end Discrepancy.Komlos_en
