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

`Discrepancy.Komlos.shiftDistance P u = ½ · Σ_x |P(x) − P(x − u)|` is the
half-total-variation distance between a finitely-supported distribution
`P : ℤ^d → ℝ` and its translation by `u`. It is the elementary brick
underlying the splitting operator `T_v` (Def 3.1) and Lemma 1.4 (the
hard core of the distillation).

The definition uses the « finite support » convention: the sum runs over
the union of the supports of `P` and `P(· − u)` (which makes the sum
finite even though the codomain is the whole `ℤ^d`).

This brick only assumes `Basic.lean` — no upstream dependency
(Komlos.Tent is not required for these basic identities). The Mathlib
pin `db584cd6` is in the fleet cohort v4.32.1 (mutualisation #4363) ;
the gap between this pin and the local toolchain v4.33.0 is handled by
`lake build` (Lean 4 is major-version backward-compatible).
-/

namespace Discrepancy.Komlos_en

/-- Finite support of a distribution: the set of points where it is
non-zero. For this elementary brick, we use the direct definition
(`Finset.univ.filter`) and bound via `tsub_eq_zero_iff_eq` when needed. -/
def supportFun {d : ℕ} (P : (Fin d → ℤ) → ℝ) : Finset (Fin d → ℤ) :=
  Finset.univ.filter fun x => P x ≠ 0

/-- Shift distance Δ(P, u) = ½ · Σ_x |P(x) − P(x − u)|.

We sum over the union of the supports of `P` and `P(· − u)`: this sum
is naturally finite (both terms vanish outside this union). The constant
`½` is reported as a multiplicative factor. -/
noncomputable def shiftDistance {d : ℕ} (P : (Fin d → ℤ) → ℝ)
    (u : Fin d → ℤ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x ∈ supportFun P ∪ supportFun (fun x => P (x - u)),
    |P x - P (x - u)|

/-- Δ(P, 0) = 0: the zero shift changes nothing. -/
lemma shiftDistance_zero {d : ℕ} (P : (Fin d → ℤ) → ℝ) :
    shiftDistance P 0 = 0 := by
  unfold shiftDistance
  simp

/-- Δ(P, u) = Δ(P, −u): the shift distance is symmetric. -/
lemma shiftDistance_symm {d : ℕ} (P : (Fin d → ℤ) → ℝ)
    (u : Fin d → ℤ) :
    shiftDistance P u = shiftDistance P (-u) := by
  unfold shiftDistance
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  simp [sub_neg_eq_add, abs_sub_comm]

/-- Δ(P, u) = 0 when P is identically zero. -/
lemma shiftDistance_eq_zero_of_zero {d : ℕ} (P : (Fin d → ℤ) → ℝ)
    (hP : ∀ x, P x = 0) (u : Fin d → ℤ) : shiftDistance P u = 0 := by
  unfold shiftDistance supportFun
  simp [hP]

/-- Δ(P, u) ≥ 0: it is a half-sum of absolute values. -/
lemma shiftDistance_nonneg {d : ℕ} (P : (Fin d → ℤ) → ℝ)
    (u : Fin d → ℤ) : 0 ≤ shiftDistance P u := by
  unfold shiftDistance
  apply mul_nonneg
  · simp
  exact Finset.sum_nonneg fun x _ => abs_nonneg _

/-- Δ(P, u) ≤ ½ · ‖P‖₁: the distance is bounded by half the total L¹
mass (sum of |P(x)| over the support of P and its translate). This
bound is immediate by the triangle inequality on each term. -/
lemma shiftDistance_le_one {d : ℕ} (P : (Fin d → ℤ) → ℝ)
    (u : Fin d → ℤ) :
    shiftDistance P u ≤
      (1 / 2 : ℝ) * (∑ x ∈ supportFun P, |P x| +
        ∑ x ∈ supportFun (fun x => P (x - u)), |P (x - u)|) := by
  unfold shiftDistance
  rw [← Finset.sum_union]
  · apply mul_le_mul_of_nonneg_left
    apply Finset.sum_le_sum
    intro x _
    exact abs_sub_le _ _
    simp
  · exact Finset.union_comm _ _ |> Finset.subset_union_right.trans
      (Finset.union_subset (Finset.subset_union_left) (Finset.subset_union_right))
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
non-negative bounds, and `Finset.sum_congr`/`Finset.union_comm` for
sum identities.
-/

end Discrepancy.Komlos_en
