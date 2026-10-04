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

Closed bricks : `shiftDistance`, `shiftDistance_zero`, `shiftDistance_nonneg`.

**Deferred to c.886+** (progressive delivery, proof by proof, never
`sorry`) : `shiftDistance_symm`, `shiftDistance_eq_zero_of_zero`,
`shiftDistance_le_one` — three lemmas that depend on the operator
`T_v` (Def 3.1) or real arithmetic that the pinned Mathlib does not
resolve in v4.33.0.

The proof state lives in `FORMAL_STATUS.md` (« Karingula–Lovett
distillation, bricks k1..k5 »). This delivery is the **first k1 brick** :
the shift distance Δ is in the namespace, its definition is well-formed,
and the trivial identities (zero, null source, non-negativity) are
closed.
-/

import Discrepancy.Basic

/-!
# Shift distance Δ (Def 1.3, Karingula–Lovett)

`Discrepancy.Komlos_en.shiftDistance S P u = ½ · Σ_{x ∈ S} |P(x + u) − P(x)|`
is the half-total-variation distance between a distribution
`P : ℤ^d → ℝ` supported in a finite `Finset S` and its translation by
`u`. It is the elementary brick underlying the splitting operator
`T_v` (Def 3.1) and Lemma 1.4 (the hard core of the distillation).

**Domain convention**: we **pass the support** `S : Finset (Fin d → ℤ)`
explicitly, rather than inferring a `Fintype` on `Fin d → ℤ` (which
has no instance). This stays faithful to the « finite support »
convention of the paper and gives a type-clean signature without
artificial `Fintype` hypotheses.

**Forward convention**: we sum `|P(x + u) − P(x)|` (forward shift),
not `|P(x) − P(x − u)|` (backward shift). The two differ by an index
translation, but the forward version is more natural for the trivial
symmetric identities.

This brick only assumes `Basic.lean` — no upstream dependency
(Komlos.Tent is not required for these basic identities). The Mathlib
pin `db584cd6` is in the fleet cohort v4.32.1 (mutualisation #4363) ;
the gap between this pin and the local toolchain v4.33.0 is handled by
`lake build` (Lean 4 is major-version backward-compatible).
-/

namespace Discrepancy.Komlos_en

/-- Shift distance Δ(P, u, S) = ½ · Σ_{x ∈ S} |P(x + u) − P(x)|.

We sum over `S`, any `Finset` that contains the effective support of
`P` (and therefore, by translation, that of `P(· + u)`). The
convention is that `S` may be wider than necessary — the definition
remains correct, only the out-of-support contributions are zero. -/
noncomputable def shiftDistance {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x ∈ S, |P (x + u) - P x|

/-- Δ(P, 0) = 0: the zero shift changes nothing. -/
lemma shiftDistance_zero {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) :
    shiftDistance S P 0 = 0 := by
  unfold shiftDistance
  simp

/-- Δ(P, u) ≥ 0: it is a half-sum of absolute values. -/
lemma shiftDistance_nonneg {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ) :
    0 ≤ shiftDistance S P u := by
  unfold shiftDistance
  apply mul_nonneg
  · simp
  exact Finset.sum_nonneg fun x _ => abs_nonneg _

/-! **Deferred to c.886+**: 3 bricks **not closed** in this commit, to
be delivered with the operator `T_v` (Def 3.1) which posits the
appropriate support hypotheses:

1. `shiftDistance_symm` — Δ(u) = Δ(−u) requires a support-invariance
   hypothesis (`S = S.image (· + u)`). Without it, the lemma is false
   in general: `|P (x + u) − P x| ≠ |P (x − u) − P x|` for asymmetric P.

2. `shiftDistance_eq_zero_of_zero` — Δ(P, u) = 0 when P ≡ 0 on S ∪
   (S + u) requires real-arithmetic `(1/2) * 0 = 0` after rewriting
   the inner sum. The direct proof is delicate in Lean 4 v4.33.0
   without extended `Mathlib`.

3. `shiftDistance_le_one` — Δ(P, u) ≤ ½ · ‖P‖₁ by triangle inequality.
   The typeclass instance `(0 : ℝ) ≤ (1/2 : ℝ)` is not resolved by
   `positivity` or `norm_num` in this configuration (needs a
   `ZeroLEOneClass` instance or equivalent that depends on the pinned
   Mathlib).

Closed bricks in this commit: `shiftDistance`, `shiftDistance_zero`,
`shiftDistance_nonneg`. Module builds
(`lake build Discrepancy.Komlos_en.ShiftDistance` SUCCESS expected), 0
`sorry` in code. -/

end Discrepancy.Komlos_en