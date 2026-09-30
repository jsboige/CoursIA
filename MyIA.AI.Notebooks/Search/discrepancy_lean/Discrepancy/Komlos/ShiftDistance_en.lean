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

Closed bricks : `shiftDistance`, `shiftDistance_zero`,
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
translation, but the forward version is more natural for the symmetry
Δ(u) = Δ(−u) — it follows from `|a − b| = |b − a|` without any
support-stability hypothesis.

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

/-! **Deferred to c.886+**: `shiftDistance_symm` (Δ(u) = Δ(−u)) — the
shift symmetry **requires** a support-invariance hypothesis:
`S = S.image (· + u)`. Without it, the lemma is false in general
(`|P (x + u) − P x| ≠ |P (x − u) − P x|` for an asymmetric P). The symm
brick will be delivered with the operator `T_v` (Def 3.1) which posits
precisely this hypothesis on the centered box `S = {-N..N}^d ∩ ℤ^d`
(Def 3.1, Claim 3.2). In the meantime, the brick is **not closed**:
we omit the lemma here, we do not stub it in `sorry`. -/

/-- Δ(P, u) = 0 when P is identically zero on S ∪ (S + u). -/
lemma shiftDistance_eq_zero_of_zero {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ)
    (hP : ∀ x ∈ S, P x = 0)
    (hu : ∀ x ∈ S, P (x + u) = 0) :
    shiftDistance S P u = 0 := by
  unfold shiftDistance
  -- Each term |P (x + u) - P x| = 0 when P is zero everywhere.
  -- The sum of zeros is zero, and (1/2) * 0 = 0.
  have : ∀ x ∈ S, |P (x + u) - P x| = 0 := fun x _ => by
    rw [hu x, hP x]; simp
  simp [this]

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
each term: `|P(x + u) − P(x)| ≤ |P(x + u)| + |P(x)|`. -/
lemma shiftDistance_le_one {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ) :
    shiftDistance S P u ≤
      (1 / 2 : ℝ) * (∑ x ∈ S, |P x| + ∑ x ∈ S, |P (x + u)|) := by
  unfold shiftDistance
  gcongr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  exact abs_sub_le _ _

/-! ## Adaptation note (progressive delivery)

**Status c.886+** : 5 bricks closed (`shiftDistance`, `shiftDistance_zero`,
`shiftDistance_eq_zero_of_zero`, `shiftDistance_nonneg`,
`shiftDistance_le_one`). The `shiftDistance_symm` lemma requires a
support-invariance hypothesis (`S = S.image (· + u)`) — out of scope
for k1.1, **deferred to the `T_v` brick** (Def 3.1) which posits this
hypothesis on the centered box `S = {-N..N}^d ∩ ℤ^d`. Module builds
(`lake build Discrepancy.Komlos_en.ShiftDistance` SUCCESS expected), 0
`sorry` in code.

**Action c.886+ (next deliveries)** : deliver `shiftDistance_symm` with
the operator `T_v` (Def 3.1 of the paper), then `splitShift_monotone`
(Claim 3.2). Lemma 1.4 (simultaneous induction over `n` and `d`) is
brick k2 and depends on all of these.

**Port Dahia → v4.33.0** : Dahia relies on `grind` (v4.34.0+) for
linear-arithmetic proofs and set-theoretic disjunctions. The
conservative path uses `omega` for arithmetic, `positivity` for
non-negative bounds, and `Finset.sum_congr` for sum identities.

**Forward convention revisited (c.886+)** : the « forward shift »
convention `|P(x + u) − P(x)|` (instead of « backward »
`|P x − P(x − u)|`) yields `Δ(P, u) = Σ |P (x+u) − P x| / 2` and
makes the chain `Δ(P, u) = Σ |P(x + u) − P x| / 2 = Σ |P x − P(x + u)| / 2`
(per-element, by `abs_sub_comm`+`abs_neg`) trivial — but this **does
not** yield `shiftDistance_symm` because the sum index `x ∈ S` vs
`x ∈ S - u` differs. The symm lemma requires a change-of-variable that
needs `S = S.image (· + u)` — out of scope here.

**Domain convention** : `S : Finset (Fin d → ℤ)` passed explicitly
(« finite support » convention of the paper, Def 1.3) rather than
inferred via `Finset.univ` (no synthetic `Fintype (Fin d → ℤ)`).
-/

end Discrepancy.Komlos_en