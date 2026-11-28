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

**Scope of this commit** (k1.8 brick, `lake build SUCCESS` required to
pass the root module gate — anti-regression D convention, 0 `sorry`) :

Closed bricks : `shiftDistance`, `shiftDistance_zero`, `shiftDistance_nonneg`,
`shiftDistance_eq_zero_of_zero`, `shiftDistance_eq_zero_of_invariant`.

**Deferred to c.886+** (progressive delivery, proof by proof, never
`sorry`) : `shiftDistance_symm`, `shiftDistance_le_one` — two lemmas that
depend on the re-indexation of the sum by `−u`, that is on the
`sum_translate_image` organ carried by `Split.lean` (k1.2) ; that module
is **downstream** of the present one, so the dependency cannot be
reversed — the brick will be delivered in a module downstream of
`Split.lean`.

The proof state lives in `FORMAL_STATUS.md` (« Karingula–Lovett
distillation, bricks k1..k5 »). This delivery is the **first k1 brick** :
the shift distance Δ is in the namespace, its definition is well-formed,
and the trivial identities (zero, null source, non-negativity) are
closed.
-/

import Discrepancy.Basic_en

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

/-- Δ(P, u) = 0 when `P` vanishes on `S` **and** on its translate `S + u`:
every term `|P (x + u) − P x|` of the sum is then zero, the whole sum is
zero, hence `½ · 0 = 0`.

The obstacle announced at brick k1.1 (« the direct proof is delicate in
Lean 4 v4.33.0 ») concerned a global rewriting of the sum; it lifts term
by term: `Finset.sum_eq_zero` suffices, the sum is zero as soon as each
term is. -/
lemma shiftDistance_eq_zero_of_zero {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ)
    (hS : ∀ x ∈ S, P x = 0) (hSu : ∀ x ∈ S, P (x + u) = 0) :
    shiftDistance S P u = 0 := by
  unfold shiftDistance
  have hsum : ∑ x ∈ S, |P (x + u) - P x| = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp [hSu x hx, hS x hx]
  rw [hsum, mul_zero]

/-- Δ(P, u) = 0 as soon as `P` is **invariant** under the shift `u` on
`S`: the term `|P (x + u) − P x|` is then `|P x − P x| = 0`.

A sufficient condition distinct from `shiftDistance_eq_zero_of_zero`
(which assumes `P` identically zero on `S ∪ (S + u)`): the two combine,
neither is deduced from the other. -/
lemma shiftDistance_eq_zero_of_invariant {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ)
    (h : ∀ x ∈ S, P (x + u) = P x) :
    shiftDistance S P u = 0 := by
  unfold shiftDistance
  have hsum : ∑ x ∈ S, |P (x + u) - P x| = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp [h x hx]
  rw [hsum, mul_zero]

/-! **Deferred to c.886+**: 2 bricks **not closed** in this commit, to
be delivered in a module **downstream of `Split.lean`** (k1.2) — the
`sum_translate_image` re-indexing organ is available there, whereas
`Split.lean` depends on the present module (a circular dependency that
cannot be reversed):

1. `shiftDistance_symm` — Δ(u) = Δ(−u) requires the support-invariance
   hypothesis (`S = S.image (· + u)`) **and** the re-indexation of the
   sum by `−u`. Without the former, the lemma is false in general:
   `|P (x + u) − P x| ≠ |P (x − u) − P x|` for asymmetric P.

2. `shiftDistance_le_one` — Δ(P, u) ≤ ½ · ‖P‖₁ by triangle inequality,
   hence Δ ≤ 1 under mass 1. Two distinct conditions: `|P (x + u) − P x| ≤
   P (x + u) + P x` under positivity of `P`, and the transfer of the
   mass `∑_{x ∈ S} P (x + u) = ∑_{x ∈ S} P x` — that is the
   `sum_translate_image` organ of `Split.lean`.

Closed bricks in this commit: `shiftDistance`, `shiftDistance_zero`,
`shiftDistance_nonneg`, `shiftDistance_eq_zero_of_zero`,
`shiftDistance_eq_zero_of_invariant`. Module builds
(`lake build Discrepancy.Komlos.ShiftDistance_en` SUCCESS expected), 0
`sorry` in code. -/

end Discrepancy.Komlos_en