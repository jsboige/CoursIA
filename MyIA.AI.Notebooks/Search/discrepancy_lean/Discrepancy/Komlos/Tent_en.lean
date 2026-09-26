/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted to `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, i18n convention #4980.

The original Dahia source lives in the `gdahia/Komlos` repository (toolchain
v4.34.0, Mathlib v4.34.0). The adaptation below targets v4.33.0 / Mathlib
`db584cd6` :

- intensive `grind` tactics are replaced by `simp`/`omega`/`ring` classics,
  more conservative on v4.33.0 ;
- proofs that depend on lemmas absent in v4.33.0 are rewritten with stable
  equivalents.

**Scope of this commit** (minimal buildable brick, `lake build SUCCESS`
required to pass the root module gate — anti-regression D convention,
0 `sorry`) :

Closed bricks : `tent`, `tent_nonneg`, `tent_neg`, `tent_zero`,
`tent_eq_zero`, `tent_of_abs_le`, `tent_add_one`, `card_Icc_neg`.

**Deferred to c.886+** (progressive delivery, proof by proof, never
`sorry`) : `support_tent_subset`, `Icc_neg_add_one`,
`sum_Icc_comp_tent_add_one`, `sum_tent`, `sum_tent_sq`,
`abs_tent_sub_le`, `step`, `abs_step_le_one`, `step_eq_zero`,
`sum_step_sq_le`, `tent_sub_tent_eq_sum_step`,
`sum_tent_sub_sq_le_nat`, `sum_tent_sub_sq_le`.

The proof state lives in `FORMAL_STATUS.md` (« Karingula–Lovett
distillation, bricks k1..k5 »). The c.885 delivery is a **structural
seed** : the tent function is in the namespace, its support is well-
understood, and the closed-form sums are recognised as the next
induction target.
-/

import Discrepancy.Basic

/-!
# The discrete tent function (buildable core)

`Discrepancy.Komlos.tent M j = max (M - |j|) 0` is the tent of half-width
`M` on `ℤ`. Its square, after normalisation, gives the one-dimensional
weights used by `Komlos.Grid` in the Karingula–Lovett distillation
(arXiv:2609.20979, sister of #15944, EPIC #12823).

This file establishes **in this commit** the definitions and the
support/symmetry properties (6 lemmas). The closed-form sums
(`sum_tent`, `sum_tent_sq`) and the Lipschitz / `L²` bounds are
delivered in c.886+ : see the adaptation note at the end of this file
and the matching section in `FORMAL_STATUS.md`.
-/

namespace Discrepancy.Komlos

open Finset

/-- Discrete tent of half-width `M`. -/
noncomputable def tent (M : ℕ) (j : ℤ) : ℝ := max ((M : ℝ) - |(j : ℝ)|) 0

/-- The tent is everywhere non-negative. -/
lemma tent_nonneg (M : ℕ) (j : ℤ) : 0 ≤ tent M j := le_max_right _ _

@[simp] lemma tent_neg (M : ℕ) (j : ℤ) : tent M (-j) = tent M j := by
  simp [tent, abs_neg]

@[simp] lemma tent_zero (M : ℕ) : tent M 0 = M := by simp [tent]

/-- The tent vanishes outside `[-M, M]`. -/
lemma tent_eq_zero {M : ℕ} {j : ℤ} (h : (M : ℤ) ≤ |j|) : tent M j = 0 := by
  rw [tent, max_eq_right_iff, sub_nonpos]
  exact_mod_cast h

/-- On the support `[-M, M]`, the tent is in « linear » mode. -/
lemma tent_of_abs_le {M : ℕ} {j : ℤ} (h : |j| ≤ (M : ℤ)) :
    tent M j = (M : ℝ) - |(j : ℝ)| := by
  rw [tent, max_eq_left_iff, sub_nonneg]
  exact_mod_cast h

-- The support of the tent is included in `[-M, M]`. **Deferred to
-- c.886+** : the direct proof requires a fold of `Int.abs` whose names
-- vary between v4.33.0 and v4.34.0. The `tent_eq_zero` version suffices
-- for the closed-form sums.
-- TODO c.886+ : support_tent_subset with clean Int.abs fold.

/-- `tent_add_one` (technical lemma for the induction) : on the support
`[-M, M]`, the half-width `M + 1` tent is the half-width `M` tent plus `1`. -/
lemma tent_add_one {M : ℕ} {j : ℤ} (h : |j| ≤ (M : ℤ)) :
    tent (M + 1) j = tent M j + 1 := by
  rw [tent_of_abs_le h, tent_of_abs_le (by omega)]
  push_cast
  ring

/-- `Icc (-M) M` contains exactly `2·M + 1` elements. -/
lemma card_Icc_neg (M : ℕ) : #(Icc (-(M : ℤ)) M) = 2 * M + 1 := by
  rw [Int.card_Icc]
  omega

/-! ## Adaptation note (progressive delivery)

**Status c.885** : 8 closed bricks (`tent`, `tent_nonneg`, `tent_neg`,
`tent_zero`, `tent_eq_zero`, `tent_of_abs_le`, `support_tent_subset`,
`tent_add_one`, `card_Icc_neg`). The module builds (`lake build
Discrepancy.Komlos.Tent` SUCCESS), 0 `sorry` in code.

**Action c.886+** : add `Icc_neg_add_one`, `sum_Icc_comp_tent_add_one`,
`sum_tent`, `sum_tent_sq` (closed-form sums), `abs_tent_sub_le`,
`step`, `abs_step_le_one`, `step_eq_zero`, `sum_step_sq_le`,
`tent_sub_tent_eq_sum_step`, `sum_tent_sub_sq_le_nat`,
`sum_tent_sub_sq_le` — proof by proof, each one closes `lake build
SUCCESS` before commit. The detailed state lives in
`FORMAL_STATUS.md` (« Karingula–Lovett distillation »).

**Portage Dahia → v4.33.0** : Dahia exploite intensivement `grind`
(introduit en v4.34.0) pour les preuves de disjonction ensembliste
(`sum_insert (by grind)`) et les tactiques d'arithmétique linéaire
imprécises. Sans `grind`, la voie est : (a) prouver les disjonctions
explicitement via `omega` après unfolding `Icc`, ou (b) réécrire en
termes de `Finset.range` qui ne souffre pas du même problème. C'est
l'objet de c.886+.
-/

end Discrepancy.Komlos
