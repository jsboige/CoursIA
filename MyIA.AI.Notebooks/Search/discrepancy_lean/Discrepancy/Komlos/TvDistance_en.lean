/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted to `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

The original Dahia source lives in `gdahia/Komlos` : the definition in
`Komlos/ShiftDistance.lean` (`tvDist`, toolchain v4.34.0), the bound in
`Komlos/Hellinger.lean` (`tvDist_sq_le`). Both are written over `Finsupp`
(`E →₀ ℝ`). The adaptation below follows the lake convention established by
k1.1 (`ShiftDistance.lean`) : **explicit `Finset`** framework — the support is
a parameter, and it is *passed* to a lemma rather than *proved* as a hypothesis.

**What the encoding barrier does not touch.** The analytic core of
`tvDist_sq_le` is stated entirely on the weights `p q : ι → ℝ` and a finite
sum ; it is already delivered (k4.1, `Hellinger.lean`), with the factor `2⁻¹`
explicit. What the `Finsupp` encoding adds is only the rewriting
`tvDist P Q = 2⁻¹ * Σ |P x − Q x|` (`tvDist_eq_sum`), which consumes the
support hypotheses. In the `Finset` convention that rewriting is the
*definition* : `tvDistance s P Q` sums over `s` by construction, so the two
hypotheses `hPs` / `hQs` of the oracle vanish instead of being transported.
The loss is zero, and `Cube.lean` consumes the result without a
`Finsupp → Finset` bridge.

**Scope of this commit** (brick k4.2b, `lake build SUCCESS` required, 0
`sorry`) :

Bricks closed : `tvDistance` (the total variation distance of two weights on a
finite `Finset`), `tvDistance_nonneg`, `tvDistance_comm`,
`shiftDistance_eq_tvDistance` (the bridge to the k1.1 shift distance — a shift
*is* a total variation, that of a weight against its translate) and
`tvDistance_sq_le` — **the "distribution" version of Hellinger's bound** that
k4.1 explicitly postponed : for weights `p`, `q` of unit `L²` norm, the squared
total variation between the distributions `p ^ 2` and `q ^ 2` is bounded by the
`L²` distance between the weights.

**Consumed by** : `Komlos.Cube.shiftDistance_cubeF_sq_le` (the oracle's
`shiftDist_cubeP_sq_le`), the last statement of boute k4.2.
-/

import Discrepancy.Komlos.ShiftDistance_en
import Discrepancy.Komlos.Hellinger_en

/-!
# Total variation distance, `Finset` convention

`tvDistance s P Q = 2⁻¹ * Σ_{x ∈ s} |P x − Q x|` : the total variation
distance between two weights, summed over an **explicit** `Finset`.

As for `shiftDistance` (k1.1), `s` is an arbitrary `Finset` containing the
effective supports of `P` and `Q` — the definition stays correct when `s` is
larger, out-of-support contributions simply vanish. It is this convention that
makes the oracle's support hypotheses **disappear** : they are not lost, they
are *passed*.

The carrying result is `tvDistance_sq_le` : the "distribution" version of
Hellinger's inequality, postponed by k4.1 (`Hellinger.lean`) and consumed by
`Komlos.Cube`.
-/

namespace Discrepancy.Komlos_en

open Finset

variable {ι : Type*}

/-- Total variation distance `2⁻¹ · Σ_{x ∈ s} |P x − Q x|`.

The sum runs over `s`, an arbitrary `Finset` containing the effective supports
of `P` and `Q` : the definition stays correct when `s` is larger than needed. -/
noncomputable def tvDistance (s : Finset ι) (P Q : ι → ℝ) : ℝ :=
  (2⁻¹ : ℝ) * ∑ x ∈ s, |P x - Q x|

/-- `tvDistance s P Q ≥ 0` : it is a half-sum of absolute values. -/
lemma tvDistance_nonneg (s : Finset ι) (P Q : ι → ℝ) : 0 ≤ tvDistance s P Q := by
  unfold tvDistance
  exact mul_nonneg (by norm_num) (sum_nonneg fun x _ ↦ abs_nonneg _)

/-- `tvDistance` is symmetric in its two weights. -/
lemma tvDistance_comm (s : Finset ι) (P Q : ι → ℝ) :
    tvDistance s P Q = tvDistance s Q P := by
  unfold tvDistance
  congr 1
  exact sum_congr rfl fun x _ ↦ abs_sub_comm (P x) (Q x)

/-- **"Distribution" version of Hellinger's inequality.**

For weights `p`, `q` of unit `L²` norm on `s`, the squared total variation
distance between the distributions `p ^ 2` and `q ^ 2` is bounded by the `L²`
distance between the weights.

This is the statement `Komlos.Cube` consumes to bound the shift of the product
weight : `P` and `Q` there are `cubeF d N (· − a) ^ 2` and
`cubeF d N (· − b) ^ 2`, and `p`, `q` their roots.

Proof : the identity `|p² − q²| = |p + q| · |p − q|` reduces the goal to the
Cauchy–Schwarz inequality `(Σ a b)² ≤ (Σ a²)(Σ b²)` with `a = |p + q|` and
`b = |p − q|`, closed by `Σ (p + q)² ≤ 4`. The oracle's support hypotheses
`hPs` / `hQs` do not appear : they are absorbed by the explicit sum over `s`. -/
lemma tvDistance_sq_le {s : Finset ι} {P Q p q : ι → ℝ}
    (hP : ∀ x ∈ s, P x = p x ^ 2) (hQ : ∀ x ∈ s, Q x = q x ^ 2)
    (hp : ∑ x ∈ s, p x ^ 2 = 1) (hq : ∑ x ∈ s, q x ^ 2 = 1) :
    tvDistance s P Q ^ 2 ≤ ∑ x ∈ s, (p x - q x) ^ 2 := by
  have h : tvDistance s P Q = (2⁻¹ : ℝ) * ∑ x ∈ s, |p x ^ 2 - q x ^ 2| := by
    unfold tvDistance
    congr 1
    refine sum_congr rfl fun x hx ↦ ?_
    rw [hP x hx, hQ x hx]
  rw [h]
  exact half_sum_abs_sq_sub_sq_sq_le hp hq

/-- The `shiftDistance` of k1.1 **is** a total variation : that of a weight
against its translate.

`shiftDistance S P u = 2⁻¹ · Σ_{x ∈ S} |P (x + u) − P x|` and
`tvDistance S (fun x ↦ P (x + u)) P` carry the same sum : the statement is the
definition, written in the form `Komlos.Cube` consumes. -/
lemma shiftDistance_eq_tvDistance {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ) :
    shiftDistance S P u = tvDistance S (fun x ↦ P (x + u)) P := by
  unfold shiftDistance tvDistance
  rw [one_div]

/-! ## Adaptation note (brick k4.2b)

**Status** : 5 bricks closed — the oracle's `tvDist` / `tvDist_sq_le`
(`Komlos/ShiftDistance.lean` + `Komlos/Hellinger.lean`) is ported into the
lake's `Finset` convention, and the "distribution" version of Hellinger that
k4.1 had postponed is delivered.

**What changed with respect to the oracle** : the two support hypotheses
`hPs` / `hQs` of `tvDist_sq_le` are **gone**, absorbed by the explicit sum
over `s` (`tvDistance` sums over a given `Finset`, where `tvDist` sums over
the support of a `Finsupp`). This is the gain of the k1.1 convention, already
documented in the headers of `ShiftDistance.lean` and `Cube.lean` : the support
is *passed*, not *proved*. `tvDistance` is moreover stated for an arbitrary
type `ι` (the oracle states it over `[AddCommGroup E]`), the specialisation
`Fin d → ℤ` appearing only in the bridge `shiftDistance_eq_tvDistance`.

**Port v4.34 → v4.33.0** : `tvDistance_sq_le` is, up to two hypotheses, the
call of the `half_sum_abs_sq_sub_sq_sq_le` delivered by k4.1 — the oracle's
proof replays verbatim. Neither of the two error classes measured while
building k4.2a (`simpa` unavailable in term position at the pin ;
`simp only [sub_zero]` blind to `(0 : Fin d → ℤ) k`) is met here.

**Postponed to k4.3** : nothing in this module. Boute k4.3
(`NearInvariant.lean`, Lemma 1.5) awaits `shiftDist_push`, the only statement
still postponed from k2.3, with its reason measured inside `Transport.lean`
itself.
-/

end Discrepancy.Komlos_en