import Mathlib
import SLT.GaussianLipConcen

/-!
# Grain 3 — Norm tails ‖w‖, ‖hᵢ‖ (Gaussian Lipschitz concentration)

This module proves the **concentration of the norms** of the MIMO detector
(Papailiopoulos 2026 paper, §11 — cf issue #11148, grain 3): the noise `w`
and each channel column `hᵢ` (i.i.d. Gaussian entries) are standard Gaussian
vectors of dimension `M`, and the Euclidean norm is a **1-Lipschitz**
function — the concentration theorem
`gaussian_lipschitz_concentration` of the external lake
`YuanheZ/lean-stat-learning-theory` (SLT) therefore gives, for every `t > 0`,

    P(|‖X‖ − E‖X‖| ≥ t) ≤ 2·exp(−t²/2).

This is the **norm tail** of §11: it bounds uniformly the sizes of `‖w‖`
and `‖hᵢ‖` that appear in the flip score `s·‖hᵢ‖² + √s·⟪hᵢ,w⟫`
(Phase 2, `mimo_flip_cost`) — the next grains combine these tails by union
bound over the `N` columns. The Lipschitz route is the "light" version of
§11: the chi-square tail of `‖w‖²` via Hanson–Wright
(`chisq_norm_concentration`, Converse.lean — issue #11152) remains the
sledgehammer for the quadratic form, while here the norm itself concentrates
sub-Gaussianly with constant `1`.

Architecture of the file:

1. `norm_lipschitz_one` — the Euclidean norm on `EuclideanSpace ℝ (Fin n)`
   is **1-Lipschitz** (reverse triangle inequality, via
   `dist_norm_norm_le`) — the `LipschitzWith` certificate required by SLT ;
2. `norm_concentration_one_sided` / `norm_concentration` — the abstract
   theorems: (one-sided, then two-sided) concentration of `‖X‖` around its
   mean for `X` standard Gaussian of dimension `n`, direct instances of
   `gaussian_lipschitz_concentration(_one_sided)` with `L = 1` ;
3. `noise_norm_tail_one_sided` / `noise_norm_tail` — MIMO instantiations:
   tail of `‖w‖` (noise, `M` antennas) ;
4. `column_norm_tail` — MIMO instantiation: tail of `‖hᵢ‖` (a channel
   column, `M` i.i.d. `N(0,1)` entries).

Axioms: the three standard ones of Mathlib — zero sorry.
-/

namespace Mimo_en

open MeasureTheory ProbabilityTheory GaussianMeasure GaussianLipConcen Real
open scoped BigOperators NNReal

/-! ## Brick A — the Euclidean norm is 1-Lipschitz -/

/-- The Euclidean norm on `EuclideanSpace ℝ (Fin n)` is a **1-Lipschitz**
function: `|‖x‖ − ‖y‖| ≤ ‖x − y‖` (reverse triangle inequality).
This is the `LipschitzWith` certificate consumed by the SLT concentration
theorem — `dist_norm_norm_le` + `lipschitzWith_iff_dist_le_mul`. -/
lemma norm_lipschitz_one {n : ℕ} : LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa [dist_eq_norm] using dist_norm_norm_le x y

/-! ## Brick B — concentration of the norm of a standard Gaussian vector -/

/-- **One-sided norm tail (abstract form).** For `X` standard Gaussian on
`EuclideanSpace ℝ (Fin n)` (`n > 0`) and `t > 0`,

    P(‖X‖ − E‖X‖ ≥ t) ≤ exp(−t²/2).

Direct instance of `gaussian_lipschitz_concentration_one_sided` (SLT) with
`f = ‖·‖` and `L = 1`: `exp(−t²/(2·1²)) = exp(−t²/2)`. -/
theorem norm_concentration_one_sided {n : ℕ} (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    (stdGaussianE n {x : EuclideanSpace ℝ (Fin n) |
      t ≤ ‖x‖ - ∫ y, ‖y‖ ∂(stdGaussianE n)}).toReal ≤
      Real.exp (-(t ^ 2) / 2) := by
  simpa using gaussian_lipschitz_concentration_one_sided (n := n)
    (f := fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) (L := 1) hn (by norm_num)
    (norm_lipschitz_one (n := n)) t ht

/-- **Norm tail (abstract form).** For `X` standard Gaussian on
`EuclideanSpace ℝ (Fin n)` (`n > 0`) and `t > 0`,

    P(|‖X‖ − E‖X‖| ≥ t) ≤ 2·exp(−t²/2).

Direct instance of `gaussian_lipschitz_concentration` (SLT) with the
function `f = ‖·‖` and the Lipschitz constant `L = 1`: the norm is
1-Lipschitz (`norm_lipschitz_one`), hence sub-Gaussian concentration applies
with parameter `1` — `2·exp(−t²/(2·1²)) = 2·exp(−t²/2)`. -/
theorem norm_concentration {n : ℕ} (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    (stdGaussianE n {x : EuclideanSpace ℝ (Fin n) |
      t ≤ |‖x‖ - ∫ y, ‖y‖ ∂(stdGaussianE n)|}).toReal ≤
      2 * Real.exp (-(t ^ 2) / 2) := by
  simpa using gaussian_lipschitz_concentration (n := n)
    (f := fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) (L := 1) hn (by norm_num)
    (norm_lipschitz_one (n := n)) t ht

/-! ## Brick C — MIMO instantiations -/

/-- **One-sided tail of the noise norm `‖w‖`.** The noise `w` of the MIMO
detector is a standard Gaussian vector of dimension `M` (one coordinate per
measurement antenna): its norm concentrates around its mean with the tail
`exp(−t²/2)`. This bounds the size of the residual at the starting point
(`mimoObj_residual_from_zero`, Phase 4). -/
theorem noise_norm_tail_one_sided {M : ℕ} (hM : 0 < M) (t : ℝ) (ht : 0 < t) :
    (stdGaussianE M {w : EuclideanSpace ℝ (Fin M) |
      t ≤ ‖w‖ - ∫ y, ‖y‖ ∂(stdGaussianE M)}).toReal ≤
      Real.exp (-(t ^ 2) / 2) :=
  norm_concentration_one_sided hM t ht

/-- **Tail of the noise norm `‖w‖`.** The noise `w` of the MIMO detector is
a standard Gaussian vector of dimension `M` (one coordinate per measurement
antenna): its norm concentrates around its mean with the same tail
`2·exp(−t²/2)`. This bounds the size of the residual at the starting point
(`mimoObj_residual_from_zero`, Phase 4). -/
theorem noise_norm_tail {M : ℕ} (hM : 0 < M) (t : ℝ) (ht : 0 < t) :
    (stdGaussianE M {w : EuclideanSpace ℝ (Fin M) |
      t ≤ |‖w‖ - ∫ y, ‖y‖ ∂(stdGaussianE M)|}).toReal ≤
      2 * Real.exp (-(t ^ 2) / 2) :=
  norm_concentration hM t ht

/-- **Tail of a column norm `‖hᵢ‖`.** For a channel with i.i.d. `N(0,1)`
entries, the column `hᵢ = A eᵢ` is a standard Gaussian vector of dimension
`M`: its norm concentrates around its mean with the same tail
`2·exp(−t²/2)`. This bounds uniformly the `‖hᵢ‖` of the flip score
`s·‖hᵢ‖² + √s·⟪hᵢ,w⟫` (Phase 2, `mimo_flip_cost`) — the next grain combines
these tails by union bound over the `N` columns. -/
theorem column_norm_tail {M : ℕ} (hM : 0 < M) (t : ℝ) (ht : 0 < t) :
    (stdGaussianE M {h : EuclideanSpace ℝ (Fin M) |
      t ≤ |‖h‖ - ∫ y, ‖y‖ ∂(stdGaussianE M)|}).toReal ≤
      2 * Real.exp (-(t ^ 2) / 2) :=
  norm_concentration hM t ht

end Mimo_en
