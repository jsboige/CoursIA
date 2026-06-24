import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic

/-!
# Geometric Discount — Proved Identities

Lemmas about geometric discounting using Mathlib's real analysis.
These are the building blocks for the Gittins index formalization.
-/

namespace Gittins

open Real

/-!
## Geometric Series

The geometric series Σ γ^n converges to 1/(1-γ) for |γ| < 1.
Mathlib provides `tsum_geometric_of_lt_one` for this.
-/

/-- The partial sum of a geometric series: Σ_{k=0}^{n-1} γ^k -/
def geometricPartialSum (γ : ℝ) (n : ℕ) : ℝ :=
  (List.range n).foldl (fun acc k => acc + γ ^ k) 0

/-- For 0 ≤ γ < 1, the geometric series converges.
    This wraps Mathlib's `tsum_geometric_of_lt_one`. -/
theorem geometric_series_converges {γ : ℝ} (hγ₁ : 0 ≤ γ) (hγ₂ : γ < 1) :
    ∑' n : ℕ, γ ^ n = 1 / (1 - γ) := by
  rw [one_div]
  exact tsum_geometric_of_lt_one hγ₁ hγ₂

/-- For 0 ≤ γ < 1, 1 - γ > 0. -/
lemma one_minus_gamma_pos {γ : ℝ} (h : γ < 1) (h₀ : 0 ≤ γ) : 0 < 1 - γ := by
  linarith

/-- For 0 < γ < 1, the discounted infinite sum of a constant reward r equals r/(1-γ).
    This is the fundamental identity used in bandit value computation. -/
theorem present_value_constant {γ r : ℝ} (hγ₁ : 0 < γ) (hγ₂ : γ < 1) (hr : 0 ≤ r) :
    ∑' n : ℕ, γ ^ n * r = r / (1 - γ) := by
  have hγ₁' : 0 ≤ γ := le_of_lt hγ₁
  -- Sum_n gamma^n * r = (Sum_n gamma^n) * r = (1-gamma)^{-1} * r = r / (1-gamma)
  rw [tsum_mul_right, tsum_geometric_of_lt_one hγ₁' hγ₂]
  ring

/-- Discount factor closer to 1 gives higher present value.
    If γ₁ ≤ γ₂, then Σ γ₁^n ≤ Σ γ₂^n.

    **Proof strategy**: rewrite both tsums via the closed-form geometric
    identity `∑' n, γ^n = 1/(1-γ)` (`geometric_series_converges`), then reduce
    the goal to `1/(1-γ₁) ≤ 1/(1-γ₂)`. Since `γ₁ ≤ γ₂` we have
    `1-γ₂ ≤ 1-γ₁`, and both denominators are positive (`γ₂ < 1`), so
    `one_div_le_one_div_of_le` closes the goal. This sidesteps the missing
    `tsum_le_tsum` on `ℝ` (not available in Mathlib v4.30.0-rc2 for bare `ℝ`
    series) by exploiting the closed form. -/
theorem discount_monotone {γ₁ γ₂ : ℝ} (h₁ : 0 ≤ γ₁) (h₂ : γ₁ ≤ γ₂) (h₃ : γ₂ < 1) :
    ∑' n : ℕ, γ₁ ^ n ≤ ∑' n : ℕ, γ₂ ^ n := by
  have hγ₁_lt : γ₁ < 1 := lt_of_le_of_lt h₂ h₃
  have hγ₂_nn : 0 ≤ γ₂ := le_trans h₁ h₂
  rw [geometric_series_converges h₁ hγ₁_lt, geometric_series_converges hγ₂_nn h₃]
  -- Goal: 1 / (1 - γ₁) ≤ 1 / (1 - γ₂)
  -- Since γ₁ ≤ γ₂, we have 1 - γ₂ ≤ 1 - γ₁; both denominators are positive.
  apply one_div_le_one_div_of_le
  · exact sub_pos.mpr (by linarith)  -- 0 < 1 - γ₂
  · linarith                        -- 1 - γ₂ ≤ 1 - γ₁

end Gittins
