/-!
# Geometric Discount — Proved Identities

Lemmas about geometric discounting using Mathlib's real analysis.
These are the building blocks for the Gittins index formalization.
-/

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Order
import Mathlib.Data.Real.Basic

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
  exact tsum_geometric_of_lt_one hγ₁ hγ₂

/-- For 0 ≤ γ < 1, 1 - γ > 0. -/
lemma one_minus_gamma_pos {γ : ℝ} (h : γ < 1) (h₀ : 0 ≤ γ) : 0 < 1 - γ := by
  linarith

/-- For 0 < γ < 1, the discounted infinite sum of a constant reward r equals r/(1-γ).
    This is the fundamental identity used in bandit value computation. -/
theorem present_value_constant {γ r : ℝ} (hγ₁ : 0 < γ) (hγ₂ : γ < 1) (hr : 0 ≤ r) :
    ∑' n : ℕ, γ ^ n * r = r / (1 - γ) := by
  have hγ₁' : 0 ≤ γ := le_of_lt hγ₁
  rw [← tsum_geometric_of_lt_one hγ₁' hγ₂]
  -- tsum_geometric_of_lt_one gives us Σ γ^n = 1/(1-γ)
  -- Multiply both sides by r
  simp [mul_comm r]
  ring_nf
  sorry  -- TODO: complete the mul cancellation proof

/-- Discount factor closer to 1 gives higher present value.
    If γ₁ ≤ γ₂, then Σ γ₁^n ≤ Σ γ₂^n. -/
theorem discount_monotone {γ₁ γ₂ : ℝ} (h₁ : 0 ≤ γ₁) (h₂ : γ₁ ≤ γ₂) (h₃ : γ₂ < 1) :
    ∑' n : ℕ, γ₁ ^ n ≤ ∑' n : ℕ, γ₂ ^ n := by
  sorry  -- TODO: requires tsum_le_tsum with termwise comparison

end Gittins
