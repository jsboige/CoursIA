import Mathlib

/-!
# Basic Definitions — Lotteries and Expected Value

Core types for decision theory under risk: lotteries (finite-support
probability distributions over a finite outcome space), expected value of a
utility function, and convex mixtures of lotteries.

These are the primitives on which the von Neumann–Morgenstern axioms and the
expected-utility representation theorem are built (see `Axioms` and
`Representation`).

Cross-references:
- Infer-14 (Infer.NET): Bayesian expected utility under posterior uncertainty.
- PyMC-1 (PyMC): expected utility estimation by posterior sampling.
-/

namespace Utility

variable {α : Type*} [Fintype α]

/-- A lottery is an assignment of non-negative weights to each outcome,
summing to 1. Equivalently, a finitely-supported probability distribution
over the outcome type `α`. -/
structure Lottery (α : Type*) [Fintype α] where
  /-- Probability weight of each outcome. -/
  probs : α → ℝ
  /-- Every weight is non-negative. -/
  nonneg : ∀ a : α, 0 ≤ probs a
  /-- Weights sum to one (normalisation). -/
  sum_one : ∑ a : α, probs a = 1

/-- The expected value of a function `f` (typically a utility function) under
the distribution `p`. -/
def expectation (p : Lottery α) (f : α → ℝ) : ℝ :=
  ∑ a : α, p.probs a * f a

/-- The mixture `t • p + (1 - t) • r` of two lotteries. Defined for `t ∈ [0,1]`,
which guarantees the mixture is again a valid lottery. -/
def mix (t : ℝ) (p r : Lottery α) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Lottery α where
  probs a := t * p.probs a + (1 - t) * r.probs a
  nonneg a := by
    refine add_nonneg ?_ ?_
    · exact mul_nonneg ht0 (p.nonneg a)
    · exact mul_nonneg (by linarith) (r.nonneg a)
  sum_one := by
    have key :
      ∑ a : α, (t * p.probs a + (1 - t) * r.probs a) =
        t * ∑ a : α, p.probs a + (1 - t) * ∑ a : α, r.probs a := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [key, p.sum_one, r.sum_one]
    ring

/-- Linearity of expectation under mixtures: the expected utility of a mixture
is the corresponding mixture of expected utilities. This affine identity is the
algebraic heart of the independence axiom. -/
theorem expectation_mix (t : ℝ) (p r : Lottery α) (f : α → ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    expectation (mix t p r ht0 ht1) f = t * expectation p f + (1 - t) * expectation r f := by
  simp only [expectation, mix]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun a _ => by ring)

/-- Expected utility is additive in the utility function. -/
theorem expectation_add (p : Lottery α) (f g : α → ℝ) :
    expectation p (fun a => f a + g a) = expectation p f + expectation p g := by
  simp only [expectation]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun a _ => by ring)

/-- Expected utility is homogeneous in the utility function. -/
theorem expectation_smul (c : ℝ) (p : Lottery α) (f : α → ℝ) :
    expectation p (fun a => c * f a) = c * expectation p f := by
  simp only [expectation]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun a _ => by ring)

/-- The expectation of a constant utility is that constant (weights sum to one). -/
theorem expectation_const (p : Lottery α) (c : ℝ) :
    expectation p (fun _ => c) = c := by
  simp only [expectation]
  rw [← Finset.sum_mul, p.sum_one]
  ring

/-- Expectation is affine in the utility: `E_p[a·u + b] = a·E_p[u] + b`. This is
the key identity behind affine uniqueness of utility representations. -/
theorem expectation_affine (p : Lottery α) (a b : ℝ) (u : α → ℝ) :
    expectation p (fun x => a * u x + b) = a * expectation p u + b := by
  rw [expectation_add p (fun x => a * u x) (fun _ => b), expectation_smul, expectation_const]

end Utility
