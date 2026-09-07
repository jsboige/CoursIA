/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## CHSH inequality: classical boundary for randomized strategies

The deterministic slice (`CHSH_en.lean`) showed that every deterministic
local strategy has a CHSH score of absolute value exactly 2. This module
handles the next step: shared randomness does not allow a classical local
model to cross this boundary. Since every deterministic profile has a score
of absolute value 2, any convex combination (finite family of non-negative
rational weights summing to 1) keeps an expected score of absolute value at
most 2.

This second slice of the quantum pilot from Epic #13106 is deliberately
bounded. It formalizes neither quantum states, nor Hermitian observables, nor
the quantum bound 2√2 (Tsirelson), which should instantiate the existing
Mathlib theorem rather than duplicate it.

Sources:
- J. F. Clauser, M. A. Horne, A. Shimony, R. A. Holt,
  "Proposed Experiment to Test Local Hidden-Variable Theories",
  Physical Review Letters 23 (1969), 880-884.
- B. S. Tsirelson, "Quantum generalizations of Bell's inequality",
  Letters in Mathematical Physics 4 (1980), 93-100.
-/

import Conway.CHSH_en
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Conway_en
namespace CHSHRandomized_en

/-- A deterministic local profile: a quadruple of binary outcomes, one per
setting of Alice (`a₀`, `a₁`) and of Bob (`b₀`, `b₁`). The type is finite of
cardinality 16 (2^4). -/
abbrev Profile := CHSH_en.Outcome × CHSH_en.Outcome × CHSH_en.Outcome × CHSH_en.Outcome

/-- Finiteness instance on `CHSH_en.Outcome`, needed to sum over the 16
profiles. `Outcome` has exactly two elements (`negative` and `positive`). -/
instance : Fintype CHSH_en.Outcome where
  elems := {CHSH_en.Outcome.negative, CHSH_en.Outcome.positive}
  complete := by
    intro x; cases x <;> simp

/-- CHSH score of a deterministic profile, reusing `CHSH_en.score`. -/
def Profile.score (p : Profile) : ℤ :=
  CHSH_en.score p.1 p.2.1 p.2.2.1 p.2.2.2

/-- Absolute value of a profile score: always 2 (deterministic classical
boundary, cf. `CHSH_en.classical_abs_score`). -/
theorem Profile.abs_score (p : Profile) : |Profile.score p| = 2 := by
  dsimp [Profile.score]
  exact CHSH_en.classical_abs_score p.1 p.2.1 p.2.2.1 p.2.2.2

/-- A randomized deterministic local strategy is a finite family of rational
weights over the 16 profiles. -/
abbrev Strategy := Profile → ℚ

/-- Expected CHSH score of a randomized strategy: convex contribution of the
deterministic scores. -/
def expectedScore (μ : Strategy) : ℚ :=
  ∑ p : Profile, μ p * (Profile.score p : ℚ)

/-- Absolute value (in ℚ) of a profile score: always 2. This rational variant
is the form the expectation uses. -/
theorem Profile.abs_score_rat (p : Profile) : |(Profile.score p : ℚ)| = 2 := by
  rw [← Int.cast_abs]
  exact_mod_cast Profile.abs_score p

/-- **Classical boundary for randomized strategies.** Any convex combination
of deterministic profiles keeps an expected CHSH score of absolute value at
most 2. The proof combines the triangle inequality for the absolute value of
a sum and the deterministic bound `CHSH_en.classical_abs_score` on each
profile. -/
theorem randomized_bound (μ : Strategy)
    (h_nonneg : ∀ p, 0 ≤ μ p)
    (h_total : (∑ p : Profile, μ p) = 1) :
    |expectedScore μ| ≤ 2 := by
  calc
    |expectedScore μ| =
        |∑ p : Profile, μ p * (Profile.score p : ℚ)| := by
      rfl
    _ ≤ ∑ p : Profile, |μ p * (Profile.score p : ℚ)| := by
      exact Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset Profile))
        (f := fun p : Profile => μ p * (Profile.score p : ℚ))
    _ = ∑ p : Profile, μ p * |(Profile.score p : ℚ)| := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [abs_mul, abs_of_nonneg (h_nonneg p)]
    _ ≤ ∑ p : Profile, μ p * (2 : ℚ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (le_of_eq (Profile.abs_score_rat p)) (h_nonneg p)
    _ = 2 := by
      rw [← Finset.sum_mul]
      rw [h_total]
      norm_num

/-- The fully `positive` deterministic profile. -/
def pPos : Profile := (.positive, .positive, .positive, .positive)

/-- The mirror profile where Alice answers `negative` on both her settings and
Bob `positive`. It is the antisymmetric profile of `pPos`. -/
def pNeg : Profile := (.negative, .negative, .positive, .positive)

/-- Score of the all-`positive` profile: 2 (deterministic bound reached). -/
theorem Profile.score_pPos : Profile.score pPos = 2 := by
  decide

/-- Score of the mirror profile: -2. -/
theorem Profile.score_pNeg : Profile.score pNeg = -2 := by
  decide

/-- The deterministic (Dirac) strategy concentrated on a single profile. -/
def dirac (p : Profile) : Strategy := fun q => if q = p then (1 : ℚ) else 0

/-- The balanced strategy on the two antagonist profiles `pPos` and `pNeg`,
each of weight 1/2. -/
def balancedMix : Strategy := fun q => if q = pPos ∨ q = pNeg then (1 / 2 : ℚ) else 0

/-- Expected score of a Dirac: only the supporting profile's contribution
remains. -/
theorem expectedScore_dirac (p : Profile) : expectedScore (dirac p) = (Profile.score p : ℚ) := by
  unfold expectedScore dirac
  simp

/-- A Dirac mixture at `pPos` reaches the upper bound: expected score 2, so
that the inequality `|expectedScore _| ≤ 2` is achieved. -/
example : expectedScore (dirac pPos) = 2 := by
  rw [expectedScore_dirac]
  exact_mod_cast Profile.score_pPos

/-- Additive linearity of the expected score: the expectation of a sum of
strategies is the sum of the expectations. -/
lemma expectedScore_add (μ ν : Strategy) :
    expectedScore (fun q => μ q + ν q) = expectedScore μ + expectedScore ν := by
  unfold expectedScore
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]

/-- Scalar linearity of the expected score: a constant weight factorizes. -/
lemma expectedScore_mul (k : ℚ) (μ : Strategy) :
    expectedScore (fun q => k * μ q) = k * expectedScore μ := by
  unfold expectedScore
  simp_rw [mul_assoc]
  rw [Finset.mul_sum]

/-- Decomposition of the balanced mixture as the half-sum of two Diracs (weight
1/2 each on `pPos` and `pNeg`). -/
theorem pPos_ne_pNeg : pPos ≠ pNeg := by
  decide

theorem balancedMix_eq : balancedMix = fun q => (1 / 2 : ℚ) * (dirac pPos q + dirac pNeg q) := by
  funext q
  by_cases hp : q = pPos <;> by_cases hn : q = pNeg <;>
    simp [balancedMix, dirac, hp, hn, pPos_ne_pNeg, pPos_ne_pNeg.symm]

/-- A balanced mixture of two antagonist profiles (score 2 and -2) gives an
expected score of zero: `expectedScore balancedMix = 0`. The contributions of
`pPos` (+2) and of `pNeg` (-2) cancel out. -/
theorem balancedMix_eq_zero : expectedScore balancedMix = 0 := by
  rw [balancedMix_eq]
  rw [expectedScore_mul]
  rw [expectedScore_add]
  rw [expectedScore_dirac, expectedScore_dirac]
  rw [Profile.score_pPos, Profile.score_pNeg]
  norm_num

end CHSHRandomized_en
end Conway_en
