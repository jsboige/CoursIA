/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## CHSH inequality: randomized classical local strategies

This module extends the deterministic classical boundary of
`Conway_en.CHSH_en` to randomized classical strategies, i.e., to finite
rational mixtures of deterministic local profiles. For such mixtures, the
expected CHSH score remains bounded in absolute value by `2`: the
deterministic classical bound is preserved under convex combination.

This slice is the second formal step of the quantum pilot from
EPIC #13106, after the deterministic bound of `Conway_en.CHSH_en`
(PR #14132). It does not claim to formalize Tsirelson's quantum bound
`2√2`, which requires Hermitian observables and an operator norm — it
only makes explicit the second classical step of Bell's analytic
program: shared randomness does not let a classical local model exceed
the deterministic bound.

Sources:
- J. F. Clauser, M. A. Horne, R. Shimony, R. A. Holt, "Proposed
  Experiment to Test Local Hidden-Variable Theories", Physical
  Review Letters 23 (1969), 880-884.
- J. S. Bell, "On the Einstein-Podolsky-Rosen Paradox", Physics
  Physique Fizika 1 (1964), 195-200.
- B. S. Tsirelson, "Quantum generalizations of Bell's inequality",
  Letters in Mathematical Physics 4 (1980), 93-100.
-/

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.Finset

import Conway_en.CHSH_en

namespace Conway_en
namespace CHSHRandomized_en

open CHSH_en
open Finset

/-- Deterministic local profile: the four predetermined binary responses
of Alice (`a₀`, `a₁`) and Bob (`b₀`, `b₁`). Locality is encoded by the
fact that each response depends only on the setting of its own party. -/
abbrev Profile := Outcome × Outcome × Outcome × Outcome

/-- The 16 deterministic local profiles of a binary 2 × 2 scenario. -/
def allProfiles : Finset Profile :=
  univ ×ˢ univ ×ˢ univ ×ˢ univ

/-- Expected cardinality: `|allProfiles| = 16`. The proof is by
enumeration of the four components (`Outcome` has two constructors, so
`2^4 = 16`). -/
theorem card_allProfiles : #allProfiles = 16 := by
  simp [allProfiles, Outcome]

/-- Finite discrete distribution on profiles: a family of non-negative
rational weights summing to `1`. This structure formalizes a randomized
classical local strategy. -/
structure Distribution where
  weight : Profile → ℚ
  nonneg : ∀ p, 0 ≤ weight p
  sums_to_one : ∑ p ∈ allProfiles, weight p = 1

/-- CHSH score of a profile, by direct reuse of `CHSH_en.score`. -/
def profileScore (p : Profile) : ℤ :=
  let (a₀, a₁, b₀, b₁) := p
  score a₀ a₁ b₀ b₁

/-- Expected CHSH score under the distribution `μ`: convex combination
of deterministic scores, weighted by the rational weights. -/
def expectedScore (μ : Distribution) : ℚ :=
  ∑ p ∈ allProfiles, μ.weight p * (profileScore p : ℚ)

/-- **Randomized classical bound.** The expected CHSH score of any
randomized classical local strategy remains bounded in absolute value
by the classical boundary `2`.

The proof combines three facts:
1. every deterministic score has absolute value exactly `2`
   (`CHSH_en.classical_abs_score`) ;
2. the weighted sum preserves the absolute-value bound via the triangle
inequality (`Finset.abs_sum_le_sum_abs`) ;
3. the weights sum to `1`, so the weighted sum of absolute values is
`2`. -/
theorem randomized_bound (μ : Distribution) :
    |expectedScore μ| ≤ 2 := by
  unfold expectedScore
  have h_triangle :
      |∑ p ∈ allProfiles, μ.weight p * (profileScore p : ℚ)| ≤
        ∑ p ∈ allProfiles, μ.weight p * |(profileScore p : ℚ)| :=
    Finset.abs_sum_le_sum_abs
      (s := allProfiles) (f := fun p => μ.weight p * (profileScore p : ℚ))
  have h_const :
      (∑ p ∈ allProfiles, μ.weight p * |(profileScore p : ℚ)|) = 2 := by
    have h :
        ∀ p ∈ allProfiles,
          (|(profileScore p : ℚ)| : ℚ) = (2 : ℚ) := by
      intro p hp
      obtain ⟨a₀, a₁, b₀, b₁⟩ := p
      have h2 : |score a₀ a₁ b₀ b₁| = 2 := classical_abs_score a₀ a₁ b₀ b₁
      rw [profileScore]
      rw [Int.cast_abs, ← h2]
      norm_num
    rw [Finset.sum_congr rfl h, Finset.sum_const]
    rw [← Finset.sum_mul]
    rw [μ.sums_to_one]
    norm_num
  exact h_triangle.trans_eq h_const

/-- The Dirac at a profile `p₀` is a valid distribution. -/
def dirac (p₀ : Profile) : Distribution where
  weight := fun p => if p = p₀ then 1 else 0
  nonneg := by
    intro p
    by_cases hp : p = p₀
    · simp [hp]
    · simp [hp]
  sums_to_one := by
    rw [Finset.sum_ite_eq' allProfiles]
    simp

/-- Expected score of the Dirac at `p₀`: it equals `profileScore p₀`. -/
theorem expectedScore_dirac (p₀ : Profile) :
    expectedScore (dirac p₀) = (profileScore p₀ : ℚ) := by
  unfold expectedScore dirac
  rw [Finset.sum_ite_eq allProfiles
      (fun p => (1 : ℚ) * (profileScore p : ℚ))
      (fun p => (0 : ℚ) * (profileScore p : ℚ))]
  simp

/-- Extremal case: the Dirac at a profile that attains the upper
classical bound yields an expected score `+2`. -/
theorem expectedScore_dirac_upper :
    expectedScore (dirac (.positive, .positive, .positive, .positive)) = 2 := by
  rw [expectedScore_dirac, profileScore]
  norm_num [score, Outcome.value]

/-- **Score of the flipped profile.** Swapping Bob's two responses flips
the sign of the CHSH score. -/
def flipBob (a₀ a₁ b₀ b₁ : Outcome) : Profile :=
  (a₀, a₁, b₁, b₀)

theorem score_flipBob_neg (a₀ a₁ b₀ b₁ : Outcome) :
    score a₀ a₁ (flipBob a₀ a₁ b₀ b₁).2.2.1 (flipBob a₀ a₁ b₀ b₁).2.2.2
      = -score a₀ a₁ b₀ b₁ := by
  unfold flipBob score
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;> decide

/-- Symmetry case: the balanced mixture between `p₀` and its
"flipped-Bob" profile gives an expected score of `0`. -/
def balanced (p₀ : Profile) : Distribution where
  weight := fun p =>
    if p = p₀ ∨ p = flipBob p₀.1 p₀.2.1 p₀.2.2.1 p₀.2.2.2 then 1 / 2 else 0
  nonneg := by
    intro p
    by_cases h : p = p₀ ∨ p = flipBob p₀.1 p₀.2.1 p₀.2.2.1 p₀.2.2.2
    · simp [h]
    · simp [h]
  sums_to_one := by
    rw [Finset.sum_ite_eq' allProfiles]
    simp

/-- Expected score of the balanced mixture between `p₀` and its
"flipped-Bob" profile: it equals `0`. -/
theorem expectedScore_balanced (p₀ : Profile) :
    expectedScore (balanced p₀) = 0 := by
  unfold expectedScore balanced
  rw [Finset.sum_ite_eq allProfiles
      (fun p =>
        if p = p₀ then (1 / 2 : ℚ) * (profileScore p : ℚ)
        else (1 / 2 : ℚ) * (profileScore p : ℚ))
      (fun p => (0 : ℚ) * (profileScore p : ℚ))]
  obtain ⟨a₀, a₁, b₀, b₁⟩ := p₀
  have hp₀ : (p₀ = p₀) ∨ (p₀ = flipBob a₀ a₁ b₀ b₁) := Or.inl rfl
  have hp₁ : (flipBob a₀ a₁ b₀ b₁ = p₀) ∨
      (flipBob a₀ a₁ b₀ b₁ = flipBob a₀ a₁ b₀ b₁) := Or.inr rfl
  rw [hp₀, hp₁]
  rw [profileScore, profileScore]
  rw [score_flipBob_neg]
  ring

end CHSHRandomized_en
end Conway_en
