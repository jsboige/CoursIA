/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## CHSH inequality: deterministic classical boundary

Clauser, Horne, Shimony, and Holt (1969) proposed an experimentally testable
Bell inequality with two binary observables per party. This module formalizes
its classical kernel: in every deterministic local strategy, each
predetermined response is -1 or +1 and the CHSH score has absolute value
exactly 2. Any correlation exceeding 2 therefore lies outside this classical
model.

This first slice of the quantum pilot from Epic #13106 is deliberately
bounded. It does not yet claim to formalize Tsirelson's quantum bound 2√2,
which requires Hermitian observables and an operator norm. The module thereby
keeps a verifiable boundary between the delivered certificate and the open
analytic continuation.

Sources:
- J. F. Clauser, M. A. Horne, A. Shimony, R. A. Holt,
  "Proposed Experiment to Test Local Hidden-Variable Theories",
  Physical Review Letters 23 (1969), 880-884.
- B. S. Tsirelson, "Quantum generalizations of Bell's inequality",
  Letters in Mathematical Physics 4 (1980), 93-100.
-/

import Mathlib.Tactic.Ring

namespace Conway_en
namespace CHSH_en

/-- Predetermined binary outcome of a classical measurement. -/
inductive Outcome
  | negative
  | positive
  deriving DecidableEq

/-- Standard numerical encoding of the outcomes as `-1` and `+1`. -/
def Outcome.value : Outcome → ℤ
  | .negative => -1
  | .positive => 1

/-- Every classical outcome is a sign, so its square is one. -/
theorem Outcome.value_sq (outcome : Outcome) : outcome.value ^ 2 = 1 := by
  cases outcome <;> decide

/-- CHSH score of a deterministic local strategy.

`a₀`, `a₁` are Alice's predetermined responses and `b₀`, `b₁` are Bob's.
Locality is encoded by each response depending only on its own party's
setting. -/
def score (a₀ a₁ b₀ b₁ : Outcome) : ℤ :=
  a₀.value * b₀.value + a₀.value * b₁.value +
    a₁.value * b₀.value - a₁.value * b₁.value

/-- Factorization exposing the two classical branches: depending on whether
Bob's responses agree or disagree, exactly one of the two terms contributes. -/
theorem score_factorization (a₀ a₁ b₀ b₁ : Outcome) :
    score a₀ a₁ b₀ b₁ =
      a₀.value * (b₀.value + b₁.value) +
        a₁.value * (b₀.value - b₁.value) := by
  simp only [score]
  ring

/-- **Classical CHSH boundary.** Every deterministic local strategy reaches
the classical boundary exactly: the absolute value of its score is `2`.

The proof enumerates the 16 assignments of four binary outcomes. Here,
`decide` is a kernel computation over a finite type, with no axiom or native
code. -/
theorem classical_abs_score (a₀ a₁ b₀ b₁ : Outcome) :
    |score a₀ a₁ b₀ b₁| = 2 := by
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;> decide

/-- Usual CHSH inequality for deterministic strategies. -/
theorem classical_bound (a₀ a₁ b₀ b₁ : Outcome) :
    |score a₀ a₁ b₀ b₁| ≤ 2 := by
  rw [classical_abs_score]

/-- A classical strategy attaining the upper bound `+2`. -/
example : score .positive .positive .positive .positive = 2 := by
  decide

/-- A classical strategy attaining the lower bound `-2`. -/
example : score .negative .negative .positive .positive = -2 := by
  decide

end CHSH_en
end Conway_en
