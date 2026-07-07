import Mathlib

/-!
# Coherence.Basic — events, prices, tickets (de Finetti)

Foundations of the Dutch Book argument. A betting agent assigns a unit price
`q A` to each event `A` (a ticket paying 1 € if `A` occurs); the agent buys AND
sells at the same price `q A` (no bid–ask spread). De Finetti's theorem (finite
case) states that prices violating the probability axioms expose the agent to a
*Dutch Book* — a book of bets guaranteeing a sure loss. See `DutchBook.lean`.

This is the conceptual foundation of *why* probabilities are (additive,
normalised) rather than arbitrary belief functions: coherence *forces* the
Kolmogorov axioms. Pedagogically, this module answers the founding question of
the whole Probas series: "why `P(A∪B) = P(A) + P(B) − P(A∩B)`?" — because
otherwise, an arbitrageur builds a sure-loss bet.

Cross-references:
- Infer-14 (Infer.NET): Bayesian expected utility under posterior uncertainty.
- PyMC-1 (PyMC): expected utility estimation by posterior sampling.

English mirror of `Coherence/Basic.lean` (French canonical). Convention EPIC #4980:
siblings `Foo.lean` (FR) + `Foo_en.lean` (EN), both compile in one lake.
Drift-CI: non-docstring content byte-identical between siblings.
Sibling namespace: `Coherence_en` (the canonical FR remains `Coherence`).
-/

namespace Coherence_en

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- An event is a finite set of states of the world. -/
abbrev Event (Ω : Type*) [Fintype Ω] [DecidableEq Ω] := Finset Ω

/-- A price function (betting quotient): `q A` is the unit price (in €) of a
    ticket paying 1 € if the event `A` occurs. The agent buys and sells at the
    same price `q A` (no spread) — the standard de Finetti framework. -/
abbrev Price (Ω : Type*) [Fintype Ω] [DecidableEq Ω] := Event Ω → ℝ

/-- The indicator `𝟙_{ω ∈ A}` as a real (1 if the state `ω` realises `A`, 0 otherwise). -/
def ind (A : Event Ω) (ω : Ω) : ℝ := if ω ∈ A then 1 else 0

/-- Inclusion–exclusion identity for indicators:
    `𝟙_A + 𝟙_B − 𝟙_{A∩B} − 𝟙_{A∪B} = 0` at every state `ω`.

    This is the keystone of the Dutch Book: it makes the payoff of the four
    tickets deterministic (independent of the realised state). See `DutchBook.lean`.

    **Proof**: disjunction on the membership `(ω ∈ A, ω ∈ B)` (4 cases); in each
    case, the identity reduces to a trivial arithmetic equation. -/
lemma ind_inclusion_exclusion (A B : Event Ω) (ω : Ω) :
    ind A ω + ind B ω - ind (A ∩ B) ω - ind (A ∪ B) ω = 0 := by
  unfold ind
  simp only [Finset.mem_inter, Finset.mem_union]
  by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;> simp [hA, hB]

end Coherence_en
