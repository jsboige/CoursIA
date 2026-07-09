import Mathlib
import Utility.Basic

/-!
# von Neumann–Morgenstern Axioms (English mirror)

The four axioms a preference over lotteries must satisfy to admit an
expected-utility representation:

1. **Completeness** — any two lotteries are comparable.
2. **Transitivity** — preference chains do not cycle.
3. **Independence (substitution)** — a common mixture preserves preference.
4. **Continuity (Archimedean)** — no lottery is infinitely better or worse
   than another; intermediate mixtures exist.

A preference satisfying all four is `IsRational`.

English mirror of `Axioms.lean` (French canonical). Convention EPIC #4980:
siblings `Foo.lean` (FR) + `Foo_en.lean` (EN), both compile in one lake.
-/

namespace Utility_en

open Utility

variable {α : Type*} [Fintype α]

/-- A preference relation is a binary relation on lotteries. Read `P p q` as
"lottery `p` is weakly preferred to lottery `q`" (p ≽ q). -/
abbrev Pref (α : Type*) [Fintype α] := Lottery α → Lottery α → Prop

/-- Strict preference derived from a weak one: `p ≻ q` means `p ≽ q` but not
`q ≽ p`. -/
def StrictPref (P : Pref α) (p q : Lottery α) : Prop := P p q ∧ ¬ P q p

/-- Indifference derived from a weak preference: `p ~ q` means `p ≽ q` **and**
`q ≽ p` (each lottery is weakly preferred to the other). This is the symmetric
twin of `StrictPref`: together they split a complete preference into its strict
skeleton and its indifference relation. -/
def Indiff (P : Pref α) (p q : Lottery α) : Prop := P p q ∧ P q p

/-- **Completeness**: any two lotteries are comparable in at least one
direction. -/
def IsComplete (P : Pref α) : Prop :=
  ∀ p q : Lottery α, P p q ∨ P q p

/-- **Transitivity**: preference chains propagate. -/
def IsTransitive (P : Pref α) : Prop :=
  ∀ p q r : Lottery α, P p q → P q r → P p r

/-- **Independence (substitution)**: if `p ≽ q`, then mixing both with the same
third lottery `r` preserves the preference, for any mixing weight `t ∈ [0,1]`. -/
def IsIndependent (P : Pref α) : Prop :=
  ∀ (p q r : Lottery α) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1),
    P p q → P (mix t p r ht0 ht1) (mix t q r ht0 ht1)

/-- **Continuity (Archimedean / mixture solvability)**: if `p ≽ q ≽ r`, then
some convex mixture of `p` and `r` is indifferent to `q`. Equivalently, no
lottery is infinitely better or worse than another; `q` can always be matched
by mixing the extremes. This is the standard solvability form of the Archimedean
axiom, equivalent to the two-witness "no lexicographic dominance" form for
complete transitive orders. -/
def IsContinuous (P : Pref α) : Prop :=
  ∀ p q r : Lottery α,
    P p q → P q r →
      ∃ (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1),
        P (mix t p r ht0 ht1) q ∧ P q (mix t p r ht0 ht1)

/-- A **rational** preference satisfies all four VNM axioms. -/
structure IsRational (P : Pref α) : Prop where
  protected complete : IsComplete P
  protected transitive : IsTransitive P
  protected independent : IsIndependent P
  protected continuous : IsContinuous P

end Utility_en
