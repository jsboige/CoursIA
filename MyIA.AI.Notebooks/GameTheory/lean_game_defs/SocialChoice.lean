/-
  Social Choice Theory in Lean 4
  ==============================

  Formalizes key concepts from social choice theory:
  - Preferences and orderings
  - Social welfare functions
  - Arrow's axioms (Pareto, IIA, Non-dictatorship)
  - Arrow's Impossibility Theorem (statement)

  Based on GameTheory-19-Lean-SocialChoice.ipynb
  Inspired by asouther4/lean-social-choice (Lean 3)
-/

/-! ## Preferences -/

/-- A preference relation is a binary relation on alternatives -/
structure Preference (A : Type) where
  /-- R x y means "x is at least as good as y" -/
  R : A → A → Prop
  /-- Completeness: for any x, y, either R x y or R y x -/
  complete : ∀ x y, R x y ∨ R y x
  /-- Transitivity -/
  trans : ∀ x y z, R x y → R y z → R x z

/-- Strict preference: x is strictly preferred to y -/
def StrictPref {A : Type} (p : Preference A) (x y : A) : Prop :=
  p.R x y ∧ ¬p.R y x

/-- Indifference: x and y are equally good -/
def Indifferent {A : Type} (p : Preference A) (x y : A) : Prop :=
  p.R x y ∧ p.R y x

/-! ## Social Welfare Functions -/

/-- A social welfare function aggregates individual preferences into a social preference -/
structure SocialWelfareFunction (I A : Type) where
  /-- The aggregation function -/
  aggregate : (I → Preference A) → Preference A

/-! ## Arrow's Axioms -/

/-- Weak Pareto: If everyone strictly prefers x to y, society prefers x to y -/
def WeakPareto {I A : Type} (swf : SocialWelfareFunction I A) : Prop :=
  ∀ prefs : I → Preference A, ∀ x y,
    (∀ i, StrictPref (prefs i) x y) → StrictPref (swf.aggregate prefs) x y

/-- Independence of Irrelevant Alternatives (IIA) -/
def IIA {I A : Type} (swf : SocialWelfareFunction I A) : Prop :=
  ∀ prefs prefs' : I → Preference A, ∀ x y,
    -- If x vs y preferences are the same in both profiles
    (∀ i, (prefs i).R x y ↔ (prefs' i).R x y) →
    (∀ i, (prefs i).R y x ↔ (prefs' i).R y x) →
    -- Then social preference over x,y is the same
    ((swf.aggregate prefs).R x y ↔ (swf.aggregate prefs').R x y)

/-- Non-dictatorship: No single individual determines the social preference -/
def NonDictatorial {I A : Type} (swf : SocialWelfareFunction I A) : Prop :=
  ¬∃ d : I, ∀ prefs : I → Preference A, ∀ x y,
    StrictPref (prefs d) x y → StrictPref (swf.aggregate prefs) x y

/-! ## Arrow's Impossibility Theorem -/

/--
Arrow's Impossibility Theorem (Statement):
There is no social welfare function with ≥3 alternatives that satisfies:
1. Weak Pareto
2. Independence of Irrelevant Alternatives
3. Non-dictatorship
-/
-- Full proof requires extensive machinery; we state it as an axiom
axiom arrow_impossibility {I A : Type} [Fintype I] [Fintype A]
    (hI : Fintype.card I ≥ 2)
    (hA : Fintype.card A ≥ 3)
    (swf : SocialWelfareFunction I A)
    (h_pareto : WeakPareto swf)
    (h_iia : IIA swf) :
    ¬NonDictatorial swf

/-! ## Examples -/

/-- Dictatorship SWF: Individual d's preference becomes social preference -/
def dictatorship {I A : Type} (d : I) : SocialWelfareFunction I A := {
  aggregate := fun prefs => prefs d
}

/-- Theorem: A dictatorship satisfies Pareto and IIA -/
theorem dictatorship_satisfies_pareto {I A : Type} (d : I) :
    WeakPareto (dictatorship (I := I) (A := A) d) := by
  intro prefs x y h_all
  exact h_all d

theorem dictatorship_satisfies_iia {I A : Type} (d : I) :
    IIA (dictatorship (I := I) (A := A) d) := by
  intro prefs prefs' x y h1 h2
  exact h1 d

/-! ## Sen's Impossibility -/

/-- Minimal Liberalism: Some individual is decisive over some pair -/
def MinimalLiberalism {I A : Type} (swf : SocialWelfareFunction I A) : Prop :=
  ∃ i : I, ∃ x y : A,
    ∀ prefs : I → Preference A,
      StrictPref (prefs i) x y → StrictPref (swf.aggregate prefs) x y

/--
Sen's Impossibility Theorem (Statement):
No SWF can satisfy both Weak Pareto and Minimal Liberalism
under certain preference configurations.
-/
-- This is a weaker statement than the full theorem
-- The full theorem requires constructing specific preference profiles

/-! ## Utility Representations -/

/-- A utility function represents a preference if u(x) ≥ u(y) iff R x y -/
def represents {A : Type} (u : A → Int) (p : Preference A) : Prop :=
  ∀ x y, p.R x y ↔ u x >= u y

/-- Create a preference from a utility function -/
def prefFromUtility {A : Type} (u : A → Int)
    (h_finite : ∀ x y, u x >= u y ∨ u y >= u x := by decide) : Preference A := {
  R := fun x y => u x >= u y
  complete := h_finite
  trans := fun x y z hxy hyz => by omega
}
