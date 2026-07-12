/-
  Théorie du choix social en Lean 4
  =================================

  Formalise les notions clés de la théorie du choix social :
  - Préférences et ordres
  - Fonctions de bien-être social
  - Axiomes d'Arrow (Pareto, IIA, Non-dictature)
  - Théorème d'impossibilité d'Arrow (énoncé)

  Basé sur GameTheory-19-Lean-SocialChoice.ipynb
  Inspiré de asouther4/lean-social-choice (Lean 3)

  ---
  English:
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

/-!
## Préférences

---
English:
## Preferences
-/

/-- Une relation de préférence est une relation binaire sur les alternatives.
    English: A preference relation is a binary relation on alternatives -/
structure Preference (A : Type) where
  /-- `R x y` signifie « x est au moins aussi bon que y ».
      English: R x y means "x is at least as good as y" -/
  R : A → A → Prop
  /-- Complétude : pour tout x, y, soit R x y soit R y x.
      English: Completeness: for any x, y, either R x y or R y x -/
  complete : ∀ x y, R x y ∨ R y x
  /-- Transitivité.
      English: Transitivity -/
  trans : ∀ x y z, R x y → R y z → R x z

/-- Préférence stricte : x est strictement préféré à y.
    English: Strict preference: x is strictly preferred to y -/
def StrictPref {A : Type} (p : Preference A) (x y : A) : Prop :=
  p.R x y ∧ ¬p.R y x

/-- Indifférence : x et y sont également bons.
    English: Indifference: x and y are equally good -/
def Indifferent {A : Type} (p : Preference A) (x y : A) : Prop :=
  p.R x y ∧ p.R y x

/-!
## Fonctions de bien-être social

---
English:
## Social Welfare Functions
-/

/-- Une fonction de bien-être social agrège les préférences individuelles en une préférence sociale.
    English: A social welfare function aggregates individual preferences into a social preference -/
structure SocialWelfareFunction (I A : Type) where
  /-- La fonction d'agrégation.
      English: The aggregation function -/
  aggregate : (I → Preference A) → Preference A

/-!
## Axiomes d'Arrow

---
English:
## Arrow's Axioms
-/

/-- Pareto faible : si tout le monde préfère strictement x à y, la société préfère x à y.
    English: Weak Pareto: If everyone strictly prefers x to y, society prefers x to y -/
def WeakPareto {I A : Type} (swf : SocialWelfareFunction I A) : Prop :=
  ∀ prefs : I → Preference A, ∀ x y,
    (∀ i, StrictPref (prefs i) x y) → StrictPref (swf.aggregate prefs) x y

/-- Indépendance des alternatives non pertinentes (IIA).
    English: Independence of Irrelevant Alternatives (IIA) -/
def IIA {I A : Type} (swf : SocialWelfareFunction I A) : Prop :=
  ∀ prefs prefs' : I → Preference A, ∀ x y,
    -- Si les préférences x vs y sont identiques dans les deux profils
    (∀ i, (prefs i).R x y ↔ (prefs' i).R x y) →
    (∀ i, (prefs i).R y x ↔ (prefs' i).R y x) →
    -- Alors la préférence sociale sur x, y est identique
    ((swf.aggregate prefs).R x y ↔ (swf.aggregate prefs').R x y)

/-- Non-dictature : aucun individu unique ne détermine la préférence sociale.
    English: Non-dictatorship: No single individual determines the social preference -/
def NonDictatorial {I A : Type} (swf : SocialWelfareFunction I A) : Prop :=
  ¬∃ d : I, ∀ prefs : I → Preference A, ∀ x y,
    StrictPref (prefs d) x y → StrictPref (swf.aggregate prefs) x y

/-!
## Théorème d'impossibilité d'Arrow

---
English:
## Arrow's Impossibility Theorem
-/

/--
Théorème d'impossibilité d'Arrow (énoncé) :
il n'existe pas de fonction de bien-être social avec ≥ 3 alternatives qui satisfasse :
1. Pareto faible
2. Indépendance des alternatives non pertinentes
3. Non-dictature

Note : énoncé avec des types `Fin n` explicites plutôt qu'un `Fintype` générique
pour éviter la dépendance Mathlib. Le contenu mathématique du théorème est identique.

---
English:
Arrow's Impossibility Theorem (Statement):
There is no social welfare function with ≥3 alternatives that satisfies:
1. Weak Pareto
2. Independence of Irrelevant Alternatives
3. Non-dictatorship

Note: Stated with explicit `Fin n` types instead of generic `Fintype`
to avoid Mathlib dependency. The theorem's mathematical content is identical.
-/
-- La preuve complète nécessite une machinerie importante ; nous l'énonçons comme axiome
axiom arrow_impossibility {nI nA : Nat}
    (hI : nI ≥ 2)
    (hA : nA ≥ 3)
    (swf : SocialWelfareFunction (Fin nI) (Fin nA))
    (h_pareto : WeakPareto swf)
    (h_iia : IIA swf) :
    ¬NonDictatorial swf

/-!
## Exemples

---
English:
## Examples
-/

/-- SWF dictatorial : la préférence de l'individu d devient la préférence sociale.
    English: Dictatorship SWF: Individual d's preference becomes social preference -/
def dictatorship {I A : Type} (d : I) : SocialWelfareFunction I A := {
  aggregate := fun prefs => prefs d
}

/-- Théorème : une dictature satisfait Pareto et IIA.
    English: Theorem: A dictatorship satisfies Pareto and IIA -/
theorem dictatorship_satisfies_pareto {I A : Type} (d : I) :
    WeakPareto (dictatorship (I := I) (A := A) d) := by
  intro prefs x y h_all
  exact h_all d

theorem dictatorship_satisfies_iia {I A : Type} (d : I) :
    IIA (dictatorship (I := I) (A := A) d) := by
  intro prefs prefs' x y h1 h2
  exact h1 d

/-!
## Impossibilité de Sen

---
English:
## Sen's Impossibility
-/

/-- Libéralisme minimal : un individu est décisif sur au moins une paire.
    English: Minimal Liberalism: Some individual is decisive over some pair -/
def MinimalLiberalism {I A : Type} (swf : SocialWelfareFunction I A) : Prop :=
  ∃ i : I, ∃ x y : A,
    ∀ prefs : I → Preference A,
      StrictPref (prefs i) x y → StrictPref (swf.aggregate prefs) x y

/- Théorème d'impossibilité de Sen (énoncé) :
   aucune SWF ne peut satisfaire à la fois Pareto faible et Libéralisme minimal
   sous certaines configurations de préférences.
   (Énoncé plus faible — le théorème complet nécessite de construire
   des profils de préférences spécifiques.)
   English: Sen's Impossibility Theorem (Statement):
   No SWF can satisfy both Weak Pareto and Minimal Liberalism
   under certain preference configurations.
   (Weaker statement — the full theorem requires constructing
   specific preference profiles.) -/

/-!
## Représentations par utilité

---
English:
## Utility Representations
-/

/-- Une fonction d'utilité représente une préférence si `u(x) ≥ u(y)` ssi `R x y`.
    English: A utility function represents a preference if u(x) ≥ u(y) iff R x y -/
def represents {A : Type} (u : A → Int) (p : Preference A) : Prop :=
  ∀ x y, p.R x y ↔ u x >= u y

/-- Construit une préférence à partir d'une fonction d'utilité.
    English: Create a preference from a utility function -/
def prefFromUtility {A : Type} (u : A → Int)
    (h_finite : ∀ x y, u x >= u y ∨ u y >= u x := by decide) : Preference A := {
  R := fun x y => u x >= u y
  complete := h_finite
  trans := fun x y z hxy hyz => by omega
}
