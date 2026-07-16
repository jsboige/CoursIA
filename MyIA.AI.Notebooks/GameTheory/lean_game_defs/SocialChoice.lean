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
  Jumelage i18n : ce module est le FR canonique (sibling pair Pattern A,
  ratifié par user 2026-07-04 sur EPIC #4980). Le miroir anglais vit dans
  `SocialChoice_en.lean` (variante reuse-FR-names : contrairement à `Nash.lean`
  qui dépend du module de base partagé `Basic`, `SocialChoice.lean` est
  autonome — aucun import, Lean core uniquement — donc le miroir EN l'est
  aussi et re-déclare ses types dans `namespace SocialChoiceEn`). Le corps des
  définitions, signatures, tactiques et de l'axiome `arrow_impossibility` est
  byte-identique entre les deux fichiers ; seules les docstrings `/-! ... -/`
  (titres de section) et `/-- ... -/` (docstrings de déclarations) diffèrent,
  FR dans ce fichier, EN dans `SocialChoice_en.lean`.
-/

/-!
## Préférences
-/

/-- Une relation de préférence est une relation binaire sur les alternatives. -/
structure Preference (A : Type) where
  /-- `R x y` signifie « x est au moins aussi bon que y ». -/
  R : A → A → Prop
  /-- Complétude : pour tout x, y, soit R x y soit R y x. -/
  complete : ∀ x y, R x y ∨ R y x
  /-- Transitivité. -/
  trans : ∀ x y z, R x y → R y z → R x z

/-- Préférence stricte : x est strictement préféré à y. -/
def StrictPref {A : Type} (p : Preference A) (x y : A) : Prop :=
  p.R x y ∧ ¬p.R y x

/-- Indifférence : x et y sont également bons. -/
def Indifferent {A : Type} (p : Preference A) (x y : A) : Prop :=
  p.R x y ∧ p.R y x

/-!
## Fonctions de bien-être social
-/

/-- Une fonction de bien-être social agrège les préférences individuelles en une préférence sociale. -/
structure SocialWelfareFunction (I A : Type) where
  /-- La fonction d'agrégation. -/
  aggregate : (I → Preference A) → Preference A

/-!
## Axiomes d'Arrow
-/

/-- Pareto faible : si tout le monde préfère strictement x à y, la société préfère x à y. -/
def WeakPareto {I A : Type} (swf : SocialWelfareFunction I A) : Prop :=
  ∀ prefs : I → Preference A, ∀ x y,
    (∀ i, StrictPref (prefs i) x y) → StrictPref (swf.aggregate prefs) x y

/-- Indépendance des alternatives non pertinentes (IIA). -/
def IIA {I A : Type} (swf : SocialWelfareFunction I A) : Prop :=
  ∀ prefs prefs' : I → Preference A, ∀ x y,
    -- Si les préférences x vs y sont identiques dans les deux profils
    (∀ i, (prefs i).R x y ↔ (prefs' i).R x y) →
    (∀ i, (prefs i).R y x ↔ (prefs' i).R y x) →
    -- Alors la préférence sociale sur x, y est identique
    ((swf.aggregate prefs).R x y ↔ (swf.aggregate prefs').R x y)

/-- Non-dictature : aucun individu unique ne détermine la préférence sociale. -/
def NonDictatorial {I A : Type} (swf : SocialWelfareFunction I A) : Prop :=
  ¬∃ d : I, ∀ prefs : I → Preference A, ∀ x y,
    StrictPref (prefs d) x y → StrictPref (swf.aggregate prefs) x y

/-!
## Théorème d'impossibilité d'Arrow
-/

/--
Théorème d'impossibilité d'Arrow (énoncé) :
il n'existe pas de fonction de bien-être social avec ≥ 3 alternatives qui satisfasse :
1. Pareto faible
2. Indépendance des alternatives non pertinentes
3. Non-dictature

Note : énoncé avec des types `Fin n` explicites plutôt qu'un `Fintype` générique
pour éviter la dépendance Mathlib. Le contenu mathématique du théorème est identique.
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
-/

/-- SWF dictatorial : la préférence de l'individu d devient la préférence sociale. -/
def dictatorship {I A : Type} (d : I) : SocialWelfareFunction I A := {
  aggregate := fun prefs => prefs d
}

/-- Théorème : une dictature satisfait Pareto et IIA. -/
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
-/

/-- Libéralisme minimal : un individu est décisif sur au moins une paire. -/
def MinimalLiberalism {I A : Type} (swf : SocialWelfareFunction I A) : Prop :=
  ∃ i : I, ∃ x y : A,
    ∀ prefs : I → Preference A,
      StrictPref (prefs i) x y → StrictPref (swf.aggregate prefs) x y

/- Théorème d'impossibilité de Sen (énoncé) :
   aucune SWF ne peut satisfaire à la fois Pareto faible et Libéralisme minimal
   sous certaines configurations de préférences.
   (Énoncé plus faible — le théorème complet nécessite de construire
   des profils de préférences spécifiques.) -/

/-!
## Représentations par utilité
-/

/-- Une fonction d'utilité représente une préférence si `u(x) ≥ u(y)` ssi `R x y`. -/
def represents {A : Type} (u : A → Int) (p : Preference A) : Prop :=
  ∀ x y, p.R x y ↔ u x >= u y

/-- Construit une préférence à partir d'une fonction d'utilité. -/
def prefFromUtility {A : Type} (u : A → Int)
    (h_finite : ∀ x y, u x >= u y ∨ u y >= u x := by decide) : Preference A := {
  R := fun x y => u x >= u y
  complete := h_finite
  trans := fun x y z hxy hyz => by omega
}
