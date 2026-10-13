import Mathlib
import Utility.Basic

/-!
# Axiomes de von Neumann–Morgenstern

Les quatre axiomes qu'une préférence sur les loteries doit satisfaire pour
admettre une représentation en utilité espérée :

1. **Complétude** — deux loteries quelconques sont comparables.
2. **Transitivité** — les chaînes de préférence ne cyclent pas.
3. **Indépendance (substitution)** — un mélange commun préserve la préférence.
4. **Continuité (Archimédienne)** — aucune loterie n'est infiniment meilleure
   ou pire qu'une autre ; des mélanges intermédiaires existent.

Une préférence satisfaisant les quatre est `IsRational`.

Convention i18n (EPIC #4980, PR pilote #5303) : FR-first appliqué sur les
en-têtes et docstrings publics. Le code tactique et les commentaires
intra-preuve restent en anglais (références Mathlib, notation formelle).
-/

namespace Utility

variable {α : Type*} [Fintype α]

/-- Une relation de préférence est une relation binaire sur les loteries. Lire
`P p q` comme « la loterie `p` est faiblement préférée à la loterie `q` » (p ≽ q). -/
abbrev Pref (α : Type*) [Fintype α] := Lottery α → Lottery α → Prop

/-- Préférence stricte dérivée d'une préférence faible : `p ≻ q` signifie
`p ≽ q` mais non `q ≽ p`. -/
def StrictPref (P : Pref α) (p q : Lottery α) : Prop := P p q ∧ ¬ P q p

/-- Indifférence dérivée d'une préférence faible : `p ~ q` signifie `p ≽ q`
**et** `q ≽ p` (chaque loterie est faiblement préférée à l'autre). C'est la
jumelle symétrique de `StrictPref` : ensemble elles décomposent une préférence
complète en son squelette strict et sa relation d'indifférence. -/
def Indiff (P : Pref α) (p q : Lottery α) : Prop := P p q ∧ P q p

/-- **Complétude** : deux loteries quelconques sont comparables dans au moins
une direction. -/
def IsComplete (P : Pref α) : Prop :=
  ∀ p q : Lottery α, P p q ∨ P q p

/-- **Transitivité** : les chaînes de préférence se propagent. -/
def IsTransitive (P : Pref α) : Prop :=
  ∀ p q r : Lottery α, P p q → P q r → P p r

/-- **Indépendance (substitution)** : si `p ≽ q`, alors mélanger les deux avec
une même troisième loterie `r` préserve la préférence, pour tout poids de
mélange `t ∈ [0,1]`. -/
def IsIndependent (P : Pref α) : Prop :=
  ∀ (p q r : Lottery α) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1),
    P p q → P (mix t p r ht0 ht1) (mix t q r ht0 ht1)

/-- **Continuité (Archimédienne / résolvabilité des mélanges)** : si
`p ≽ q ≽ r`, alors un certain mélange convexe de `p` et `r` est indifférent à
`q`. De manière équivalente, aucune loterie n'est infiniment meilleure ou
pire qu'une autre ; `q` peut toujours être obtenu en mélangeant les extrêmes.
C'est la forme standard de résolvabilité de l'axiome archimédien, équivalente
à la forme « pas de dominance lexicographique » à deux témoins pour les ordres
transitifs complets. -/
def IsContinuous (P : Pref α) : Prop :=
  ∀ p q r : Lottery α,
    P p q → P q r →
      ∃ (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1),
        P (mix t p r ht0 ht1) q ∧ P q (mix t p r ht0 ht1)

/-- Une préférence **rationnelle** satisfait les quatre axiomes VNM. -/
structure IsRational (P : Pref α) : Prop where
  protected complete : IsComplete P
  protected transitive : IsTransitive P
  protected independent : IsIndependent P
  protected continuous : IsContinuous P

end Utility
