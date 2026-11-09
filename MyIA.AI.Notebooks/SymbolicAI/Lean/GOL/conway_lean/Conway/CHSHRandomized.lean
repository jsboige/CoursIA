/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Inégalité CHSH : frontière classique pour les stratégies randomisées

La tranche déterministe (`CHSH.lean`) a montré que toute stratégie locale
déterministe a un score CHSH de valeur absolue exactement 2. Ce module traite
l'étape suivante : la randomité partagée ne permet pas à un modèle local
classique de dépasser cette frontière. Comme chaque profil déterministe a un
score de valeur absolue 2, toute combinaison convexe (famille finie de poids
rationnels non négatifs de somme 1) garde un score espéré de valeur absolue au
plus 2.

Cette seconde tranche du pilote quantique de l'Epic #13106 reste volontairement
bornée. Elle ne formalise ni états quantiques, ni observables hermitiennes, ni
la borne quantique 2√2 (Tsirelson), qui doit instancier le théorème Mathlib
existant plutôt que le dupliquer.

Sources :
- J. F. Clauser, M. A. Horne, A. Shimony, R. A. Holt,
  « Proposed Experiment to Test Local Hidden-Variable Theories »,
  Physical Review Letters 23 (1969), 880-884.
- B. S. Tsirelson, « Quantum generalizations of Bell's inequality »,
  Letters in Mathematical Physics 4 (1980), 93-100.
-/

import Conway.CHSH
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Conway
namespace CHSHRandomized

/-- Un profil local déterministe : un quadruplet de résultats binaires, un par
réglage d'Alice (`a₀`, `a₁`) et de Bob (`b₀`, `b₁`). Le type est fini de
cardinal 16 (2^4). -/
abbrev Profile := CHSH.Outcome × CHSH.Outcome × CHSH.Outcome × CHSH.Outcome

/-- Instance de finitude sur `CHSH.Outcome`, nécessaire pour sommer sur les 16
profils. `Outcome` a exactement deux éléments (`negative` et `positive`). -/
instance : Fintype CHSH.Outcome where
  elems := {CHSH.Outcome.negative, CHSH.Outcome.positive}
  complete := by
    intro x; cases x <;> simp

/-- Score CHSH d'un profil déterministe, en réutilisant `CHSH.score`. -/
def Profile.score (p : Profile) : ℤ :=
  CHSH.score p.1 p.2.1 p.2.2.1 p.2.2.2

/-- Valeur absolue du score d'un profil : toujours 2 (frontière classique
déterministe, cf. `CHSH.classical_abs_score`). -/
theorem Profile.abs_score (p : Profile) : |Profile.score p| = 2 := by
  dsimp [Profile.score]
  exact CHSH.classical_abs_score p.1 p.2.1 p.2.2.1 p.2.2.2

/-- Une stratégie localement déterministe randomisée est une famille finie de
poids rationnels sur les 16 profils. -/
abbrev Strategy := Profile → ℚ

/-- Score CHSH espéré d'une stratégie randomisée : contribution convexe des
scores déterministes. -/
def expectedScore (μ : Strategy) : ℚ :=
  ∑ p : Profile, μ p * (Profile.score p : ℚ)

/-- Valeur absolue (dans ℚ) du score d'un profil : toujours 2. Cette variante
en `ℚ` est la forme qu'utilise l'espérance. -/
theorem Profile.abs_score_rat (p : Profile) : |(Profile.score p : ℚ)| = 2 := by
  rw [← Int.cast_abs]
  exact_mod_cast Profile.abs_score p

/-- **Frontière classique pour les stratégies randomisées.** Toute combinaison
convexe de profils déterministes garde un score CHSH espéré de valeur absolue
au plus 2. La preuve combine l'inégalité triangulaire pour la valeur absolue
d'une somme et la borne déterministe `CHSH.classical_abs_score` sur chaque
profil. -/
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

/-- Le profil déterministe entièrement `positive`. -/
def pPos : Profile := (.positive, .positive, .positive, .positive)

/-- Le profil miroir où Alice répond `negative` sur ses deux réglages et Bob
`positive`. C'est le profil antisymétrique de `pPos`. -/
def pNeg : Profile := (.negative, .negative, .positive, .positive)

/-- Score du profil tout-`positive` : 2 (borne déterministe atteinte). -/
theorem Profile.score_pPos : Profile.score pPos = 2 := by
  decide

/-- Score du profil miroir : -2. -/
theorem Profile.score_pNeg : Profile.score pNeg = -2 := by
  decide

/-- La stratégie déterministe (Dirac) concentrée sur un seul profil. -/
def dirac (p : Profile) : Strategy := fun q => if q = p then (1 : ℚ) else 0

/-- La stratégie équilibrée sur les deux profils antagonistes `pPos` et `pNeg`,
chacun de poids 1/2. -/
def balancedMix : Strategy := fun q => if q = pPos ∨ q = pNeg then (1 / 2 : ℚ) else 0

/-- Score espéré d'un Dirac : seule la contribution du profil support subsiste. -/
theorem expectedScore_dirac (p : Profile) : expectedScore (dirac p) = (Profile.score p : ℚ) := by
  unfold expectedScore dirac
  simp

/-- Un mélange de Dirac en `pPos` atteint la borne supérieure : score espéré 2,
si bien que l'inégalité `|expectedScore _| ≤ 2` est atteinte. -/
example : expectedScore (dirac pPos) = 2 := by
  rw [expectedScore_dirac]
  exact_mod_cast Profile.score_pPos

/-- Linéarité additive du score espéré : l'espérance d'une somme de stratégies
est la somme des espérances. -/
lemma expectedScore_add (μ ν : Strategy) :
    expectedScore (fun q => μ q + ν q) = expectedScore μ + expectedScore ν := by
  unfold expectedScore
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]

/-- Linéarité scalaire du score espéré : un poids constant se factorise. -/
lemma expectedScore_mul (k : ℚ) (μ : Strategy) :
    expectedScore (fun q => k * μ q) = k * expectedScore μ := by
  unfold expectedScore
  simp_rw [mul_assoc]
  rw [Finset.mul_sum]

/-- Décomposition du mélange équilibré en demi-somme de deux Diracs (poids 1/2
chacun sur `pPos` et `pNeg`). -/
theorem pPos_ne_pNeg : pPos ≠ pNeg := by
  decide

theorem balancedMix_eq : balancedMix = fun q => (1 / 2 : ℚ) * (dirac pPos q + dirac pNeg q) := by
  funext q
  by_cases hp : q = pPos <;> by_cases hn : q = pNeg <;>
    simp [balancedMix, dirac, hp, hn, pPos_ne_pNeg, pPos_ne_pNeg.symm]

/-- Un mélange équilibré de deux profils antagonistes (score 2 et -2) donne un
score espéré nul : `expectedScore balancedMix = 0`. Les contributions de `pPos`
(+2) et de `pNeg` (-2) s'annulent. -/
theorem balancedMix_eq_zero : expectedScore balancedMix = 0 := by
  rw [balancedMix_eq]
  rw [expectedScore_mul]
  rw [expectedScore_add]
  rw [expectedScore_dirac, expectedScore_dirac]
  rw [Profile.score_pPos, Profile.score_pNeg]
  norm_num

end CHSHRandomized
end Conway
