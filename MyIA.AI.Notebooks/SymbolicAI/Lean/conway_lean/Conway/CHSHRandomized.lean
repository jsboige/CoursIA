/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Inégalité CHSH : stratégies locales classiques randomisées

Ce module étend la frontière classique déterministe de `Conway.CHSH` aux
stratégies randomisées classiques, c'est-à-dire aux mélanges finis
rationnels de profils locaux déterministes. Pour de tels mélanges, le score
CHSH espéré reste borné en valeur absolue par `2` : la borne classique
déterministe est préservée par combinaison convexe.

Cette tranche est la deuxième étape formelle du pilote quantique de
l'EPIC #13106, après la borne déterministe de `Conway.CHSH` (PR #14132).
Elle ne prétend pas formaliser la borne quantique de Tsirelson `2√2`,
qui demande des observables hermitiennes et une norme d'opérateur —
elle explicite seulement la deuxième étape classique du programme
analytique de Bell : la randomité partagée ne permet pas à un modèle
local classique de dépasser la borne déterministe.

Sources :
- J. F. Clauser, M. A. Horne, R. Shimony, R. A. Holt, « Proposed
  Experiment to Test Local Hidden-Variable Theories », Physical
  Review Letters 23 (1969), 880-884.
- J. S. Bell, « On the Einstein-Podolsky-Rosen Paradox », Physics
  Physique Fizika 1 (1964), 195-200.
- B. S. Tsirelson, « Quantum generalizations of Bell's inequality »,
  Letters in Mathematical Physics 4 (1980), 93-100.
-/

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.Finset

import Conway.CHSH

namespace Conway
namespace CHSHRandomized

open CHSH
open Finset

/-- Profil local déterministe : les quatre réponses binaires
prédéterminées d'Alice (`a₀`, `a₁`) et de Bob (`b₀`, `b₁`). La localité
est encodée par le fait que chaque réponse ne dépend que du réglage de
sa propre partie. -/
abbrev Profile := Outcome × Outcome × Outcome × Outcome

/-- Les 16 profils locaux déterministes d'un scénario binaire 2 × 2. -/
def allProfiles : Finset Profile :=
  univ ×ˢ univ ×ˢ univ ×ˢ univ

/-- Cardinal attendu : `|allProfiles| = 16`. La preuve est par énumération
des quatre composantes (`Outcome` a deux constructeurs, donc
`2^4 = 16`). -/
theorem card_allProfiles : #allProfiles = 16 := by
  simp [allProfiles, Outcome]

/-- Distribution discrète finie sur les profils : une famille de poids
rationnels non négatifs de somme `1`. Cette structure formalise une
stratégie randomisée classique locale. -/
structure Distribution where
  weight : Profile → ℚ
  nonneg : ∀ p, 0 ≤ weight p
  sums_to_one : ∑ p ∈ allProfiles, weight p = 1

/-- Score CHSH d'un profil, par réutilisation directe de `CHSH.score`. -/
def profileScore (p : Profile) : ℤ :=
  let (a₀, a₁, b₀, b₁) := p
  score a₀ a₁ b₀ b₁

/-- Score CHSH espéré sous la distribution `μ` : combinaison convexe des
scores déterministes, pondérée par les poids rationnels. -/
def expectedScore (μ : Distribution) : ℚ :=
  ∑ p ∈ allProfiles, μ.weight p * (profileScore p : ℚ)

/-- **Borne classique randomisée.** Le score CHSH espéré de toute
stratégie locale randomisée classique reste borné en valeur absolue par
la frontière classique `2`.

La preuve combine trois faits :
1. chaque score déterministe a pour valeur absolue exactement `2`
   (`CHSH.classical_abs_score`) ;
2. la somme pondérée préserve la borne en valeur absolue par
   inégalité triangulaire (`Finset.abs_sum_le_sum_abs`) ;
3. la somme des poids vaut `1`, donc la somme pondérée des valeurs
absolues vaut `2`. -/
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
    -- ∑ p, μ.weight p = 1, donc la somme vaut 1 * 2 = 2.
    rw [← Finset.sum_mul]
    rw [μ.sums_to_one]
    norm_num
  exact h_triangle.trans_eq h_const

/-- Le Dirac en un profil `p₀` est une distribution valide. -/
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

/-- Score espéré du Dirac en `p₀` : il vaut exactement `profileScore p₀`. -/
theorem expectedScore_dirac (p₀ : Profile) :
    expectedScore (dirac p₀) = (profileScore p₀ : ℚ) := by
  unfold expectedScore dirac
  rw [Finset.sum_ite_eq allProfiles
      (fun p => (1 : ℚ) * (profileScore p : ℚ))
      (fun p => (0 : ℚ) * (profileScore p : ℚ))]
  simp

/-- Cas extrême : le Dirac en un profil qui atteint la borne supérieure
classique donne un score espéré `+2`. -/
theorem expectedScore_dirac_upper :
    expectedScore (dirac (.positive, .positive, .positive, .positive)) = 2 := by
  rw [expectedScore_dirac, profileScore]
  norm_num [score, Outcome.value]

/-- **Score du profil opposé.** Inverser la réponse de Bob change le signe
du score CHSH. -/
def flipBob (a₀ a₁ b₀ b₁ : Outcome) : Profile :=
  (a₀, a₁, b₁, b₀)

theorem score_flipBob_neg (a₀ a₁ b₀ b₁ : Outcome) :
    score a₀ a₁ (flipBob a₀ a₁ b₀ b₁).2.2.1 (flipBob a₀ a₁ b₀ b₁).2.2.2
      = -score a₀ a₁ b₀ b₁ := by
  unfold flipBob score
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;> decide

/-- Cas de symétrie : le mélange équilibré entre un profil et son profil
« inversé-Bob » donne un score espéré nul. -/
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

/-- Score espéré du mélange équilibré entre `p₀` et son profil
« inversé-Bob » : il vaut `0`. -/
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

end CHSHRandomized
end Conway
