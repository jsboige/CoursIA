/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Inégalité CHSH : frontière classique déterministe

Clauser, Horne, Shimony et Holt (1969) ont proposé une inégalité de Bell
expérimentale à deux observables binaires par partie. Ce module formalise son
noyau classique : dans toute stratégie locale déterministe, chaque réponse
prédéterminée vaut -1 ou +1 et le score CHSH a une valeur absolue exactement
égale à 2. Toute corrélation dépassant 2 sort donc de ce modèle classique.

Cette première tranche du pilote quantique de l'Epic #13106 est volontairement
bornée. Elle ne prétend pas encore formaliser la borne quantique de Tsirelson
2√2, qui demande des observables hermitiennes et une norme d'opérateur. Elle
conserve ainsi une frontière vérifiable entre le certificat livré et la suite
analytique encore ouverte.

Sources :
- J. F. Clauser, M. A. Horne, A. Shimony, R. A. Holt,
  « Proposed Experiment to Test Local Hidden-Variable Theories »,
  Physical Review Letters 23 (1969), 880-884.
- B. S. Tsirelson, « Quantum generalizations of Bell's inequality »,
  Letters in Mathematical Physics 4 (1980), 93-100.
-/

import Mathlib.Tactic.Ring

namespace Conway
namespace CHSH

/-- Résultat binaire prédéterminé d'une mesure classique. -/
inductive Outcome
  | negative
  | positive
  deriving DecidableEq

/-- Encodage numérique standard des deux résultats par `-1` et `+1`. -/
def Outcome.value : Outcome → ℤ
  | .negative => -1
  | .positive => 1

/-- Chaque résultat classique est un signe : son carré vaut un. -/
theorem Outcome.value_sq (outcome : Outcome) : outcome.value ^ 2 = 1 := by
  cases outcome <;> decide

/-- Score CHSH d'une stratégie locale déterministe.

`a₀`, `a₁` sont les réponses prédéterminées d'Alice et `b₀`, `b₁` celles de
Bob. La localité est encodée par le fait que chaque réponse ne dépend que du
réglage de sa propre partie. -/
def score (a₀ a₁ b₀ b₁ : Outcome) : ℤ :=
  a₀.value * b₀.value + a₀.value * b₁.value +
    a₁.value * b₀.value - a₁.value * b₁.value

/-- Factorisation qui expose les deux branches classiques : selon que les
réponses de Bob coïncident ou s'opposent, un seul des deux termes contribue. -/
theorem score_factorization (a₀ a₁ b₀ b₁ : Outcome) :
    score a₀ a₁ b₀ b₁ =
      a₀.value * (b₀.value + b₁.value) +
        a₁.value * (b₀.value - b₁.value) := by
  simp only [score]
  ring

/-- **Frontière classique CHSH.** Toute stratégie locale déterministe atteint
exactement la frontière classique : la valeur absolue du score est `2`.

La preuve énumère les 16 assignations de quatre résultats binaires. `decide`
est ici un calcul noyau sur un type fini, sans axiome ni code natif. -/
theorem classical_abs_score (a₀ a₁ b₀ b₁ : Outcome) :
    |score a₀ a₁ b₀ b₁| = 2 := by
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;> decide

/-- Forme usuelle de l'inégalité CHSH pour les stratégies déterministes. -/
theorem classical_bound (a₀ a₁ b₀ b₁ : Outcome) :
    |score a₀ a₁ b₀ b₁| ≤ 2 := by
  rw [classical_abs_score]

/-- Une stratégie classique qui atteint la borne supérieure `+2`. -/
example : score .positive .positive .positive .positive = 2 := by
  decide

/-- Une stratégie classique qui atteint la borne inférieure `-2`. -/
example : score .negative .negative .positive .positive = -2 := by
  decide

end CHSH
end Conway
