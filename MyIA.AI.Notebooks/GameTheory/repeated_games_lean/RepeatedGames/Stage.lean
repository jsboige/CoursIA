import Mathlib.Tactic

/-!
# Stage Game : le Dilemme du Prisonnier

On formalise le jeu de stage (stage game) sous-jacent : le Dilemme du
Prisonnier, paramétré par quatre réels `T, R, P, S` satisfaisant les
contraintes classiques `T > R > P > S` et `2 * R > T + S`.

Notation (Gibbons 1992) :
  - `T` (Temptation) : paiement d'une déviation unilatérale contre un coopérateur,
  - `R` (Reward)    : paiement de la coopération mutuelle,
  - `P` (Punishment): paiement de la défection mutuelle,
  - `S` (Sucker)    : paiement du coopérateur exploité.

La contrainte `2 * R > T + S` garantit que la coopération mutuelle
Pareto-domine l'alternance exploiter/être exploité.
-/

namespace RepeatedGames

/-- Une action du joueur : Coopérer ou Dévier (Defect). -/
inductive PDAction where
  | cooperate : PDAction
  | defect : PDAction
  deriving DecidableEq, Repr

open PDAction

/-- Paramètres du Dilemme du Prisonnier. La structure transporte les
contraintes `T > R > P > S` et `2 * R > T + S` comme champs de preuve,
de sorte qu'aucune hypothèse implicite n'est nécessaire en aval. -/
structure PrisonersDilemma where
  (T R P S : ℝ)
  (hTR : T > R)
  (hRP : R > P)
  (hPS : P > S)
  (hPD : 2 * R > T + S)

/-- Paiement de stage pour le joueur de référence (row) face au coup `b`
de l'adversaire. Matrice de paiement standard :

    b = cooperate  |  b = defect
  C :   R          |  S
  D :   T          |  P
-/
def stagePayoff (g : PrisonersDilemma) (a b : PDAction) : ℝ :=
  match a, b with
  | cooperate, cooperate => g.R
  | defect,    cooperate => g.T
  | cooperate, defect    => g.S
  | defect,    defect    => g.P

/-- Dans un PD, dévier domine strictement coopérer quel que soit le coup
adverse : `T > R` (adversaire coopère) et `P > S` (adversaire dévie).
C'est précisément ce qui rend la coopération irrationnelle dans le jeu
*une shot* — et donc non triviale à soutenir dans le jeu répété. -/
lemma defect_strictly_dominates (g : PrisonersDilemma) (b : PDAction) :
    stagePayoff g defect b > stagePayoff g cooperate b := by
  cases b
  · simp only [stagePayoff]; exact g.hTR
  · simp only [stagePayoff]; exact g.hPS

/-- La coopération mutuelle Pareto-domine la défection mutuelle (`R > P`). -/
lemma mutual_coop_better_than_mutual_defect (g : PrisonersDilemma) :
    g.R > g.P := g.hRP

/-- Le paiement de déviation `T` est strictement supérieur à `R`. -/
lemma temptation_gt_reward (g : PrisonersDilemma) : g.T > g.R := g.hTR

end RepeatedGames
