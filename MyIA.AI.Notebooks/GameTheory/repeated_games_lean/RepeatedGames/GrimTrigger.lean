import Mathlib.Tactic
import RepeatedGames.Stage
import RepeatedGames.Discounting

/-!
# Grim Trigger — théorème-phare

Résultat central de la théorie des jeux répétés : la stratégie *grim trigger*
(coopérer tant que l'adversaire coopère, dévier pour toujours dès la première
défection) soutient la coopération comme équilibre de Nash parfait en
sous-jeux du Dilemme du Prisonnier infiniment répété **si et seulement si**
le facteur d'escompte `δ` dépasse le seuil critique `(T − R) / (T − P)`.

La preuve repose sur le **principe de déviation en un coup** (one-shot
deviation principle) : pour une stratégie stationaire comme grim trigger,
vérifier toutes les déviations possibles équivaut à vérifier les déviations
d'un seul coup.

**Companion notebook** : `GameTheory-6c` (jeux répétés) dérive ce seuil à la
main. Le présent module en donne la preuve formelle. Pont `ICT-13` (#4879) :
la vérification numérique du seuil δ y est un gate.
-/

namespace RepeatedGames

open PDAction

/-! ## Stratégie grim trigger -/

/-- Une stratégie grim trigger : coopérer à la première période, puis
recopier le coup adverse de la période précédente (coopérer s'il a coopéré,
dévier pour toujours dès qu'il dévie une fois). -/
def grimNext (prevSelf prevFoe : PDAction) : PDAction :=
  match prevFoe with
  | cooperate => cooperate
  | defect    => defect

/-! ## Théorème-phare (scaffold — preuve en tranche 2) -/

/-- **Grim trigger soutient la coopération ssi `δ ≥ (T − R) / (T − P)`.**

Une déviation unilatérale en un coup n'est pas profitable (i.e. grim trigger
est stable) exactement lorsque le facteur d'escompte est assez grand pour que
la perte de coopération future (`R → P` à toutes les périodes post-déviation)
compense le gain immédiat (`R → T` à la période de déviation).

Par `coop_ge_deviate_iff`, ce résultat se réduit à un seuil explicite sur `δ`.

TODO tranche 2 : assembler la preuve via le one-shot deviation principle
(`coop_ge_deviate_iff` + `geom_sum` + `defect_strictly_dominates`). -/
theorem grim_trigger_sustains_iff (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1) :
    (coopValue g.R δ ≥ deviateValue g.T g.P δ) ↔
      δ ≥ (g.T - g.R) / (g.T - g.P) := by
  -- Par réduction au seuil (algèbre réelle pure).
  exact coop_ge_deviate_iff g h0 h1

end RepeatedGames
