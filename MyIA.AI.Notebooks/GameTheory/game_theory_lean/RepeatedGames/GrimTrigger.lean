import Mathlib.Tactic
import RepeatedGames.Stage
import RepeatedGames.Discounting

/-!
# Grim Trigger — transition et condition d'incitation

Ce module formalise deux briques du *grim trigger* dans le Dilemme du
Prisonnier infiniment répété :

1. la transition irréversible vers la punition après la première défection ;
2. l'équivalence algébrique entre l'absence de gain pour une déviation en un
   coup et le seuil `δ ≥ (T − R) / (T − P)`.

La seconde brique est la condition d'incitation utilisée dans la preuve
classique par déviation en un coup. Elle ne constitue pas à elle seule une
formalisation d'équilibre de Nash parfait en sous-jeux : une telle preuve
demanderait une sémantique des historiques et des profils de stratégies.

**Companion notebook** : `GameTheory-6c` (jeux répétés) dérive ce seuil à la
main. Pont `ICT-13` (#4879) : la vérification numérique du seuil δ y est un
gate.
-/

namespace RepeatedGames

open PDAction

/-! ## Stratégie grim trigger -/

/-- Transition du grim trigger. `prevSelf` encode l'état courant :
`defect` signifie que la phase de punition a déjà commencé. Cet état est
absorbant ; sinon, une première défection adverse déclenche la punition. -/
def grimNext (prevSelf prevFoe : PDAction) : PDAction :=
  match prevSelf, prevFoe with
  | defect, _ => defect
  | cooperate, cooperate => cooperate
  | cooperate, defect => defect

@[simp]
theorem grimNext_cooperate_cooperate :
    grimNext cooperate cooperate = cooperate := rfl

@[simp]
theorem grimNext_cooperate_defect :
    grimNext cooperate defect = defect := rfl

@[simp]
theorem grimNext_defect_cooperate :
    grimNext defect cooperate = defect := rfl

@[simp]
theorem grimNext_defect_defect :
    grimNext defect defect = defect := rfl

/-- Une fois la punition déclenchée, elle reste active quel que soit le
prochain coup adverse. -/
theorem grimPunishment_absorbing (prevFoe : PDAction) :
    grimNext defect prevFoe = defect := by
  cases prevFoe <;> rfl

/-! ## Condition d'incitation en une déviation -/

/-- **La coopération domine une déviation en un coup ssi
`δ ≥ (T − R) / (T − P)`.**

Cette équivalence compare les deux flux actualisés associés au chemin
coopératif et à une déviation suivie de la punition grim. Elle établit la
condition d'incitation algébrique utilisée par le principe de déviation en un
coup ; elle ne quantifie pas encore sur les historiques ou les profils de
stratégies nécessaires à un énoncé formel de SPNE.

Par `coop_ge_deviate_iff`, le résultat se réduit au seuil explicite sur `δ`. -/
theorem grim_trigger_sustains_iff (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1) :
    (coopValue g.R δ ≥ deviateValue g.T g.P δ) ↔
      δ ≥ (g.T - g.R) / (g.T - g.P) := by
  exact coop_ge_deviate_iff g h0 h1

end RepeatedGames
