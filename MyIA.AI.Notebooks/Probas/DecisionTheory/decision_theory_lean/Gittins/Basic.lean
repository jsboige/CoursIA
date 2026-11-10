import Mathlib.Data.Real.Basic

/-!
# Définitions de base — Bandits Manchots (Multi-Armed Bandits)

Types fondamentaux du problème du bandit : bras, instances, politiques et fonctions
de valeur. Les moyennes et facteurs d'actualisation sont portés par `ℝ` (et non
`Float`) afin que les lois d'ordre soient réflexives — une moyenne de bandit est un
nombre réel, jamais un `NaN`. Les historiques de récompenses échantillonnées
restent en `Float` (quantités empiriques) ; les deux notions sont délibérément
distinctes.
-/

namespace Gittins

/-- Un bras de bandit, caractérisé par sa récompense moyenne réelle. -/
structure BanditArm where
  name : String
  trueMean : ℝ

/-- Une instance de bandit : une collection de bras avec un facteur d'actualisation. -/
structure BanditInstance where
  arms : Array BanditArm
  discount : ℝ  -- gamma in (0, 1)

/-- Une politique associe à chaque pas de temps l'indice du bras à tirer. -/
def Policy := Nat → Nat

/-- Un historique de récompenses pour un seul bras. -/
def RewardHistory := List Float

/-- Nombre de fois qu'un bras a été tiré. -/
def pullCount (history : RewardHistory) : Nat := history.length

/-- Moyenne empirique d'un historique de récompenses. Vaut 0 pour un historique vide. -/
def empiricalMean (history : RewardHistory) : Float :=
  match history with
  | [] => 0.0
  | _ => history.foldl (· + ·) 0.0 / history.length.toFloat

end Gittins
