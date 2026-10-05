/-
  StableMarriage.GaleShapley -- stub tranche 0 (issue #19276)
  L'algorithme de Gale-Shapley (1962) execute sur le type `Matching` cible.
  L'etat intermediaire (proposition courante, appariement temporaire) sera
  modelise par un `GSState` distinct (option B du PORT_ANALYSIS) car le
  type `Matching` total ne peut pas representer "non apparie" pendant
  l'execution.
-/
namespace StableMarriage

/-- Stub : etat intermediaire de l'algorithme GS (cible phase 1). -/
def StubGSState : Type := Unit

end StableMarriage
