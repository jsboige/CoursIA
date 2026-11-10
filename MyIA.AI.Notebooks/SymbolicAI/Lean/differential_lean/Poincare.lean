/-
  Temoin — conjecture de Poincare (qinz1yang/differential-geometry v0.1.3)
  =========================================================================

  Compagnon de `DifferentialTour.lean`, pour le Pli 1 sub-grain 2 de
  l'EPIC #18205. Ce fichier ne reimplemente rien et ne recopie rien : il
  importe le module amont qui declare l'enonce, et demande au noyau Lean la
  liste des axiomes dont cet enonce depend.

  Enonce amont, `Topology/ThreeManifold/Poincare.lean` ligne 12 :

    theorem poincare_conjecture
        (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] :
        Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

  Toute 3-variete fermee simplement connexe est homeomorphe a la 3-sphere.

  Ce que `#print axioms` mesure ici n'est pas la conjecture : c'est la
  *dependance* de l'enonce tel que l'amont le porte. Un theoreme qui
  dependrait d'un axiome prohibe (`sorryAx`, `native_decide.*`) est visible
  en clair, sans qu'aucune preuve n'ait ete reecrite.

  Depot  : https://github.com/qinz1yang/differential-geometry
  Licence : Apache-2.0
-/

import DifferentialGeometry.Topology.ThreeManifold.Poincare

-- Conjecture de Poincare : 3-variete fermee simplement connexe = 3-sphere.
#print axioms DifferentialGeometry.Topology.poincare_conjecture
