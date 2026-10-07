/-
  Visite — trois petites fermetures de qinz1yang/differential-geometry v0.1.3
  ===========================================================================

  Ce fichier ne reimplemente rien et ne recopie rien : il importe trois
  modules de l'amont — declare en dependance Lake dans lakefile.lean — et
  demande au noyau Lean la liste des axiomes dont depend un theoreme-tete de
  chacune des trois fermetures citees par l'EPIC #18205 :

  1. lemme de Morse          Topology/Morse/ExtremumChart.lean
  2. cohomologie de de Rham  Tensor/Exterior/Cochain.lean
  3. Bonnet-Myers            Geometry/Comparison/BonnetMyers/Diameter.lean

  La sortie de `#print axioms` est le temoin de cette visite : un theoreme qui
  dependrait d'un axiome prohibe (`sorryAx`, `native_decide.*`) est visible
  ici, en clair, sans qu'aucune preuve n'ait ete reecrite.

  L'amont annonce n'utiliser que `propext`, `Classical.choice` et `Quot.sound`.
  Ce fichier mesure cette annonce sur trois points d'entree, il ne la reprend
  pas sur parole.

  Depot  : https://github.com/qinz1yang/differential-geometry
  Licence : Apache-2.0
-/

import DifferentialGeometry.Topology.Morse.ExtremumChart
import DifferentialGeometry.Tensor.Exterior.Cochain
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.Diameter

-- 1. Lemme de Morse : existence d'une carte quadratique en un minimum local.
#print axioms DifferentialGeometry.Topology.Morse.exists_quadratic_chart_of_isLocalMin

-- 2. Cohomologie de de Rham : l'identite induit l'identite en cohomologie.
#print axioms DifferentialGeometry.DifferentialForm.pullbackCohomologyMap_id

-- 3. Bonnet-Myers : borne de diametre sous borne inferieure de courbure de Ricci.
#print axioms DifferentialGeometry.Geometry.Riemannian.BonnetMyers.bonnet_myers_diameter_le_of_complete_metric
