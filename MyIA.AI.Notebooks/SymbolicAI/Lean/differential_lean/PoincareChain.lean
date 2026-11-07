/-
  Temoin — la chaine de preuve de Poincare (qinz1yang/differential-geometry v0.1.3)
  ==================================================================================

  Compagnon de `Poincare.lean`, pour le Pli 2 de l'EPIC #18205. La ou
  `Poincare.lean` demande les axiomes de l'enonce seul, ce fichier descend
  la chaine que la preuve emprunte reellement, maillon par maillon, et
  demande au noyau la dependance axiomatique de chacun.

  La preuve de l'enonce tient en cinq lignes de tactiques (indexation mesuree le
  2026-10-30 : 23 lignes de module, 11 pour le bloc du theoreme enonce compris,
  5 apres `:= by`), dans
  `Topology/ThreeManifold/Poincare.lean` :

    obtain ⟨C, hC⟩ := PiecewiseLinear.exists_isManifold_three (M := M)
    let := C
    let : IsManifold (𝓡 3) ∞ M := hC
    obtain ⟨f⟩ := PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_holds M
    exact ⟨f.toHomeomorph⟩

  Trois temps, et ils ne sont pas symetriques :

    1. Moise (`exists_isManifold_three`) fabrique une structure lisse sur la
       3-variete topologique. C'est la porte d'entree : le flot de Ricci
       exige `IsManifold (𝓡 3) ∞ M`, que les hypotheses topologiques de
       l'enonce ne fournissent pas.
    2. Le flot de Ricci avec chirurgie rend un DIFFEOMORPHISME vers la
       3-sphere (`smoothPoincareConjecture_holds`) — strictement plus fort
       que l'enonce topologique.
    3. `toHomeomorph` ramene le resultat au monde topologique.

  Ce que `#print axioms` mesure ici, maillon par maillon, est la
  *dependance* de chaque etape telle que l'amont la porte. Un maillon qui
  dependrait d'un axiome prohibe (`sorryAx`, `native_decide.*`) est visible
  en clair, sans qu'aucune preuve n'ait ete reecrite. Ce fichier ne prouve
  donc pas la conjecture : il prouve que la chaine publiee ne triche pas.

  Depot  : https://github.com/qinz1yang/differential-geometry
  Licence : Apache-2.0

  Note de build : la fermeture de cet enonce a coute 22 909 jobs et
  11 253 s en local (#21916). Ce fichier de visite n'ajoute aucun travail
  de preuve, mais il partage le cache de build de l'amont.
-/

import DifferentialGeometry.Topology.PiecewiseLinear.Moise352Producer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Skeleton.PoincareEndgame
import DifferentialGeometry.Topology.ThreeManifold.Poincare

-- 1. Moise : toute 3-variete topologique admet une structure lisse.
#print axioms DifferentialGeometry.Topology.PiecewiseLinear.exists_isManifold_three

-- 2. Le maillon de Hamilton : extinction en temps fini sous Ricci positive.
#print axioms DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.exists_hamilton_finite_time_flow_on_closed_open

-- 3. L'extinction controlee, assemblee par la chirurgie.
#print axioms DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction

-- 4. La conjecture de Poincare lisse : un diffeomorphisme vers la 3-sphere.
#print axioms DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_holds

-- 5. La conjecture de Poincare topologique : un homeomorphisme.
#print axioms DifferentialGeometry.Topology.poincare_conjecture
