/-
  Knots.Conway — aggregator du nœud de Conway et de Kinoshita-Terasaka
  =====================================================================

  Historiquement monolithe (mutation, codes PD, polynôme d'Alexander,
  preuves de Dehn, slice, Piccirillo), ce module est réduit au stub
  aggregator du plan Option A (#18397, tranches 2-4) : le contenu vit
  désormais dans les sous-modules, tous disponibles par transitivité
  via `import Knots.Conway` (entrée historique préservée) :

  - `Knots.Mutation` — mutation de Conway (tranche 2) ;
  - `Knots.ConwayPD` — codes PD des deux nœuds 11n34/11n42 (tranche 2) ;
  - `Knots.ArcPartition` — partition des arcs du code PD (tranche 3) ;
  - `Knots.AlexanderTrivial` — polynôme d'Alexander et preuves de Dehn
    (conway_trivial_alexander, KT_trivial_alexander) (tranche 4).

  Le volet slice/Piccirillo vit dans `Knots.Slice` (module sœur,
  importé séparément — Slice importe Conway, l'inverse cyclerait).
-/

import Knots.Basic
import Knots.Invariant
import Knots.Mutation
import Knots.ConwayPD
import Knots.ArcPartition
import Knots.AlexanderTrivial
