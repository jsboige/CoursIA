/-
Knots.ReidemeisterInvariance — Invariance des invariants sous Reidemeister
=========================================================================

Domicile du theoreme d'invariance : `alexanderPolynomialSigned` est invariant
sous les trois mouvements de Reidemeister (issue #16650, tranche 3 du socle
Alexander, cadrage `docs/lean/alexander-strategy/c652-reidemeister-invariance.md`).

Pourquoi un module separe : le theoreme croise `Reidemeister3Connected`
(`Knots.Reidemeister`) et `alexanderPolynomialSigned` (`Knots.Conway`).
`Knots.Conway` importe `Knots.Invariant`, qui importe `Knots.Reidemeister` —
importer `Knots.Conway` suffit donc a voir les deux, et l'inverse serait un
cycle. Ce module est le point ou les deux theories se rencontrent.

Convention i18n (EPIC #4980) : ce fichier est **FR canonique**, avec son miroir
anglais dans le sibling `ReidemeisterInvariance_en.lean`.
-/

import Knots.Conway

namespace Knots

/-! ## 1. La bifurcation `i = 0` / `i ≥ 1` (mise au point du cadrage)

Le cadrage c652 (§4.1) presente R3 comme « trivial par reindexation ». C'est
vrai **sous une condition qui n'y est pas enoncee** : que le triangle soit
entierement hors de la ligne eliminee du mineur designe.

`alexanderPolynomialSigned` supprime la **premiere** ligne (`rest` = queue de
`crossings`) et la derniere colonne du mineur. Donc :

* **`i ≥ 1`** — les trois lignes reecrites du triangle sont dans le corps de la
  matrice ; l'invariance est un argument de reindexation : la chirurgie ne
  change ni le nombre de croisements, ni le nombre d'aretes, et la partition
  d'arcs est preservee (section 2 ci-dessous). Le mineur est inchange au
  transport des colonnes pres.
* **`i = 0`** — la ligne 0 porte un sommet du triangle, et c'est precisement
  celle que le mineur designe **elimine**. La reindexation ne suffit plus : le
  mineur change de forme (des coefficients quittent les colonnes du triangle
  pour d'autres), et l'invariance ne peut se lire qu'a une **unite** `±t^k`
  pres — c'est l'argument determinant al des sections 4.2-4.3 du cadrage
  (colonne non partagee, rang du mineur augmente).

Les deux cas sont donc de nature differente et doivent etre des theoremes
distincts. Les confondre ferait passer `i = 0` pour un oubli de preuve alors que
c'est le cas ou le mineur designe change reellement de forme.

## 2. L'obligation de preservation de la partition d'arcs

L'argument de reindexation (`i ≥ 1`) repose sur une premiere que le cadrage
**suppose sans la prouver** : `arcPartition` est preservee par la chirurgie.

L'enonce general demande : la chirurgie R3 connectee reecrit les paires
`(e2, e4)` des trois croisements du triangle (cf `Conway.lean:350-354`,
`pairs := d.crossings.map (fun c => (c.e2, c.e4))`). Sur le temoin du lake
(`reidemeister3Connected_satisfiable`), ces paires, prises comme multi-ensemble
non ordonne (`mergePair` est symetrique en ses deux arguments), **coincident**
entre X et Y — la partition est donc preservee trivialement, et `decide` au
kernel suffit a etablir le theoreme.

Ce temoin ne suffit donc pas, a lui seul, a fonder la preservation generale :
un contre-exemple minimal ou les paires `(e2, e4)` du triangle different entre
X et Y reste a exhiber. C'est le premier verrou de la tranche, avant tout
argument de reindexation.
-/

/-! ## 3. Controle : la partition d'arcs du temoin R3 est preservee

Le temoin est celui de `reidemeister3Connected_satisfiable` (litteraux repris
tels quels) : les deux diagrammes sont bien formes (`decide` sur `wf` au lake),
et leur partition d'arcs — 5 classes pour 10 aretes — est **la meme** de part et
d'autre de la chirurgie. C'est le **controle trivial** de la section 2 : sur ce
temoin, les paires `(e2, e4)` du triangle, prises comme multi-ensemble, sont les
memes des deux cotes — la preservation est vide. Un contre-exemple ou elles
different reste a exhiber pour etablir la preservation generale.
-/

/-- Controle de la tranche 3 (etape 1) : sur la paire temoin du move R3
    connecte, la chirurgie preserve `arcPartition`. Sur ce temoin, les paires
    `(e2, e4)` du triangle coincident comme multi-ensemble entre X et Y, donc la
    preservation est triviale ; la forme generale (sur des diagrammes ou les
    paires du triangle different) reste a prouver. -/
theorem reidemeister3Connected_arcPartition_witness :
    arcPartition
        { crossings := [⟨1, 2, 7, 8⟩, ⟨3, 7, 9, 4⟩, ⟨9, 8, 5, 6⟩,
                        ⟨1, 2, 10, 10⟩, ⟨3, 4, 5, 6⟩], numEdges := 10 }
      = arcPartition
        { crossings := [⟨3, 4, 9, 7⟩, ⟨9, 2, 5, 8⟩, ⟨7, 8, 1, 6⟩,
                        ⟨1, 2, 10, 10⟩, ⟨3, 4, 5, 6⟩], numEdges := 10 } := by
  decide

end Knots
