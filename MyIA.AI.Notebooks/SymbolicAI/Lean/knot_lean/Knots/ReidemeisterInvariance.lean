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

Precisons l'obstacle sur le temoin : la chirurgie R3 connectee reecrit les
paires `(e2, e4)` des trois croisements du triangle (cf `Conway.lean`,
`pairs := d.crossings.map (fun c => (c.e2, c.e4))`). Sur le temoin du lake
(`reidemeister3Connected_satisfiable`), ces paires coincident comme paires
**non orientees** —

    X : (2,8), (7,4), (8,6)      Y : (4,7), (2,8), (8,6)

— mais seule l'**orientation** de la paire centrale differe ((7,4) contre
(4,7)), et les croisements reecrits changent de **position** dans la liste du
repli. Le repli voit des paires orientees prises dans l'ordre de la liste :
la preservation n'y est donc **pas vide** — elle exige d'absorber l'une et
l'autre difference, par l'insensibilite a l'orientation d'une paire
(`mergePair_symm`, #17429) puis par la commutation des fusions au niveau des
classes (`mergePair_mergePair_comm_equiv`, #17646). Ce qui est preserve par
ailleurs est le **multi-ensemble des etiquettes** (docstring de
`Reidemeister3Connected`), d'ou `wf`.

Ce temoin ne suffit pas, a lui seul, a fonder la preservation generale : un
diagramme ou les paires `(e2, e4)` du triangle different reellement comme
multi-ensemble reste a exhiber. C'est le premier verrou de la tranche, avant
tout argument de reindexation.
-/

/-! ## 3. Controle : la partition d'arcs du temoin R3 est preservee

Le temoin est celui de `reidemeister3Connected_satisfiable` (litteraux repris
tels quels) : les deux diagrammes sont bien formes (`decide` sur `wf` au lake),
et leur partition d'arcs — 5 classes pour 10 aretes — est **la meme** de part et
d'autre de la chirurgie. C'est le controle positif de la section 2 : les paires
`(e2,e4)` du triangle y coincident non orientees, avec une orientation et une
position de repli differentes — le repli produit la meme partition, et c'est
`foldl_mergePair_swap` (orientation) puis `foldl_mergePair_permute_adjacent`
(transposition des positions) qui le justifient. Un temoin ou les paires
different comme multi-ensemble reste a exhiber pour la preservation generale.
-/

/-- Controle de la tranche 3 (etape 1) : sur la paire temoin du move R3
    connecte, la chirurgie preserve `arcPartition` — les paires `(e2,e4)` du
    triangle coincident non orientees, et le repli absorbe leurs differences
    d'orientation et de position (`foldl_mergePair_swap`,
    `foldl_mergePair_permute_adjacent`). C'est la premiere que l'argument de
    reindexation (cas `i ≥ 1`) suppose ; la forme generale reste a prouver. -/
theorem reidemeister3Connected_arcPartition_witness :
    arcPartition
        { crossings := [⟨1, 2, 7, 8⟩, ⟨3, 7, 9, 4⟩, ⟨9, 8, 5, 6⟩,
                        ⟨1, 2, 10, 10⟩, ⟨3, 4, 5, 6⟩], numEdges := 10 }
      = arcPartition
        { crossings := [⟨3, 4, 9, 7⟩, ⟨9, 2, 5, 8⟩, ⟨7, 8, 1, 6⟩,
                        ⟨1, 2, 10, 10⟩, ⟨3, 4, 5, 6⟩], numEdges := 10 } := by
  decide

end Knots
