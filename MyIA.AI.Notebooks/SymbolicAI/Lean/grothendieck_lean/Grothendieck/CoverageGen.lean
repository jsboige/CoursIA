/-

# Hommage Grothendieck — Partie 9 : Génération de couverture et caractérisation des faisceaux

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-4 ont établi les fondamentaux : catégories, cribles, topologies,
lois de treillis, identités de pullback, bases de faisceaux, clôture couvrante.
Les parties 5-8 ont bâti dessus avec calibration, lois de treillis, propriétés
de faisceaux, et ordre des topologies.

Ce module aborde la question centrale de génération : comment *construire*
une topologie de Grothendieck à partir de données plus simples ?

  - Une **couverture** (Coverage) est une collection de familles couvrantes
    stable par pullback (mais pas nécessairement saturée par transitivité).
  - `Coverage.toGrothendieck` sature une couverture en une topologie pleine.
  - Le **théorème clé** : un préfaisceau est un faisceau pour la topologie
    générée ssi il satisfait la condition de faisceau pour chaque famille
    couvrante.
  - La borne sup de couvertures correspond à l'intersection des catégories
    de faisceaux.

Ces faits montrent que les couvertures (données bien plus simples)
déterminent la même théorie des faisceaux que la topologie pleine
qu'ils engendrent.

EPIC #1646, Phase 5 (#2159). Tous les `sorry`s éliminés à la création.

### Note d'accessibilité (Epics #1452/#1453)

Ce module expose **7 theorem + 1 abbrev** sur la génération de couverture
(bridge Coverage → GrothendieckTopology → Presheaf.IsSheaf), accessibilité
progressive par 6 sections thématiques : (1) Coverage → topologie de Grothendieck,
(2) infimum des topologies, (3) sup de couvertures et préservation des faisceaux,
(4) préservation par sur-ensemble, (5) génération de crible, (6) pont topologie/couverture.

### Convention i18n (EPIC #4980 ratifiée par user 2026-07-04)

Ce module substantiel est apparié avec son jumeau anglais dans le fichier sibling
`CoverageGen_en.lean` (modèle sibling pair, voir PR #6154 pour le pilote sur
`Utility.lean`).
-/

import Mathlib.CategoryTheory.Sites.Coverage

namespace Grothendieck

open CategoryTheory
/-!
## Couverture → topologie de Grothendieck

Une couverture K sur C est une collection de pré-cribles couvrants en chaque objet,
stable par pullback. La fonction `Coverage.toGrothendieck` sature une couverture
en une topologie de Grothendieck pleine en clôturant sous :
  - le crible maximal (axiome d'identité)
  - la stabilité par pullback (héritée de K)
  - la transitivité (générée depuis K)

Le résultat est la *plus petite* topologie de Grothendieck contenant K.
-/

/-- La topologie de Grothendieck générée par une couverture.
    C'est `Coverage.toGrothendieck` : la plus petite topologie dont
    la couverture associée contient K. -/

abbrev coverageToTopology {C : Type*} [Category C] (K : Coverage C) :
    GrothendieckTopology C :=
  Coverage.toGrothendieck K

/-!
## La conversion couverture → topologie est un infimum

La topologie générée par une couverture K est l'infimum de toutes les topologies
dont la couverture associée contient K. Cela donne une caractérisation alternative
via la théorie de l'ordre.
-/

/-- La topologie générée par une couverture K est l'infimum de toutes les
    topologies J telles que K ≤ J.toCoverage.
    Restatement direct de `Coverage.toGrothendieck_eq_sInf`. -/

theorem coverageToTopology_eq_sInf {C : Type*} [Category C] (K : Coverage C) :
    Coverage.toGrothendieck K =
    sInf {J : GrothendieckTopology C | K ≤ J.toCoverage} :=
  Coverage.toGrothendieck_eq_sInf K

/-!
## Sup de couvertures et préservation des faisceaux

La borne sup de deux couvertures K ⊔ L couvre chaque objet par l'union des familles
de K et de L. La condition de faisceau pour la sup-couverture équivaut à être un
faisceau pour K et pour L individuellement.
-/

/-- Familles couvrantes pour la sup de deux couvertures.
    Restatement direct de `Coverage.sup_covering`. -/

theorem sup_coverage {C : Type*} [Category C] (K L : Coverage C) (X : C) :
    (K ⊔ L) X = K X ∪ L X :=
  Coverage.sup_covering K L X

/-- Un préfaisceau à valeurs dans Type est un faisceau pour la topologie
    générée par une couverture ssi il satisfait la condition de faisceau pour
    chaque famille couvrante de la couverture. C'est le **théorème fondamental**
    connectant couvertures et théorie des faisceaux : la donnée plus simple
    d'une couverture suffit.
    Utilise `Presieve.isSheaf_coverage`. -/

theorem isSheaf_coverageToTopology {C : Type*} [Category C]
    (K : Coverage C) (P : Cᵒᵖ ⥤ Type*) :
    Presieve.IsSheaf (Coverage.toGrothendieck K) P ↔
    ∀ {X : C} (R : Presieve X), R ∈ K X → Presieve.IsSheafFor P R :=
  Presieve.isSheaf_coverage K P

/-- Un préfaisceau est un faisceau pour la topologie générée par K ⊔ L
    ssi il est un faisceau pour la topologie générée par chaque couverture
    individuellement.
    Utilise `Presieve.isSheaf_sup`. -/

theorem isSheaf_sup_coverage {C : Type*} [Category C]
    (K L : Coverage C) (P : Cᵒᵖ ⥤ Type*) :
    Presieve.IsSheaf (K ⊔ L).toGrothendieck P ↔
    Presieve.IsSheaf K.toGrothendieck P ∧ Presieve.IsSheaf L.toGrothendieck P :=
  Presieve.isSheaf_sup K L P

/-!
## Tout pré-crible couvrant contenu dans un crible rend ce crible couvrant

Si R ∈ K X (un pré-crible couvrant pour la couverture) et R ≤ S (le pré-crible
est contenu dans le crible S), alors S est couvrant pour la topologie générée.
-/

/-- Préservation par sur-ensemble : si un pré-crible couvrant R est contenu
    dans un crible S, alors S est couvrant pour la topologie générée.
    Utilise `Coverage.mem_toGrothendieck_sieves_of_superset`. -/

theorem superset_mem_coverageToTopology {C : Type*} [Category C]
    (K : Coverage C) {X : C} {S : Sieve X} {R : Presieve X}
    (hRS : R ≤ S) (hR : R ∈ K X) :
    S ∈ Coverage.toGrothendieck K X :=
  Coverage.mem_toGrothendieck_sieves_of_superset K hRS hR

/-!
## Génération de crible depuis des pré-cribles couvrants

Un pré-crible couvrant R génère un crible couvrant pour la topologie associée.
C'est la façon la plus élémentaire dont une famille couvrante produit un crible
couvrant.
-/

/-- Un pré-crible couvrant génère un crible couvrant pour la topologie de
    Grothendieck associée. Utilise `Coverage.Saturate.of`. -/

theorem generate_mem_coverageToTopology {C : Type*} [Category C]
    (K : Coverage C) {X : C} {R : Presieve X} (hR : R ∈ K X) :
    Sieve.generate R ∈ Coverage.toGrothendieck K X :=
  Coverage.Saturate.of _ _ hR

/-!
## Les couvrants de topologie étendent les couvrants de couverture

Chaque pré-crible couvrant d'une couverture s'étend en un crible couvrant via
`Sieve.generate`. Cela fait le pont entre pré-cribles et cribles.
-/

/-- Un crible généré depuis une famille couvrante couvre dans la topologie
    générée. Restatement utilisant `Sieve.generate`. -/

theorem sieve_generate_covering {C : Type*} [Category C]
    (K : Coverage C) (X : C) (R : Presieve X) (hR : R ∈ K X) :
    Sieve.generate R ∈ Coverage.toGrothendieck K X :=
  Coverage.Saturate.of _ _ hR

end Grothendieck
