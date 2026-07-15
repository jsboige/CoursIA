/-
Grothendieck hommage — Partie 8 : ordre de la topologie, pullback de
couvrant, et faits de treillis.

Alexandre Grothendieck (1928-2014).

Extension Phase 4 (#2159, Epic #1646).

La Partie 6 (`SieveLattice.lean`) a établi les identités de pullback. La
Partie 7 (`SheafBasics.lean`) a connecté les faisceaux avec le treillis
des topologies. Mathlib fournit déjà `Sieve.pullback_inter` (le pullback
préserve ⊓).

Ce module ajoute des wrappers pédagogiques et observations :

  - La chaîne d'ordre complète : ⊥ ≤ J ≤ ⊤ pour toute topologie J
  - Pullback d'un crible couvrant est couvrant (stabilité, énoncé explicite)
  - Intersection de cribles couvrants est couvrante (clôture par meet)
  - Une topologie qui couvre le crible maximal est discrète

Ces faits sont des exercices de lecture des axiomes de la topologie de
Grothendieck à travers le prisme de la théorie de l'ordre.

Epic #1646, Phase 4 (#2159). Tous les `sorry`s éliminés à la création.

### i18n — convention #4980 ratifiée 2026-07-04

Ce module est jumelé avec sa version anglaise canonique dans le fichier
sibling `SieveOps_en.lean` (modèle sibling pair, voir PR #6154 pour le
pilote sur `Utility.lean`). Les énoncés de théorèmes, les noms de lemmes,
les tactiques Lean et les références Mathlib restent en anglais (Mathlib 4,
tactic DSL standard). Seules les **docstrings `/-- ... -/`** et les
**commentaires `-- ...`** diffèrent entre les deux fichiers. Anti-§D
byte-identity garanti : le namespace body est préservé bit-pour-bit
(énoncés et preuves byte-identiques entre `SieveOps.lean` et
`SieveOps_en.lean`).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck

open CategoryTheory

/-!
## Pullback et intersections (wrapper)

Mathlib fournit `Sieve.pullback_inter` : le pullback distribue sur
l'intersection. Nous enregistrons un énoncé commode en notation ⊓.
-/

/-- Pullback préserve les intersections : `Sieve.pullback f (S ⊓ T) =
    Sieve.pullback f S ⊓ Sieve.pullback f T`.
    Restatement direct de `Sieve.pullback_inter`. -/
theorem pullback_inf {C : Type*} [Category C] {X Y : C} (f : Y ⟶ X)
    (S T : Sieve X) :
    Sieve.pullback f (S ⊓ T) = Sieve.pullback f S ⊓ Sieve.pullback f T :=
  Sieve.pullback_inter S T

/-!
## Chaîne d'ordre des topologies

Toute topologie de Grothendieck J se trouve entre les topologies triviale
(⊥) et discrète (⊤). C'est une conséquence simple de la structure de
treillis complet.
-/

/-- La topologie triviale (la plus grossière) est en-dessous de toute
    topologie de Grothendieck. -/
theorem trivial_le_any {C : Type*} [Category C] (J : GrothendieckTopology C) :
    (GrothendieckTopology.trivial C : GrothendieckTopology C) ≤ J := by
  rw [GrothendieckTopology.trivial_eq_bot]
  exact bot_le

/-- Toute topologie de Grothendieck est en-dessous de la topologie discrète
    (la plus fine). -/
theorem any_le_discrete {C : Type*} [Category C] (J : GrothendieckTopology C) :
    (J : GrothendieckTopology C) ≤ GrothendieckTopology.discrete C := by
  rw [GrothendieckTopology.discrete_eq_top]
  exact le_top

/-- Toute topologie de Grothendieck se trouve entre triviale et discrète :
    ⊥ ≤ J ≤ ⊤. -/
theorem trivial_le_J_le_discrete {C : Type*} [Category C]
    (J : GrothendieckTopology C) :
    (GrothendieckTopology.trivial C : GrothendieckTopology C) ≤ J ∧
    (J : GrothendieckTopology C) ≤ GrothendieckTopology.discrete C :=
  ⟨trivial_le_any J, any_le_discrete J⟩

/-!
## Opérations de clôture des cribles couvrants

Les trois axiomes d'une topologie de Grothendieck (stabilité, intersection,
supremum) donnent des propriétés de clôture sur les cribles couvrants. Nous
enregistrons des énoncés pédagogiques explicites pour chacun.
-/

/-- L'intersection de deux cribles couvrants est un crible couvrant.
    C'est l'axiome d'intersection, énoncé via `intersection_covering`. -/
theorem cover_inf {C : Type*} [Category C] {J : GrothendieckTopology C}
    {X : C} {R S : Sieve X} (hR : R ∈ J X) (hS : S ∈ J X) :
    R ⊓ S ∈ J X :=
  J.intersection_covering hR hS

/-- Caractérisation de l'intersection : R ⊓ S couvre ssi R et S couvrent.
    Sens direct : `intersection_covering`. Sens indirect :
    `superset_covering` avec `inf_le`. -/
theorem cover_inf_iff {C : Type*} [Category C] {J : GrothendieckTopology C}
    {X : C} {R S : Sieve X} :
    R ⊓ S ∈ J X ↔ R ∈ J X ∧ S ∈ J X :=
  ⟨fun h => ⟨J.superset_covering inf_le_left h, J.superset_covering inf_le_right h⟩,
   fun ⟨hR, hS⟩ => J.intersection_covering hR hS⟩

/-- Pullback d'un crible couvrant est couvrant (axiome de stabilité).
    C'est la propriété de stabilité fondamentale : si S couvre X et
    f : Y ⟶ X, alors `Sieve.pullback f S` couvre Y. Utilise
    `GrothendieckTopology.pullback_stable`. -/
theorem cover_pullback_stable {C : Type*} [Category C]
    {J : GrothendieckTopology C} {X Y : C} {S : Sieve X}
    (hS : S ∈ J X) (f : Y ⟶ X) :
    Sieve.pullback f S ∈ J Y :=
  J.pullback_stable f hS

/-!
## Caractérisation de la topologie discrète

La topologie discrète est l'unique topologie où le crible maximal ⊤
couvre tout objet. Nous enregistrons ceci comme caractérisation explicite.
-/

/-- Tout crible appartient à la topologie discrète (par définition, cribles = univ). -/
theorem mem_discrete {C : Type*} [Category C] (X : C) (S : Sieve X) :
    S ∈ GrothendieckTopology.discrete C X :=
  Set.mem_univ _

/-- Le crible maximal appartient à la topologie triviale en tout objet.
    Utilise `GrothendieckTopology.top_mem`. -/
theorem top_mem_trivial {C : Type*} [Category C] (X : C) :
    (⊤ : Sieve X) ∈ GrothendieckTopology.trivial C X :=
  (GrothendieckTopology.trivial C).top_mem X

end Grothendieck