/-
Grothendieck hommage — Partie 7 : fondements des faisceaux.

Alexandre Grothendieck (1928-2014).

Extension Phase 3 (#2159, Epic #1646).

La Partie 1 (`CategoryAndSites.lean`) a introduit les topologies de
Grothendieck et les cribles. La Partie 5 (`Calibration.lean`) a montré
que tout préfaisceau est un faisceau pour la topologie triviale. La
Partie 6 (`SieveLattice.lean`) a établi les identités de pullback sur
les cribles.

Ce module enregistre les propriétés fondamentales des faisceaux et des
préfaisceaux séparés :

  - Tout faisceau est séparé (l'inclusion fondamentale).
  - Tout préfaisceau est séparé pour la topologie triviale (la plus grossière).
  - Pour une topologie sous-canonique, tout préfaisceau représentable
    est un faisceau.
  - La condition de faisceau se transfère le long des comparaisons
    de topologies (J₁ ≤ J₂).

Ce sont les faits algébriques de base sur les faisceaux sur un site,
connectant les propriétés théoriques de treillis des cribles (Parties 1/6)
avec la condition de faisceau (Partie 5).

Epic #1646, Phase 3 (#2159). Tous les `sorry`s éliminés à la création.

### i18n — convention #4980 ratifiée 2026-07-04

Ce module est jumelé avec sa version anglaise canonique dans le fichier
sibling `SheafBasics_en.lean` (modèle sibling pair, voir PR #6154 pour le
pilote sur `Utility.lean`). Les énoncés de théorèmes, les noms de lemmes,
les tactiques Lean et les références Mathlib restent en anglais (Mathlib 4,
tactic DSL standard). Seules les **docstrings `/-- ... -/`** et les
**commentaires `-- ...`** diffèrent entre les deux fichiers. Anti-§D
byte-identity garanti : le namespace body est préservé bit-pour-bit
(énoncés et preuves byte-identiques entre `SheafBasics.lean` et
`SheafBasics_en.lean`).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Canonical

namespace Grothendieck

universe v u w w'

open CategoryTheory

/-!
## Faisceau ⇒ Séparé

L'inclusion fondamentale : tout faisceau est automatiquement un préfaisceau
séparé. Intuitivement, si un préfaisceau admet des recollages uniques,
alors les familles compatibles ont au plus un recollement (unicité).
-/

/-- Tout faisceau est séparé. Utilise `Presieve.IsSheaf.isSeparated` de Mathlib. -/
theorem sheaf_is_separated {C : Type*} [Category C]
    {J : GrothendieckTopology C} {P : Cᵒᵖ ⥤ Type*}
    (h : Presieve.IsSheaf J P) :
    Presieve.IsSeparated J P :=
  h.isSeparated

/-!
## Préfaisceaux séparés pour la topologie triviale

La topologie triviale ⊥ (la plus grossière) n'a que le crible maximal ⊤
comme couvrant. Comme tout préfaisceau est un faisceau pour ⊥, tout
préfaisceau est aussi séparé.
-/

/-- Tout préfaisceau en `Type` est séparé pour la topologie triviale
    (la plus grossière). Conséquence de `isSheaf_bot` combiné avec
    `sheaf_is_separated`. -/
theorem isSeparated_trivial {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type*) :
    Presieve.IsSeparated (⊥ : GrothendieckTopology C) P :=
  Presieve.isSheaf_bot.isSeparated

/-!
## Topologies sous-canoniques et faisceaux représentables

Une topologie de Grothendieck J est *sous-canonique* si tout préfaisceau
représentable (i.e. `yoneda.obj X` pour tout X) est un faisceau. Ceci est
équivalent à dire que J ≤ la topologie canonique (la plus fine sous-canonique).

La topologie de Zariski sur les schémas est sous-canonique (voir `ZariskiSite.lean`).
-/

/-- Pour une topologie sous-canonique J, le préfaisceau de Yoneda en X est
    un faisceau. C'est le pont clé : l'embedding de Yoneda atterrit dans
    les faisceaux. Utilise `GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable`. -/
theorem yoneda_isSheaf_subcanonical {C : Type*} [Category C]
    (J : GrothendieckTopology C) [J.Subcanonical] (X : C) :
    Presieve.IsSheaf J (yoneda.obj X) :=
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj X)

/-!
## Condition de faisceau le long des comparaisons de topologies

Si J₁ ≤ J₂ (J₁ a moins de cribles couvrants) et P est un faisceau pour J₂,
alors P est un faisceau pour J₁. Plus la topologie est grossière, plus il y
a de préfaisceaux qui sont des faisceaux.
-/

/-- Un préfaisceau qui est un faisceau pour une topologie plus fine est
    aussi un faisceau pour une topologie plus grossière. Utilise
    `Presieve.isSheaf_of_le` de Mathlib. -/
theorem isSheaf_of_le {C : Type*} [Category C]
    {J₁ J₂ : GrothendieckTopology C} (h : J₁ ≤ J₂)
    {P : Cᵒᵖ ⥤ Type*} (hP : Presieve.IsSheaf J₂ P) :
    Presieve.IsSheaf J₁ P :=
  Presieve.isSheaf_of_le P h hP

/-!
## Sous-canonique est clos vers le bas

Si K est sous-canonique et J ≤ K, alors J est aussi sous-canonique.
Ceci suit du fait qu'avoir moins de cribles couvrants rend la condition
de faisceau plus facile à satisfaire.
-/

/-- La sous-canonicité est close vers le bas : si K est sous-canonique et
    J ≤ K, alors J est sous-canonique. Utilise
    `GrothendieckTopology.Subcanonical.of_le`. -/
theorem subcanonical_of_le {C : Type*} [Category C]
    {J K : GrothendieckTopology C} (h : J ≤ K) [K.Subcanonical] :
    J.Subcanonical :=
  GrothendieckTopology.Subcanonical.of_le h

/-!
## La topologie triviale est sous-canonique

Puisque la topologie triviale ⊥ est en-dessous de toute topologie,
et que toute topologie est en-dessous de la topologie canonique (qui est
sous-canonique), la topologie triviale est sous-canonique.
-/

/-- La topologie triviale (la plus grossière) est sous-canonique.
    Tout préfaisceau est un faisceau pour ⊥, donc en particulier tout
    préfaisceau représentable est un faisceau. Utilise
    `GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj`. -/
theorem trivial_subcanonical {C : Type*} [Category C] :
    @GrothendieckTopology.Subcanonical C _ (⊥ : GrothendieckTopology C) :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj ⊥
    (fun _ => Presieve.isSheaf_bot)

/-!
## Préservation des conditions de faisceau par isomorphismes de préfaisceaux

Les conditions `IsSheaf` et `IsSeparated` sont des **propriétés de la classe
d'isomorphie** du préfaisceau. Si `P ≅ P'`, alors `P` est un faisceau (resp.
séparé) si et seulement si `P'` l'est. Cette invariance est nécessaire pour
toute la théorie : les faisceaux forment une sous-catégorie pleine de la
catégorie des préfaisceaux, et la pleine-fidélité exige que les isomorphismes
entre objets préservent la propriété.

Ce sont `isSheaf_iso` et `isSeparated_iso` de Mathlib (`SheafOfTypes.lean`).
-/

/-- La condition `IsSheaf` est préservée par isomorphisme de préfaisceaux :
    si `P ≅ P'` et `P` est un faisceau, alors `P'` est un faisceau. C'est
    la stabilité des faisceaux sous les isomorphismes — propriété nécessaire
    pour la pleine-fidélité de l'inclusion `Sheaf J A ↪ Presheaf A`.
    Utilise `Presieve.isSheaf_iso` de Mathlib. -/
theorem isSheaf_iso {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {P P' : Cᵒᵖ ⥤ Type w}
    (i : P ≅ P') (h : Presieve.IsSheaf J P) :
    Presieve.IsSheaf J P' :=
  Presieve.isSheaf_iso J i h

/-- La condition `IsSeparated` est préservée par isomorphisme de préfaisceaux :
    si `P ≅ P'` et `P` est séparé, alors `P'` est séparé. Symétrique de
    `isSheaf_iso` pour la séparation. Utilise `Presieve.isSeparated_iso`
    de Mathlib. -/
theorem isSeparated_iso {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {P P' : Cᵒᵖ ⥤ Type w}
    (i : P ≅ P') (hP : Presieve.IsSeparated J P) :
    Presieve.IsSeparated J P' :=
  Presieve.isSeparated_iso J i hP

/-!
## Symétrie : la séparation descend le long des comparaisons de topologies

Tout comme `IsSheaf` descend le long de `J₁ ≤ J₂` (cf. `isSheaf_of_le`),
la condition `IsSeparated` descend aussi. Plus la topologie est grossière,
plus il est facile d'être séparé.

C'est `isSeparated_of_le` de Mathlib (`SheafOfTypes.lean`).
-/

/-- La condition `IsSeparated` descend le long des comparaisons de topologies :
    si `J₁ ≤ J₂` et `P` est séparé pour `J₂`, alors `P` est séparé pour `J₁`.
    Symétrique de `isSheaf_of_le` pour la séparation. Utilise
    `Presieve.isSeparated_of_le` de Mathlib. -/
theorem isSeparated_of_le {C : Type u} [Category.{v} C]
    {J₁ J₂ : GrothendieckTopology C}
    (P : Cᵒᵖ ⥤ Type w) (h : J₁ ≤ J₂)
    (hP : Presieve.IsSeparated J₂ P) :
    Presieve.IsSeparated J₁ P :=
  Presieve.isSeparated_of_le P h hP

/-!
## Équivalence de IsSheaf via équivalence naturelle de préfaisceaux

Une **équivalence naturelle** entre préfaisceaux `e : P₁ ≅ P₂` (un isomorphisme
naturel, i.e. composant par composant) préserve aussi la condition `IsSheaf`,
et ce **dans les deux sens**. C'est strictement plus fort que l'invariance
par un isomorphisme global de préfaisceaux : on a `IsSheaf J P₁ ↔ IsSheaf J P₂`
via une équivalence naturelle.

C'est `isSheaf_iff_of_nat_equiv` de Mathlib (`SheafOfTypes.lean`).
-/

/-- Une équivalence naturelle entre préfaisceaux préserve la condition
    `IsSheaf` dans les deux sens : `IsSheaf J P₁ ↔ IsSheaf J P₂` via une
    famille d'équivalences composant par composant. Plus fort qu'un isomorphisme
    global de préfaisceaux : la condition est préservée composant par composant.
    Utilise `Presieve.isSheaf_iff_of_nat_equiv` de Mathlib. -/
theorem isSheaf_iff_of_nat_equiv {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {P₁ : Cᵒᵖ ⥤ Type w} {P₂ : Cᵒᵖ ⥤ Type w'}
    (e : ∀ ⦃X : C⦄, P₁.obj (Opposite.op X) ≃ P₂.obj (Opposite.op X))
    (he : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : P₁.obj (Opposite.op Y)),
      e (P₁.map f.op x) = P₂.map f.op (e x)) :
    Presieve.IsSheaf J P₁ ↔ Presieve.IsSheaf J P₂ :=
  Presieve.isSheaf_iff_of_nat_equiv e he

end Grothendieck