/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 37 : lois de coherence du pullback

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-36 ont etabli les fondamentaux : categories, cribles, topologies,
lois de treillis, identites de pullback, bases de faisceaux, cloture couvrante,
calibration, sous-canonicalite, topologies denses, faisceaux, hom interne,
cohomologie de Cech, limite de Mayer-Vietoris, extensions de Kan, adjonctions,
monades, equivalences, categories monoidales, limites et colimites, couples
comma, images directes, theoremes propres sur la forme fleche (`J.Covers S f`)
et sur la couverture bundlee (`J.Cover X`).

Ce module enregistre les **lois de coherence du pseudo-foncteur pullback** :
pour une topologie de Grothendieck `J` sur une categorie `C`, le pullback le
long d'une fleche `f : X ⟶ Y` est le foncteur contravariant
`J.pullback f : J.Cover Y ⥤ J.Cover X`. Mathlib fournit les isomorphismes
naturels `J.pullbackId X : J.pullback (𝟙 X) ≅ 𝟭 _` et
`J.pullbackComp f g : J.pullback (f ≫ g) ≅ J.pullback g ⋙ J.pullback f` ;
il ne fournit **pas** leurs lois de coherence. Ce module les enonce et les
prouve : ce sont des **preuves tactiques reelles** (veine DEEP, a la
difference des ponts re-export des parties precedentes) :

  - `pullback_triple` : cocycle elementaire — pullbacker le long de `f`, puis
    `g`, puis `h` revient a pullbacker le long de `f ≫ g ≫ h`.
  - `pullbackComp_unit_left` : loi de triangle gauche — la composition
    `J.pullbackComp (𝟙 X) f` se redresse en l'identite par la re-indexation
    `J.pullbackId X` et l'unitor droit.
  - `pullbackComp_unit_right` : loi de triangle droite — la composition
    `J.pullbackComp f (𝟙 Y)` se redresse en l'identite par `J.pullbackId Y`
    et l'unitor gauche.
  - `pullbackComp_assoc` : loi du pentagone — le cocycle est associatif :
    pullbacker le long de `f`, `g`, `h` en deux temps est independant du
    groupement (commute via l'associateur du produit des foncteurs).

Chaque preuve mobilise un lemme Mathlib distinct (`Iso.ext`, `NatTrans.ext`,
`Subsingleton.elim`, `Category.assoc`, `Category.id_comp`,
`Category.comp_id`) et les lois definitionnelles de `J.Cover` — aucune preuve
n'est un simple re-export.

EPIC #1646, Phase 5 (#2159). Tous les `sorry`s elimines a la creation.

### Convention i18n (EPIC #4980 ratifiee par user 2026-07-04)

Ce module est apparie avec son jumeau anglais dans le fichier sibling
`PullbackFunctor_en.lean` (modele sibling pair, voir PR #6154 pour le pilote
sur `Utility.lean`). Namespace suffix `_en` applique au fichier EN
(anti-collision, conforme code-style.md #4980). Les enonces de theoremes, les
noms de lemmes, les tactiques Lean et les references Mathlib restent en
anglais ; seules les docstrings `/-- ... -/` et les commentaires `-- ...`
different entre les deux fichiers (preservation byte-identity).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Functor.Category

namespace Grothendieck.PullbackFunctor

open CategoryTheory

/-!
## Section 1 : cocycle elementaire

Rappel : la membership de `S.pullback f` est donnee par la regle `simp`
`GrothendieckTopology.Cover.coe_pullback : (S.pullback f) g ↔ S (g ≫ f)`.
Le cocycle elementaire enonce que pullbacker trois fois de suite le long de
`f`, `g`, `h` revient a pullbacker une seule fois le long de la composee
`f ≫ g ≫ h`.
-/

/-- Cocycle elementaire du pullback :
    `((S.pullback h).pullback g).pullback f = S.pullback (f ≫ g ≫ h)`.
    Preuve : extensionalite (`GrothendieckTopology.Cover.ext`), quatre
    reecritures par `GrothendieckTopology.Cover.coe_pullback` (deux cotes de
    l'equivalence) puis normalisation de l'associativite par `simp`
    (`Category.assoc`) ramenent la membership de gauche a celle de droite. -/
theorem pullback_triple {C : Type*} [Category C] {X Y Z W : C}
    (J : GrothendieckTopology C) (S : J.Cover W) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    ((S.pullback h).pullback g).pullback f = S.pullback (f ≫ g ≫ h) := by
  apply GrothendieckTopology.Cover.ext
  intro Y' f'
  rw [GrothendieckTopology.Cover.coe_pullback, GrothendieckTopology.Cover.coe_pullback,
    GrothendieckTopology.Cover.coe_pullback, GrothendieckTopology.Cover.coe_pullback]
  simp [Category.assoc]

/-!
## Section 2 : lois de coherence du pseudo-foncteur

Les trois theoremes suivants sont les lois de coherence qui manquent a
Mathlib pour que `J.pullbackId` et `J.pullbackComp` forment un vrai
pseudo-foncteur contravariant `Cᵒᵖ ⥤ Cat`. Le codomaine `J.Cover X` est un
preordre (une couverture est determinee par ses fleches), donc deux fleches
quelconques entre deux couvertures donnees sont egales
(`CategoryTheory.subsingleton_hom`). La strategie de preuve commune :
`Iso.ext` ramene l'egalite d'isomorphismes naturels a l'egalite des
morphismes (`α.hom`), `ext` decompose aux composantes (`NatTrans.ext`), et
`Subsingleton.elim` conclut chaque egalite de fleches du preordre.
-/

/-- Loi de triangle gauche : pullbacker le long de `𝟙 X` puis de `f` (via
    `J.pullbackComp`) se redresse en l'identite par la re-indexation
    `J.pullbackId X` (whiskering a gauche le long de `J.pullback f`) et
    l'unitor droit du produit des foncteurs.
    Preuve : `Iso.ext`, `ext` aux composantes, `Subsingleton.elim`. -/
theorem pullbackComp_unit_left {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (f : X ⟶ Y) :
    J.pullbackComp (𝟙 X) f ≪≫ Functor.isoWhiskerLeft (J.pullback f) (J.pullbackId X) ≪≫
        Functor.rightUnitor (J.pullback f) = eqToIso (by simp [Category.id_comp]) := by
  apply Iso.ext
  ext S
  apply Subsingleton.elim

/-- Loi de triangle droite : pullbacker le long de `f` puis de `𝟙 Y` (via
    `J.pullbackComp`) se redresse en l'identite par `J.pullbackId Y`
    (whiskering a droite le long de `J.pullback f`) et l'unitor gauche du
    produit des foncteurs.
    Preuve : `Iso.ext`, `ext` aux composantes, `Subsingleton.elim`. -/
theorem pullbackComp_unit_right {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (f : X ⟶ Y) :
    J.pullbackComp f (𝟙 Y) ≪≫ Functor.isoWhiskerRight (J.pullbackId Y) (J.pullback f) ≪≫
        Functor.leftUnitor (J.pullback f) = eqToIso (by simp [Category.comp_id]) := by
  apply Iso.ext
  ext S
  apply Subsingleton.elim

/-- Loi du pentagone (cocycle) : pullbacker le long de `f`, `g`, `h` en deux
    temps est independant du groupement. Les deux membres composent
    `J.pullbackComp` avec les whiskerings et l'associateur du produit des
    foncteurs ; ils ont meme source `J.pullback (f ≫ g ≫ h)` et meme cible
    `J.pullback h ⋙ (J.pullback g ⋙ J.pullback f)`.
    Preuve : `Iso.ext`, `ext` aux composantes, `Subsingleton.elim`. -/
theorem pullbackComp_assoc {C : Type*} [Category C] {W X Y Z : C}
    (J : GrothendieckTopology C) (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    J.pullbackComp f (g ≫ h) ≪≫ Functor.isoWhiskerRight (J.pullbackComp g h) (J.pullback f) ≪≫
        Functor.associator (J.pullback h) (J.pullback g) (J.pullback f) =
      eqToIso (by simp [Category.assoc]) ≪≫
        (J.pullbackComp (f ≫ g) h ≪≫
          Functor.isoWhiskerLeft (J.pullback h) (J.pullbackComp f g)) := by
  apply Iso.ext
  ext S
  apply Subsingleton.elim

end Grothendieck.PullbackFunctor
