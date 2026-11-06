/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 58 : Le classifieur de sous-objets — Ω, le préfaisceau des cribles

Alexandre Grothendieck (1928-2014).

Extension de #2159 (EPIC #1646).

Les parties 1-44 ont établi le socle : catégories, cribles, topologies, lois
de treillis (`SieveLattice`), identités de pullback/pushforward, faisceaux,
faisceautisation, cohomologie. Les parties 45-57 ont systématisé la forme
flèche de la couverture pour une collection croissante de topologies nommées.

Cette partie franchit un seuil : elle exhibe le **classifieur de sous-objets**
du topos des préfaisceaux et du topos des faisceaux — le constituant qui, avec
la clôture cartésienne et les limites finies, définit un **topos élémentaire**
(Lawvere–Tierney). La révélation grothendieckienne est que ce classifieur
n'est pas une construction abstraite : Ω est littéralement **le préfaisceau des
cribles** `Functor.sieves`, l'objet que toute la Partie 6 (`SieveLattice`) a
equipé d'un treillis complet (`pullback_imap`, `pullback_iinf`,
`pushforward_imap`…). Les lois de treillis de la Partie 6 sont la structure
interne de Ω ; la Partie 58 referme la boucle en montrant que ce même objet
classe les sous-préfaisceaux.

Constructions clés pontées depuis Mathlib (`CategoryTheory.Topos.Sheaf`) :

  - `Functor.sieves C`        : le préfaisceau `X ↦ Sieve X` — c'est Ω
  - `Presheaf.truth C`        : le morphisme « vrai » `1 ⟶ Ω`, qui choisit `⊤`
  - `Presheaf.χ m`            : la caractéristique d'un mono `m : F ⟶ G`
  - `Presheaf.classifier C`   : le classifieur `Subobject.Classifier` des préfaisceaux
  - `Sheaf.Ω J`               : le faisceau des cribles **J-clos**
  - `Sheaf.classifier J`      : le classifieur du topos des faisceaux
  - instances `HasSubobjectClassifier (Cᵒᵖ ⥤ Type w)` et `HasSubobjectClassifier (Sheaf J (Type w))`

La topologie entre par la porte des cribles clos : pour un mono `m` entre
faisceaux, les valeurs de `χ m` sont des cribles **J-clos**
(`GrothendieckTopology.isClosed_χ_app_apply_of_isSheaf_of_isSeparated`),
et c'est cette fermeture qui permet de faire descendre Ω des préfaisceaux
aux faisceaux.

Tous les `sorry`s éliminés à la création.

### Note d'accessibilité (Epics #1452/#1453)

Ce module expose **12 vérifications `#check`** et **4 théorèmes propres**,
organisés en 5 sections : (1) Ω est le préfaisceau des cribles ; (2) le
morphisme vrai et la caractéristique χ ; (3) le classifieur des préfaisceaux ;
(4) la topologie filtre Ω — cribles clos ; (5) le classifieur des faisceaux.

### Convention i18n (EPIC #4980 ratifiée par user 2026-07-04)

Ce module est jumelé avec sa version anglaise canonique dans le fichier sibling
`Classifier_en.lean` (modèle sibling pair). Namespace suffixé `_en` (anti-
collision). Les `#check`, signatures, variables et univers sont byte-identiques
entre les deux fichiers ; seules les docstrings et commentaires diffèrent.
-/

import Mathlib.CategoryTheory.Topos.Sheaf

universe u v w

namespace Grothendieck.Classifier

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-!
## Section 1 : Ω est le préfaisceau des cribles

Le classifieur de sous-objets d'une catégorie de préfaisceaux vit dans la
catégorie elle-même : c'est `Functor.sieves C`, l'objet `X ↦ Sieve X`. Chaque
composante de Ω est le treillis complet des cribles sur `X` — l'objet que la
Partie 6 (`SieveLattice`) a parcouru de long en large. La fonctorialité
(`sieves_map`) tire un crible en arrière le long d'une flèche : c'est le
`Sieve.pullback` de la Partie 6, qui préserve ⊥, ⊤, ⊔, ⊓, `iSup` et `iInf`.
-/

-- CALIBRATION : le préfaisceau des cribles, composante par composante.
#check @CategoryTheory.Functor.sieves          -- Cᵒᵖ ⥤ Type (max u v), X ↦ Sieve X.unop
#check @CategoryTheory.Functor.sieves_map       -- la fonctorialité est le pullback de cribles

/-!
## Section 2 : Le morphisme vrai et la caractéristique χ

Le morphisme `truth : 1 ⟶ Ω` est la flèche « vrai » : en chaque composante,
il choisit le crible maximal `⊤`. La caractéristique `χ m` d'un mono `m : F ⟶ G`
envoie un élément `x : G(X)` sur le crible des flèches `f : Y ⟶ X` le long
desquelles `x` remonte dans `F` : `f ∈ χ m x` ssi `∃ a, G(f)(x) = m(a)`.
-/

-- CALIBRATION : le morphisme vrai choisit le crible maximal.
#check @CategoryTheory.Presheaf.truth           -- (const PUnit) ⟶ sieves C
#check @CategoryTheory.Presheaf.χ               -- (m : F ⟶ G) : G ⟶ sieves C

variable {F G : Cᵒᵖ ⥤ Type (max u v)} (m : F ⟶ G) (X : Cᵒᵖ) (x : G.obj X)

/-- VRAI (rfl) : le morphisme vrai choisit exactement le crible maximal.
    La composante en `X` est constante de valeur `⊤`. -/
theorem truth_picks_top (X : Cᵒᵖ)
    (b : ((Functor.const Cᵒᵖ).obj PUnit).obj X) :
    (Presheaf.truth C).app X b = (⊤ : Sieve X.unop) := rfl

/-- PONT : l'appartenance dans la caractéristique se lit sur la définition —
    `f` appartient au crible `χ m x` exactement quand `x` remonte dans `F`
    le long de `f`. C'est la lecture membre à membre du classifieur. -/
theorem chi_app_mem_iff {Y : C} (f : Y ⟶ X.unop) :
    Sieve.arrows ((Presheaf.χ m).app X x) f ↔
      ∃ a : F.obj (Opposite.op Y), G.map f.op x = m.app (Opposite.op Y) a := Iff.rfl

/-- PROPRE : la caractéristique est descendante — si `x` remonte le long de
    `f`, il remonte le long de toute précomposition `g ≫ f`. C'est la
    stabilité par tirage arrière qui fait de `χ m x` un crible (et non une
    simple partie de flèches) : la même preuve que Mathlib intègre dans la
    définition de `χ`, exposée ici comme loi nommée. -/
theorem chi_app_downward_closed {Y Z : C} (f : Y ⟶ X.unop) (g : Z ⟶ Y)
    (hf : Sieve.arrows ((Presheaf.χ m).app X x) f) :
    Sieve.arrows ((Presheaf.χ m).app X x) (g ≫ f) := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨F.map g.op a, ?_⟩
  simp [ha, NatTrans.naturality_apply]

/-- PROPRE : un élément défini dans `F` a une caractéristique maximale —
    si `x = m(a)` est dans l'image directe, alors `χ m x = ⊤` : le crible des
    flèches le long desquelles `x` remonte est tout le crible maximal. -/
theorem chi_app_eq_top_of_app (a : F.obj X) (h : m.app X a = x) :
    (Presheaf.χ m).app X x = (⊤ : Sieve X.unop) := by
  refine Sieve.ext fun Y f => ?_
  constructor
  · intro _
    exact Sieve.top_apply f
  · intro _
    refine ⟨F.map f.op a, ?_⟩
    rw [← h]
    exact (NatTrans.naturality_apply m f.op a).symm

/-!
## Section 3 : Le classifieur des préfaisceaux

`Presheaf.classifier C` empaquette Ω, `truth` et χ en un
`Subobject.Classifier` : chaque mono `m` possède exactement une flèche
caractéristique (l'universalité `χ_unique`), et le carré de `m`, du terminal,
de `truth` et de `χ m` est pullback. Sur un site essentiellement petit,
l'instance `HasSubobjectClassifier` est disponible d'office.
-/

-- CALIBRATION : l'empaquetage classifieur des préfaisceaux.
#check @CategoryTheory.Presheaf.classifier      -- Subobject.Classifier (Cᵒᵖ ⥤ Type (max u v))
#check @CategoryTheory.Presheaf.comp_χ_eq
#check @CategoryTheory.Presheaf.isPullback_χ_truth
#check @CategoryTheory.Presheaf.χ_unique

variable [EssentiallySmall.{w} C]

/-- CALIBRATION : l'instance de classifieur pour les préfaisceaux de types. -/
example : HasSubobjectClassifier (Cᵒᵖ ⥤ Type w) := inferInstance

variable (J : GrothendieckTopology C)

/-!
## Section 4 : La topologie filtre Ω — les cribles clos

Une topologie de Grothendieck `J` découpe dans Ω son sous-faisceau des
cribles **J-clos** (`Functor.closedSieves`). Le pont clé : pour un mono `m`
entre faisceaux, chaque valeur `(χ m) x` est un crible J-clos — c'est
exactement ce qui autorise `χ` à atterrir dans les cribles clos et donc à
descendre au niveau faisceaux.
-/

-- CALIBRATION : le sous-foncteur des cribles J-clos.
#check @CategoryTheory.Functor.closedSieves     -- sous-foncteur de sieves, cribles J-clos
#check @CategoryTheory.GrothendieckTopology.IsClosed

-- CALIBRATION (le pont topologie ↔ classifieur) : la caractéristique d'un
-- mono entre faisceaux prend des valeurs J-closes.
#check @CategoryTheory.GrothendieckTopology.isClosed_χ_app_apply_of_isSheaf_of_isSeparated

/-!
## Section 5 : Le classifieur des faisceaux

Au niveau faisceaux, Ω devient le faisceau des cribles clos `Sheaf.Ω J`,
`truth` choisit toujours `⊤` (le crible maximal est clos), et la
caractéristique d'un mono de faisceaux est la même qu'au niveau préfaisceaux
— restreinte aux cribles clos. Sur un site essentiellement petit, le topos
des faisceaux d'ensembles possède donc un classifieur de sous-objets : avec
la clôture cartésienne et les limites finies, c'est un **topos élémentaire**
(Lawvere–Tierney). Mathlib énonce cette conséquence en prose ; l'instance
`ElementaryTopos` elle-même n'est pas encore disponible dans cette révision
de Mathlib — la frontière reste honnête, comme la carte de la Partie 4.
-/

-- CALIBRATION : le faisceau des cribles clos et le classifieur des faisceaux.
#check @CategoryTheory.Sheaf.Ω                  -- Sheaf J (Type (max u v)), cribles J-clos
#check @CategoryTheory.Sheaf.truth               -- terminal ⟶ Ω, choisit ⊤ (clos)
#check @CategoryTheory.Sheaf.classifier          -- Subobject.Classifier (Sheaf J (Type (max u v)))

/-- CALIBRATION : l'instance de classifieur pour le topos des faisceaux. -/
example : HasSubobjectClassifier (Sheaf J (Type w)) := inferInstance

end Grothendieck.Classifier
