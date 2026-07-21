/-
Grothendieck Partie 29 — Catégories monoïdales

Alexander Grothendieck (1928-2014).

Extension Phase 2+ (#2159, Epic #1646).

Une **catégorie monoïdale** est l'analogue catégorifié d'un monoïde : un
monoïde est la donnée d'un ensemble `M`, d'une multiplication
`M × M → M` et d'un élément unité `e ∈ M` satisfaisant l'associativité et
l'unité ; une catégorie monoïdale est la donnée d'une catégorie `C`, d'un
**foncteur tensoriel** `⊗ : C × C ⥤ C` et d'un **objet unité** `𝟙_ C`,
munis de contraintes de cohérence (l'associateur `α_` et les unitaires
`λ_`, `ρ_`) qui ne sont des isomorphismes — pas des égalités — parce que,
en général, `(X ⊗ Y) ⊗ Z` et `X ⊗ (Y ⊗ Z)` ne sont pas *égaux* mais
*canoniquement isomorphes*.

Grothendieck utilise constamment les structures monoïdales : le produit
tensoriel de faisceaux, les catégories monoïdales symétriques sous-jacentes
aux catégories dérivées, les sites monoïdaux. Plus profondément, la théorie
des faisceaux repose sur une catégorie monoïdale (produit cartésien ou
tensoriel) qui rend possibles les opérations internes (Hom faisceautique,
⊗ de faisceaux). Le théorème de cohérence de Mac Lane (tout diagramme
bien typé d'associateurs et d'unitaires commute) garantit que l'on peut
manipuler les parenthèses « comme si » l'associativité était stricte.

La définition se décompose en deux temps :
  - `MonoidalCategoryStruct C` — la **donnée** brute (tensorObj, tensorUnit,
    whiskerLeft, whiskerRight, tensorHom, associator, leftUnitor,
    rightUnitor) ;
  - `MonoidalCategory C` — la **propriété de cohérence** : le pentagone de
    Mac Lane et le triangle de cohérence unité/associativité commutent.

Mathlib 4 formalise toute cette infrastructure dans
`Mathlib.CategoryTheory.Monoidal.Category` :
  - `MonoidalCategoryStruct C` — la structure (avec notations `⊗`, `𝟙_`,
    `◁`, `▷`, `α_`, `λ_`, `ρ_`)
  - `MonoidalCategory C` — la structure cohérente (étend la précédente +
    axiomes de pentagone/triangle)
  - `Pentagon` / lemmas `triangle_*` — les diagrammes de cohérence
  - `BraidedCategory C` / `SymmetricCategory C` — tressage et symétrie
    (dans `Mathlib.CategoryTheory.Monoidal.Braided`)
  - `instance prodMonoidal` — toute paire de catégories monoïdales est
    monoïdale (produit terme à terme)

Ce module ré-expose ces faits comme un parcours pédagogique organisé, pour
des apprenants découvrant les catégories monoïdales pour la première fois,
en miroir des modules `Grothendieck.YonedaLemma` (la catégorie des
préfaisceaux `(Cᵒᵖ ⥤ Type*)` est monoïdale cartésienne) et
`Grothendieck.Adjunction` (une adjonction monoïdale est la donnée de deux
foncteurs monoïdaux adjoints). Les catégories monoïdales fondent aussi les
modules à venir sur les catégories fermées (CCC) et les topos élémentaires.

Epic #1646, See #2159. Tous les `sorry` éliminés à la création.

### i18n — convention #4980 ratifiée 2026-07-04

Ce module est jumelé avec sa version anglaise canonique dans le fichier
sibling `Monoidal_en.lean`. Les énoncés de théorèmes/lemmes, les tactiques
Lean et les références Mathlib restent en anglais. Seules les
**docstrings `/-- ... -/`** et les **commentaires `-- ...`** diffèrent entre
les deux fichiers. Anti-§D byte-identity garanti.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Discrete

universe v u

namespace Grothendieck.MonoidalCategories

open CategoryTheory
open scoped MonoidalCategory

variable {C : Type u} [Category.{v} C]

/-!
## 1. Le problème : catéifier la structure monoïdale

Un monoïde `(M, ·, e)` est un ensemble `M`, une multiplication `· : M × M → M`
et une unité `e ∈ M` tels que `(x · y) · z = x · (y · z)` et `e · x = x = x · e`.
Pour « catéifier » cette notion, on remplace :
  - l'ensemble `M` par une catégorie `C` ;
  - la multiplication `·` par un **foncteur tensoriel** `⊗ : C × C ⥤ C` ;
  - l'égalité d'objets `(X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z)` par un **isomorphisme**
    canonique `α_ X Y Z : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)` (l'associateur).
L'associativité n'est plus stricte mais « upto coherent isomorphism ». Les
contraintes de cohérence (pentagone, triangle) garantissent qu'aucune
ambiguïté ne subsiste.
-/

-- Le foncteur tensoriel : objets. `tensorObj X Y = X ⊗ Y`.
#check @MonoidalCategoryStruct.tensorObj

-- L'objet unité de la catégorie monoïdale. Notation `𝟙_ C`.
#check @MonoidalCategoryStruct.tensorUnit

-- Le produit tensoriel de morphismes (via whiskerings gauche/droit).
#check @MonoidalCategoryStruct.tensorHom

-- Whiskering à gauche : `X ◁ f : X ⊗ Y₁ ⟶ X ⊗ Y₂`.
#check @MonoidalCategoryStruct.whiskerLeft

-- Whiskering à droite : `f ▷ Y : X₁ ⊗ Y ⟶ X₂ ⊗ Y`.
#check @MonoidalCategoryStruct.whiskerRight

/-!
## 2. La structure : MonoidalCategoryStruct

`MonoidalCategoryStruct C` regroupe la **donnée** brute d'une structure
monoïdale sur `C` : le produit tensoriel `⊗` (sur objets et morphismes),
l'unité `𝟙_ C`, l'associateur `α_`, et les unitaires gauche/droit `λ_`, `ρ_`.
À ce stade, **aucune cohérence** n'est exigée — seulement l'existence des
données. Les isomorphismes `α_`, `λ_`, `ρ_` témoignent que le produit est
associatif et unital «upto iso».
-/

-- L'associateur : `(X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`. Notation `α_`.
#check @MonoidalCategoryStruct.associator

-- L'unitaire à gauche : `𝟙_ C ⊗ X ≅ X`. Notation `λ_`.
#check @MonoidalCategoryStruct.leftUnitor

-- L'unitaire à droite : `X ⊗ 𝟙_ C ≅ X`. Notation `ρ_`.
#check @MonoidalCategoryStruct.rightUnitor

-- La classe regroupant toutes ces données (sans cohérence).
#check @MonoidalCategoryStruct

/-!
## 3. La cohérence : MonoidalCategory (pentagone + triangle)

`MonoidalCategory C` étend `MonoidalCategoryStruct C` en exigeant que les
deux diagrammes de cohérence de Mac Lane commutent :
  - le **pentagone** : les deux façons de réassocier `(W ⊗ X) ⊗ Y ⊗ Z`
    en `W ⊗ (X ⊗ (Y ⊗ Z))` via `α_` coïncident ;
  - le **triangle** : l'unité et l'associativité interagissent cohéremment
    (`(X ⊗ 𝟙_) Y` se simplifie via `α_` et `ρ_`).
Le **théorème de cohérence de Mac Lane** assure alors que *tout* diagramme
bien typé construit à partir de `α_`, `λ_`, `ρ_` commute — on peut donc
manipuler les parenthèses comme si la structure était strictement
associative. C'est ce qui rend la théorie praticable.
-/

-- La classe des catégories monoïdales cohérentes (pentagone + triangle).
#check @MonoidalCategory

-- Le diagramme du pentagone (cohérence d'associativité) — un `Prop`.
#check @MonoidalCategory.Pentagon

-- Un lemme-témoin du triangle : `α_` et `ρ_` interagissent cohéremment.
#check @MonoidalCategory.triangle_assoc_comp_right

/-!
## 4. Exemples canoniques

Toute catégorie à produits finis est monoïdale (le produit cartésien `×`
joue le rôle de `⊗`, l'objet terminal joue le rôle de `𝟙_`). Mathlib fournit
aussi l'instance générale : le produit de deux catégories monoïdales est
monoïdal (`prodMonoidal`). La catégorie `Type*` est monoïdale cartésienne
(produit `×`) et aussi monoïdale pour le produit tensoriel des types.
-/

-- Le produit de deux catégories monoïdales est monoïdal.
#check @MonoidalCategory.prodMonoidal

/-!
## 5. Tressage et symétrie : BraidedCategory / SymmetricCategory

Une catégorie monoïdale **tressée** est munie d'un isomorphisme naturel
`braiding : X ⊗ Y ≅ Y ⊗ X` (le « tressage ») satisfaisant les équations
de tressage de Yang-Baxter (hexagones). Une catégorie **symétrique** est un
tressage tel que `braiding ∘ braiding = id` (involutive). C'est le cadre
naturel des produits tensoriels de faisceaux et des catégories dérivées.
-/

-- La classe des catégories monoïdales tressées.
#check @BraidedCategory

-- Le tressage `X ⊗ Y ≅ Y ⊗ X`.
#check @BraidedCategory.braiding

-- La classe des catégories monoïdales symétriques (tressage involutif).
#check @SymmetricCategory

/-!
## 6. Lien vers la suite : catégories fermées, CCC, topos

Une catégorie monoïdale **fermée** possède un « Hom interne » `ihom` tel que
`ihom X ⟶ Y` représente le foncteur `X ⊗ (-)`. Le cas cartésien (produit `×`)
donne les **catégories cartésiennes fermées** (CCC) — le cadre de la
correspondance de Curry-Howard-Lambek (logique ↔ types ↔ catégories). Un
**topos élémentaire** est une CCC avec un classifiant de sous-objets `Ω` :
c'est l'axiomatisation purement catégorique de la théorie des ensembles et
des faisceaux. Les catégories monoïdales en sont le socle.
-/

-- Un monoïde `M` donne une catégorie monoïdale `Discrete M` (catégorification minimale).
#check @Discrete.monoidal

-- Un morphisme de monoïdes `M →* N` donne un foncteur monoïdal `Discrete M ⥤ Discrete N`.
#check @Discrete.monoidalFunctor

/-!
## 7. Théorèmes ponts

Reformulations dans l'espace de noms du projet, pontant les faits Mathlib.
-/

/-- Pont : le produit tensoriel de deux objets, exposé comme fonction nue.
    C'est `X ⊗ Y` dans toute catégorie monoïdale. -/
noncomputable def tensor_product [MonoidalCategory C] (X Y : C) : C :=
  X ⊗ Y

/-- Pont : l'objet unité de la catégorie monoïdale, exposé comme objet nu.
    C'est `𝟙_ C`, neutre pour `⊗` upto iso (`λ_`, `ρ_`). -/
noncomputable def tensor_unit_obj [MonoidalCategory C] : C :=
  𝟙_ C

/-- Pont : l'associateur `(X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`, exposé comme
    isomorphisme nu. Témoin que le produit tensoriel est associatif
    «upto coherent isomorphism» — la donnée brute, avant la cohérence. -/
noncomputable def associator_iso [MonoidalCategory C] (X Y Z : C) :
    (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z) :=
  α_ X Y Z

/-- Pont : l'unitaire à gauche `𝟙_ C ⊗ X ≅ X`. -/
noncomputable def left_unitor_iso [MonoidalCategory C] (X : C) :
    𝟙_ C ⊗ X ≅ X :=
  λ_ X

/-- Pont : l'unitaire à droite `X ⊗ 𝟙_ C ≅ X`. -/
noncomputable def right_unitor_iso [MonoidalCategory C] (X : C) :
    X ⊗ 𝟙_ C ≅ X :=
  ρ_ X

/-- Pont : le tressage `X ⊗ Y ≅ Y ⊗ X` dans une catégorie monoïdale tressée.
    Témoin de la commutativité «upto iso» du produit tensoriel. -/
noncomputable def braiding_iso [MonoidalCategory C] [BraidedCategory C]
    (X Y : C) : X ⊗ Y ≅ Y ⊗ X :=
  BraidedCategory.braiding X Y

end Grothendieck.MonoidalCategories
