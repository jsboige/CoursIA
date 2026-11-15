/-
Grothendieck Partie 32 — Catégories monoïdales

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

universe v u u₁ u₂ v₁ v₂

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

/-!
## 8. Théorèmes propres (c.1301+107)

Identités fondamentales des structures monoïdales, prouvées localement
via la tactique `rw` sur les lemmes canoniques Mathlib (les isomorphismes
`α_`, `λ_`, `ρ_` sont des champs de `MonoidalCategoryStruct` ; leurs
égalités sont déf. valides via `.hom` / `.inv`).

Leçon L902 ★★ : `rfl` est prouvable quand l'égalité est définitionnelle.
Les isomorphismes canoniques `(α_ X Y Z).hom` etc. sont des champs ;
les lemmes les pontants sont des `(rfl)` ou `by rw [name]` selon le
niveau de unfold requis.
-/

/-- Théorème : l'associateur `(X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)` est défini
    comme `(α_ X Y Z).hom` au niveau du morphisme. C'est la définition
    même de l'associateur dans Mathlib 4 comme champ de
    `MonoidalCategoryStruct`. -/
theorem associator_iso_hom_eq [MonoidalCategoryStruct C] (X Y Z : C) :
    (α_ X Y Z).hom = (MonoidalCategoryStruct.associator X Y Z).hom := rfl

/-- Théorème : l'unitaire à gauche `λ_ X : 𝟙_ C ⊗ X ≅ X` est défini
    implicitement par le cham `leftUnitor` de `MonoidalCategoryStruct`.
    Au niveau de `Iso.hom`, c'est une construction définitionnelle. -/
theorem left_unitor_iso_hom_eq [MonoidalCategoryStruct C] (X : C) :
    (λ_ X).hom = (MonoidalCategoryStruct.leftUnitor X).hom := rfl

/-- Théorème : l'unitaire à droite `ρ_ X : X ⊗ 𝟙_ C ≅ X` est défini
    par le champ `rightUnitor` de `MonoidalCategoryStruct`. -/
theorem right_unitor_iso_hom_eq [MonoidalCategoryStruct C] (X : C) :
    (ρ_ X).hom = (MonoidalCategoryStruct.rightUnitor X).hom := rfl

/-- Théorème : le tenseur d'objets `tensorObj X Y = X ⊗ Y` est
    définitionnellement égal à l'application du champ `tensorObj` de
    `MonoidalCategoryStruct`. Pont observa entre la notation `⊗` et
    la fonction primitive. -/
theorem tensorObj_eq_app [MonoidalCategoryStruct C] (X Y : C) :
    X ⊗ Y = MonoidalCategoryStruct.tensorObj X Y := rfl

/-!
## 9. Théorèmes propres (c.1301+121 — ajouts sur les fields `whiskerLeft` /
##     `whiskerRight`)

Suite logique directe des 4 lemmes ci-dessus : on prouve maintenant
que les champs `whiskerLeft`, `whiskerRight` de
`MonoidalCategoryStruct` sont reliés définitionnellement à leurs
notations Lean `◁`, `▷`. Ces égalités sont des unfolds triviaux
après `rfl` ; L902 ★★ n'est pas concernée (pas de polymorphic
universe constructor : `MonoidalCategoryStruct` est une classe de
type `Type → Type`).

**Note** : un lemme analogue sur `tensorHom f g` est SKIPPED — la
notation `f ▷ g` utilise `whiskerRight` (morphisme `f`, objet `g`)
mais pas `tensorHom` (qui prend morphisme `f` ET morphisme `g`).
Un lemme `tensorHom_eq_app` analogue pourrait être ajouté dans
une PR ultérieure si une notation infixe `f ⊗ g` pour morphismes
est étendue à Mathlib.

**Origine** (issue #2159 dispatch ai-01, c.1301+121) : même scope que
les ajouts `Equivalences.lean`. Sous-grain microscopique 2/2.
-/

/-- Théorème : le whiskering gauche `whiskerLeft X f = X ◁ f`
    est définitionnellement égal au champ `whiskerLeft` de
    `MonoidalCategoryStruct`. Pont entre la notation `◁` et la
    fonction primitive. -/
theorem whiskerLeft_eq_app [MonoidalCategoryStruct C] {X Y Z : C}
    (f : Y ⟶ Z) :
    X ◁ f = MonoidalCategoryStruct.whiskerLeft X f := rfl

/-- Théorème : le whiskering droit `whiskerRight f Z = f ▷ Z`
    est définitionnellement égal au champ `whiskerRight` de
    `MonoidalCategoryStruct`. Pont entre la notation `▷` (avec
    argument objet) et la fonction primitive. -/
theorem whiskerRight_eq_app [MonoidalCategoryStruct C] {X Y Z : C}
    (f : X ⟶ Y) :
    f ▷ Z = MonoidalCategoryStruct.whiskerRight f Z := rfl

/-!
## 10. Ponts sur la cohérence (pentagone + triangle) et les exemples canoniques

Les **deux axiomes de cohérence** exigés par la classe `MonoidalCategory`
— le pentagone `Pentagon` (cohérence de l'associativité) et l'identité
triangulaire `triangle_assoc_comp_right` (cohérence unité-associateur)
— sont les `Prop` de la section 3. Le pont `pentagon_field` expose la
définition du pentagone comme type ; le pont `triangle_field` prouve
l'identité triangulaire par appel direct au lemme Mathlib. Les
**exemples canoniques** des sections 4-6 complètent le tableau : le
produit de deux catégories monoïdales (`prod_monoidal_field`), la
classe symétrique (`symmetric_category_field`) et la catégorification
minimale d'un monoïde (`discrete_monoidal_field`).

Le pont `prod_monoidal_field` requiert deux univers distincts `u₁ u₂`
(les univers des objets de `C₁` et `C₂`), déclarés au scope module —
L902 ★★ reste satisfaite (args résidents `(C₁ : Type u₁)` /
`(C₂ : Type u₂)`, instances `Category`/`MonoidalCategory` structurelles).
-/

/-- Pont : le diagramme du pentagone de Mac Lane — la cohérence de
    l'associativité exigée par la classe `MonoidalCategory`. Pour quatre
    objets `Y₁ Y₂ Y₃ Y₄`, les deux chemins de réassociation
    `((Y₁ ⊗ Y₂) ⊗ Y₃) ⊗ Y₄` et `Y₁ ⊗ (Y₂ ⊗ (Y₃ ⊗ Y₄))` coïncident.
    Re-export direct de la def Mathlib `MonoidalCategory.Pentagon`.
    Type-sig bridge (L902 ★★ Tier 5) — re-export direct de la def Prop. -/
def pentagon_field [MonoidalCategoryStruct C] (Y₁ Y₂ Y₃ Y₄ : C) : Prop :=
  MonoidalCategory.Pentagon Y₁ Y₂ Y₃ Y₄

/-- Pont : l'identité triangulaire de la catégorie monoïdale — la
    compatibilité entre l'associateur et les unitaires :
    `(α_ X (𝟙_ C) Y).inv ≫ ((ρ_ X).hom ▷ Y) = X ◁ (λ_ Y).hom`.
    C'est la version « associateur-inverse + unitaire droit » du
    triangle de Mac Lane. Délègue directement au lemme Mathlib
    `MonoidalCategory.triangle_assoc_comp_right`.
    Lemma call direct (L902 ★★ Tier 5) — args résidents `(X Y : C)`. -/
theorem triangle_field [MonoidalCategory C] (X Y : C) :
    (α_ X (𝟙_ C) Y).inv ≫ ((ρ_ X).hom ▷ Y) = X ◁ (λ_ Y).hom :=
  MonoidalCategory.triangle_assoc_comp_right X Y

/-- Pont : le produit de deux catégories monoïdales — l'instance
    canonique `MonoidalCategory (C₁ × C₂)` : le tenseur et l'unité se
    calculent composante par composante. Re-export direct de l'instance
    Mathlib `MonoidalCategory.prodMonoidal`.
    Type retour `MonoidalCategory` = classe data → `noncomputable def`
    (leçon c.1301+131-L2 ★). Args : `(C₁ : Type u₁)` `(C₂ : Type u₂)`
    — univers distincts déclarés au scope module. -/
@[reducible]
noncomputable def prod_monoidal_field (C₁ : Type u₁) [Category.{v₁} C₁]
    [MonoidalCategory.{v₁} C₁] (C₂ : Type u₂) [Category.{v₂} C₂]
    [MonoidalCategory.{v₂} C₂] : MonoidalCategory (C₁ × C₂) :=
  MonoidalCategory.prodMonoidal C₁ C₂

/-- Pont : la classe `SymmetricCategory` — une catégorie monoïdale
    tressée dont le tressage est involutif (`β_ X Y ≫ β_ Y X = 𝟙`).
    C'est la structure « symétrique » de la section 5, cadre des
    produits tensoriels de faisceaux. Re-export direct de la classe
    Mathlib `CategoryTheory.SymmetricCategory`.
    Type-sig bridge (L902 ★★ Tier 5) — re-export direct de la classe. -/
def symmetric_category_field (C : Type u) [Category.{v} C]
    [MonoidalCategory.{v} C] : Type _ :=
  CategoryTheory.SymmetricCategory C

/-- Pont : la catégorification minimale d'un monoïde — l'instance
    canonique `MonoidalCategory (Discrete M)` : les objets sont les
    éléments de `M`, le tenseur est la multiplication, l'unité est `1`.
    C'est le lien « monoïde → catégorie monoïdale » de la section 6.
    Re-export direct de l'instance Mathlib `Discrete.monoidal`.
    Type retour `MonoidalCategory` = classe data → `noncomputable def`
    (leçon c.1301+131-L2 ★). -/
@[reducible]
noncomputable def discrete_monoidal_field (M : Type u) [Monoid M] :
    MonoidalCategory (Discrete M) :=
  CategoryTheory.Discrete.monoidal M

end Grothendieck.MonoidalCategories
