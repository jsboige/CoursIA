/-
Grothendieck Partie 27 — Équivalences de catégories

Alexandre Grothendieck (1928-2014).

Extension Phase 2+ (#2159, Epic #1646).

L'équivalence de catégories est la « bonne » notion de sameness en
catégorie : deux catégories équivalentes sont indistinguables du point de
vue de la théorie, même si elles ne sont pas identiques ensembles d'objets.
Grothendieck en fait un usage constant : le théorème de Yoneda dit que
tout foncteur représentable est équivalent à un foncteur de Hom ; la
géométrie algébrique identifie les schémas affines à la catégorie opposée
des anneaux commutatifs (anti-équivalence de catégories) ; les topos sont
définis comme des catégories équivalentes à la catégorie des faisceaux
d'ensembles sur un site ; et toute la théorie des catégories dérivées
repose sur des équivalences de catégories triangulées.

Une **équivalence de catégories** `C ≌ D` est la donnée de deux foncteurs
`functor : C ⥤ D` et `inverse : D ⥤ C`, ainsi que deux isomorphismes
naturels `unitIso : 𝟭 C ≅ functor ⋙ inverse` et
`counitIso : inverse ⋙ functor ≅ 𝟭 D` satisfaisant les identités
triangulaires. C'est l'analogue catégorique d'un isomorphisme, mais « à
isomorphisme près sur les objets » — ce qui est la bonne notion : les
objets n'ont pas de substance intrinsèque en théorie des catégories, seules
les flèches comptent.

Le critère pratique (le plus utilisé) : un foncteur est une équivalence si
et seulement s'il est **pleinement fidèle** (bijecte les Hom) et
**essentiellement surjectif** (tout objet cible est isomorphe à l'image d'un
objet source). Mathlib encode cela dans la classe `Functor.IsEquivalence`.

Mathlib 4 formalise toute cette infrastructure dans
`Mathlib.CategoryTheory.Equivalence` :
  - `CategoryTheory.Equivalence : Type*` — la structure d'équivalence C ≌ D
  - `CategoryTheory.Equivalence.functor` / `inverse` — les deux foncteurs
  - `CategoryTheory.Equivalence.unitIso` / `counitIso` — les isos naturels
  - `CategoryTheory.Equivalence.functor_unitIso_comp` — l'identité triangulaire
  - `CategoryTheory.Equivalence.refl` / `symm` / `trans` — structure de (2-)groupeoïde
  - `CategoryTheory.Functor.FullyFaithful` — le foncteur bijecte les Hom
  - `CategoryTheory.Functor.EssSurj` — essential surjectivity
  - `CategoryTheory.Functor.IsEquivalence` — la propriété d'être une équivalence

Ce module ré-expose ces faits comme un parcours pédagogique organisé, pour
des apprenants découvrant les équivalences pour la première fois, en miroir
des modules `Grothendieck.Adjunction` et `Grothendieck.Limits` (l'adjonction
donne les équivalences « locales » Hom_D(LX,Y) ≃ Hom_C(X,RY) ; l'équivalence
est une adjonction où l'unité et la coïnité sont des isomorphismes).

Epic #1646, See #2159. Tous les `sorry` éliminés à la création.

### i18n — convention #4980 ratifiée 2026-07-04

Ce module est jumelé avec sa version anglaise canonique dans le fichier
sibling `Equivalences_en.lean`. Les énoncés de théorèmes, les noms de lemmes,
les tactiques Lean et les références Mathlib restent en anglais. Seules les
**docstrings `/-- ... -/`** et les **commentaires `-- ...`** diffèrent entre
les deux fichiers. Anti-§D byte-identity garanti.
-/

import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.FullyFaithful

universe v₁ v₂ u₁ u₂

namespace Grothendieck.Equivalences

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-!
## 1. La structure d'équivalence

Une équivalence `e : C ≌ D` est la donnée d'un foncteur `e.functor : C ⥤ D`,
d'un inverse `e.inverse : D ⥤ C`, et de deux isomorphismes naturels
`e.unitIso : 𝟭 C ≅ e.functor ⋙ e.inverse` et
`e.counitIso : e.inverse ⋙ e.functor ≅ 𝟭 D`. La notation `C ≌ D` dénote
`Equivalence C D`.
-/

-- La structure d'équivalence de catégories C ≌ D.
#check @CategoryTheory.Equivalence

-- Le foncteur « aller » e.functor : C ⥤ D de l'équivalence.
#check @CategoryTheory.Equivalence.functor

-- Le foncteur « retour » e.inverse : D ⥤ C de l'équivalence.
#check @CategoryTheory.Equivalence.inverse

/-!
## 2. Unité et coïnité, identités triangulaires

Comme pour une adjonction (cf `Grothendieck.Adjunction`), une équivalence
détermine une unité `unitIso : 𝟭 C ≅ functor ⋙ inverse` et une coïnité
`counitIso : inverse ⋙ functor ≅ 𝟭 D` — mais ce sont ici des **isomorphismes
naturels** (pas de simples transformations naturelles). C'est précisément ce
qui distingue une équivalence d'une adjonction quelconque : l'unité et la
coïnité sont inversibles.
-/

-- L'isomorphisme naturel unité 𝟭 C ≅ functor ⋙ inverse.
#check @CategoryTheory.Equivalence.unitIso

-- L'isomorphisme naturel coïnité inverse ⋙ functor ≅ 𝟭 D.
#check @CategoryTheory.Equivalence.counitIso

-- La première identité triangulaire (compatibilité unité × coïnité).
#check @CategoryTheory.Equivalence.functor_unitIso_comp

/-!
## 3. La (2-)catégorie des catégories : refl, symm, trans

Les équivalences de catégories se composent et s'inversent : elles forment
une structure de (2-)groupeoïde. `Equivalence.refl` est l'équivalence
identité, `Equivalence.symm` inverse une équivalence (échange functor ↔
inverse), et `Equivalence.trans` compose deux équivalences.
-/

-- L'équivalence identité C ≌ C.
#check @CategoryTheory.Equivalence.refl

-- L'inverse d'une équivalence : si C ≌ D alors D ≌ C.
#check @CategoryTheory.Equivalence.symm

-- La composition de deux équivalences : C ≌ D et D ≌ E donne C ≌ E.
#check @CategoryTheory.Equivalence.trans

/-!
## 4. Le critère pratique : pleinement fidèle + essentiellement surjectif

Le critère le plus utilisé en pratique : un foncteur `F : C ⥤ D` est une
équivalence si et seulement s'il est **pleinement fidèle** (pour tous
`X Y : C`, l'application `Hom_C(X,Y) → Hom_D(FX,FY)` est bijective) et
**essentiellement surjectif** (tout objet de `D` est isomorphe à l'image
d'un objet de `C`). Mathlib encode cela dans la classe `Functor.IsEquivalence`.
-/

-- La structure témoignant qu'un foncteur est pleinement fidèle (bijecte les Hom).
#check @CategoryTheory.Functor.FullyFaithful

-- La classe témoignant qu'un foncteur est essentiellement surjectif.
#check @CategoryTheory.Functor.EssSurj

-- La propriété pour un foncteur d'être une équivalence (plein + fidèle + ess. surj.).
#check @CategoryTheory.Functor.IsEquivalence

/-!
## 5. Théorèmes ponts

Reformulations dans l'espace de noms du projet, pontant les faits Mathlib.
-/

/-- Pont : le foncteur « aller » d'une équivalence C ≌ D, exposé comme
    foncteur nu dans la catégorie des foncteurs. C'est la moitié « directe »
    de l'équivalence, l'autre étant `equivalence_inverse`. -/
noncomputable def equivalence_functor (e : C ≌ D) : C ⥤ D :=
  e.functor

/-- Pont : le foncteur « retour » d'une équivalence C ≌ D. Avec
    `equivalence_functor`, il forme la paire de foncteurs quasi-inverses. -/
noncomputable def equivalence_inverse (e : C ≌ D) : D ⥤ C :=
  e.inverse

/-- Pont : l'isomorphisme naturel unité d'une équivalence — 𝟭 C ≅ functor ⋙
    inverse. C'est le témoignage que « aller puis revenir » est isomorphe à
    l'identité (à isomorphisme près, pas égalité). -/
noncomputable def equivalence_unit (e : C ≌ D) : 𝟭 C ≅ e.functor ⋙ e.inverse :=
  e.unitIso

/-- Pont : l'isomorphisme naturel coïnité d'une équivalence — inverse ⋙
    functor ≅ 𝟭 D. C'est le témoignage dual que « revenir puis aller » est
    isomorphe à l'identité. -/
noncomputable def equivalence_counit (e : C ≌ D) : e.inverse ⋙ e.functor ≅ 𝟭 D :=
  e.counitIso

/-- Pont : l'équivalence symétrique (inverse) — si C ≌ D alors D ≌ C.
    Échange les rôles de functor et inverse ; l'unité de `e.symm` est la
    coïnité de `e` et réciproquement. -/
noncomputable def equivalence_symm (e : C ≌ D) : D ≌ C :=
  e.symm

/-- Pont : la composition de deux équivalences — C ≌ D et D ≌ E donne C ≌ E.
    La composition préserve les équivalences (fermeture de la structure de
    2-groupeoïde). -/
noncomputable def equivalence_trans {E : Type*} [Category E] (e : C ≌ D) (f : D ≌ E) : C ≌ E :=
  e.trans f

end Grothendieck.Equivalences
