/-
Grothendieck hommage — Partie 26 : Catégories comma

Alexandre Grothendieck (1928-2014).

Extension Phase 2+ (#2159, Epic #1646).

La **catégorie comma** est une construction universelle qui, à partir de
deux foncteurs `L : A ⥤ T` et `R : B ⥤ T` de même but, fabrique la catégorie
`Comma L R` dont :
  - les **objets** sont les triplets `(a, b, f)` avec `a : A`, `b : B` et
    `f : L.obj a ⟶ R.obj b` (un morphisme dans `T`) ;
  - les **morphismes** sont les carrés commutatifs reliant deux tels objets.

Grothendieck utilisait massivement les catégories comma (et leurs cas
particuliers : catégories slices `Over`/`Under`, flèches structurées
`StructuredArrow`) pour encoder les familles d'objets indexées par un
morphisme — fondement des espaces annelés, des champs (champs en
groupoïdes), et de la théorie des foncteurs fibres.

La catégorie comma est aussi le cadre naturel où vivent les adjonctions
(voir `Adjunction.lean`) : les foncteurs d'oubli, les foncteurs libres, et
les constructions universelles s'expriment comme des objets initiaux/
terminaux d'une catégorie comma.

Mathlib 4 formalise les catégories comma dans `Mathlib.CategoryTheory.Comma` :
  - `structure Comma (L : A ⥤ T) (R : B ⥤ T)` — la catégorie comma
  - `CommaMorphism` — les morphismes (carrés commutatifs)
  - `commaCategory : Category (Comma L R)` — l'instance de catégorie
  - `Comma.fst : Comma L R ⥤ A` / `Comma.snd : Comma L R ⥤ B` — projections
  - `Comma.natTrans : fst ⋙ L ⟶ snd ⋙ R` — la transformation naturelle canonique

Ce module ré-expose ces faits comme un parcours pédagogique organisé.

Epic #1646, See #2159. Aucun `sorry` à la création.

### i18n — convention #4980 ratifiée 2026-07-04

Ce module est jumelé avec sa version anglaise canonique dans le fichier
sibling `Comma_en.lean`. Les énoncés de théorèmes, les noms de lemmes,
les tactiques Lean et les références Mathlib restent en anglais. Seules les
**docstrings `/-- ... -/`** et les **commentaires `-- ...`** diffèrent entre
les deux fichiers. Anti-§D byte-identity garanti : le namespace body est
préservé bit-pour-bit entre `Comma.lean` et `Comma_en.lean`.
-/

import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Grothendieck.Comma

open CategoryTheory

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {T : Type u₃} [Category.{v₃} T]
  {L : A ⥤ T} {R : B ⥤ T}

/-!
## 1. La structure d'objet comma

Un objet de la catégorie comma `Comma L R` est un triplet `(a, b, f)` où
`a : A`, `b : B`, et `f : L.obj a ⟶ R.obj b` est un morphisme dans `T`.
C'est l'encodage d'une flèche « à source dans l'image de `L`, à but dans
l'image de `R` ».
-/

-- La catégorie comma `Comma L R` : objets = triplets (a, b, f : L a ⟶ R b).
#check @CategoryTheory.Comma

-- Un morphisme de catégories comma : carré commutatif entre deux objets.
#check @CategoryTheory.CommaMorphism

-- La donnée de `Comma L R` comme catégorie (identité + composition).
#check @CategoryTheory.commaCategory

/-!
## 2. Les projections vers les catégories source

Deux foncteurs d'oubli canoniques projettent la catégorie comma sur ses
catégories sous-jacentes :
  - `Comma.fst : Comma L R ⥤ A` oublie `b` et `f`, garde `a` ;
  - `Comma.snd : Comma L R ⥤ B` oublie `a` et `f`, garde `b`.

La composée de ces projections avec `L` et `R` est reliée par une
transformation naturelle `Comma.natTrans : fst ⋙ L ⟶ snd ⋙ R` dont la
composante en un objet `(a, b, f)` est précisément la flèche `f`.
-/

/-- Le foncteur de projection `Comma.fst : Comma L R ⥤ A` : oublie `b`
    et la flèche `f`, ne retient que l'objet source `a : A`. -/
def fstFunctor : CategoryTheory.Comma L R ⥤ A :=
  CategoryTheory.Comma.fst L R

/-- Le foncteur de projection `Comma.snd : Comma L R ⥤ B` : oublie `a`
    et la flèche `f`, ne retient que l'objet but `b : B`. -/
def sndFunctor : CategoryTheory.Comma L R ⥤ B :=
  CategoryTheory.Comma.snd L R

/-- La transformation naturelle canonique `fst ⋙ L ⟶ snd ⋙ R` : sa
    composante en `(a, b, f)` est la flèche `f` elle-même. C'est elle qui
    fait de `Comma L R` la « catégorie universelle des flèches `L → R`. -/
def natTransCanonical :
    CategoryTheory.Comma.fst L R ⋙ L ⟶ CategoryTheory.Comma.snd L R ⋙ R :=
  CategoryTheory.Comma.natTrans L R

/-!
## 3. Cas particuliers fondamentaux : slices et flèches structurées

Les catégories comma particularisées donnent les constructions
fondamentales de Grothendieck :
  - la **catégorie slice** `Over X` (objets : morphismes de but `X`) =
    `Comma (𝟭 C) (functor.ofObj X)` ;
  - la **catégorie coslice** `Under X` (objets : morphismes de source `X`) ;
  - les **flèches structurées** `StructuredArrow` (cas où un foncteur est
    l'inclusion d'un objet).

Ces cas particuliers sont l'encodage standard des familles indexées par un
morphisme en géométrie algébrique (fibrés, champs).
-/

-- La catégorie slice et les flèches structurées sont des cas particuliers
-- de catégorie comma. Mathlib les définit dans `Mathlib.CategoryTheory.Comma`.
#check @CategoryTheory.Over
#check @CategoryTheory.StructuredArrow

end Grothendieck.Comma
