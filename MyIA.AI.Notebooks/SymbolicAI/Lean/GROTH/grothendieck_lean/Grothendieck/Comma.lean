/-
Grothendieck hommage — Partie 27 : Catégories comma

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

/-!
## 4. Théorèmes ponts : loi fonctorielle et composante de la transformation naturelle

La catégorie comma `Comma L R` est une catégorie à part entière : les
projections `fst` et `snd` sont des foncteurs, et la transformation
naturelle canonique `natTrans : fst ⋙ L ⟶ snd ⋙ R` admet des composantes
qu'on peut expliciter. Les 4 bridges suivants font la jointure entre les
définitions du module et les faits Mathlib 4 sous-jacents :

  - `map_id` / `map_comp` : champs de structure du foncteur `fstFunctor`
    (accès direct `(fstFunctor).map_id X` / `(fstFunctor).map_comp f g`).
  - `natTrans_app` : lemme namespace `@[simp]` de `Mathlib.CategoryTheory.Comma`
    à 3 arguments explicites (`L R X`) — application directe.
  - `fst_snd_map_comp` : composition explicite des projections fst et snd.

Les lemmes namespace à args explicites = application directe (cf. leçon
L902 ★★ Tier 5 : un `by rw [...]` défait la LHS mais ne ferme pas
l'égalité de morphismes en général). Les champs de structure de `Functor`
sont accessibles sans préfixe (`h.map_id X` vs `Functor.map_id h X`).
-/

/-- Bridge : le foncteur `Comma.fst` préserve les identités. C'est le champ
    `Functor.map_id` de la structure, accessible directement. -/
theorem fst_map_id {X : CategoryTheory.Comma L R} :
    (fstFunctor).map (𝟙 X) = 𝟙 ((fstFunctor).obj X) :=
  (fstFunctor).map_id X

/-- Bridge : le foncteur `Comma.fst` préserve la composition des morphismes.
    Champ `Functor.map_comp` de la structure. -/
theorem fst_map_comp {X Y Z : CategoryTheory.Comma L R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (fstFunctor).map (f ≫ g) = (fstFunctor).map f ≫ (fstFunctor).map g :=
  (fstFunctor).map_comp f g

/-- Bridge : la composante de `natTrans : fst ⋙ L ⟶ snd ⋙ R` en un objet
    `(a, b, f)` est la flèche `f` elle-même. Lemme namespace `@[simp]`
    `Comma.natTrans_app` à 3 arguments explicites, application directe. -/
theorem natTrans_app_apply (X : CategoryTheory.Comma L R) :
    (natTransCanonical).app X = X.hom :=
  CategoryTheory.Comma.natTrans_app L R X

/-- Bridge : la composée `fst ⋙ snd` (les deux projections enchaînées) envoie
    un morphisme de `Comma L R` sur la composante droite du carré
    commutatif. C'est la deuxième moitié de la structure : la projection sur
    la catégorie but préserve aussi identités et composition. -/
theorem snd_map_comp {X Y Z : CategoryTheory.Comma L R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (sndFunctor).map (f ≫ g) = (sndFunctor).map f ≫ (sndFunctor).map g :=
  (sndFunctor).map_comp f g

/-!
## 5. Bridges : les structures comma et leurs cas particuliers

Les 5 bridges ci-dessous ferment le répertoire `#check` documentaire du
module : la **structure** `Comma L R` (objets = triplets `(a, b, f)` avec
`f : L.obj a ⟶ R.obj b`), les **morphismes** `CommaMorphism` (carrés
commutatifs), l'**instance de catégorie** `commaCategory`, et les deux cas
particuliers canoniques — la **catégorie slice** `Over X` et les **flèches
structurées** `StructuredArrow S F`. Chacun est un re-export type-sig de
l'API Mathlib (pattern winner L902 ★★ Tier 5) : les variables résidentes du
module (`{A B T L R}`), instances structurelles uniquement, zéro
constructeur polymorphe d'univers.

Universe note (leçon c.1301+144-L1) : `Comma L R` vit dans
`Type (max u₁ u₂ v₃)` — les univers des deux catégories sources et celui
des morphismes du but ; `CommaMorphism X Y` dans `Type (max v₁ v₂)`, et
`Over X` / `StructuredArrow S F` dans `Type (max u₃ v₃)`. Tous alignés
sur les univers résidents du module — aucun univers supplémentaire.
-/

/-- Bridge : la **structure d'objet comma** — un triplet `(a, b, f)` avec
    `a : A`, `b : B` et `f : L.obj a ⟶ R.obj b` (un morphisme de `T`).
    C'est l'encodage d'une flèche « à source dans l'image de `L`, à but
    dans l'image de `R` » — la donnée universelle des familles indexées par
    un morphisme. Type-sig re-export de `CategoryTheory.Comma L R`. -/
def comma_field : Type _ :=
  CategoryTheory.Comma L R

/-- Bridge : les **morphismes de la catégorie comma** — un carré commutatif
    entre deux objets comma `X` et `Y` : un couple `(left, right)` de
    flèches `X.left ⟶ Y.left` dans `A` et `X.right ⟶ Y.right` dans `B` tel
    que `L.map left ≫ Y.hom = X.hom ≫ R.map right`. Type-sig re-export de
    `CategoryTheory.CommaMorphism`. -/
def comma_morphism_field (X Y : CategoryTheory.Comma L R) : Type _ :=
  CategoryTheory.CommaMorphism X Y

/-- Bridge : la donnée de `Comma L R` comme **catégorie** — identités,
    composition, et lois de catégorie. Instance Mathlib `commaCategory`,
    re-exportée en `def` `@[reducible]` (une def de type classe doit être
    marquée `@[reducible]` pour satisfaire le linter). C'est ce qui rend
    tous les morphismes de `Comma L R` composables. -/
@[reducible] def comma_category_field : Category (CategoryTheory.Comma L R) :=
  CategoryTheory.commaCategory

/-- Bridge : la **catégorie slice** `Over X` — le cas particulier de
    catégorie comma `Comma (𝟙 T) (const X)` dont les objets sont les
    flèches `Y ⟶ X` dans `T` et les morphismes les triangles commutatifs.
    C'est l'encodage standard des objets « au-dessus de X » (fibrés,
    espaces au-dessus d'un schéma). Type-sig re-export de
    `CategoryTheory.Over X`. -/
def over_field (X : T) : Type _ :=
  CategoryTheory.Over X

/-- Bridge : les **flèches structurées** `StructuredArrow S F` — le cas
    particulier de catégorie comma `Comma (const S) F` dont les objets sont
    les flèches `S ⟶ F.obj Y` dans `T` et les morphismes les triangles
    commutatifs. C'est l'encodage des « flèches à source fixe S » (pointé,
    initial, base). Type-sig re-export de
    `CategoryTheory.StructuredArrow S F` pour un endofoncteur `F : T ⥤ T`. -/
def structured_arrow_field (S : T) (F : T ⥤ T) : Type _ :=
  CategoryTheory.StructuredArrow S F

end Grothendieck.Comma
