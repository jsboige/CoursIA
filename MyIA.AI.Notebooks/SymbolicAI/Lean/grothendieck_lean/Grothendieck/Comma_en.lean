/-
Grothendieck tribute — Part 26: Comma categories

Alexander Grothendieck (1928-2014).

Phase 2+ extension (#2159, Epic #1646).

The **comma category** is a universal construction which, from two
functors `L : A ⥤ T` and `R : B ⥤ T` with common codomain, builds the
category `Comma L R` whose:
  - **objects** are triples `(a, b, f)` with `a : A`, `b : B`, and
    `f : L.obj a ⟶ R.obj b` (a morphism in `T`);
  - **morphisms** are commutative squares relating two such objects.

Grothendieck used comma categories extensively (and their special cases:
slice categories `Over`/`Under`, structured arrows `StructuredArrow`) to
encode families of objects indexed by a morphism — the foundation of
ringed spaces, stacks (stacks in groupoids), and the theory of fibered
functors.

The comma category is also the natural setting where adjunctions live (see
`Adjunction.lean`): forgetful functors, free functors, and universal
constructions are expressed as initial/terminal objects of a comma
category.

Mathlib 4 formalizes comma categories in `Mathlib.CategoryTheory.Comma`:
  - `structure Comma (L : A ⥤ T) (R : B ⥤ T)` — the comma category
  - `CommaMorphism` — the morphisms (commutative squares)
  - `commaCategory : Category (Comma L R)` — the category instance
  - `Comma.fst : Comma L R ⥤ A` / `Comma.snd : Comma L R ⥤ B` — projections
  - `Comma.natTrans : fst ⋙ L ⟶ snd ⋙ R` — the canonical natural transformation

This module restates these facts as a curated pedagogical tour.

Epic #1646, See #2159. No `sorry` at creation.

### i18n — convention #4980 ratified 2026-07-04

This module is paired with its French canonical counterpart in the sibling
file `Comma.lean`. Theorem statements, lemma names, Lean tactics, and
Mathlib references remain in English. Only the **docstrings `/-- ... -/`**
and **comments `-- ...`** differ between the two files. Anti-§D
byte-identity guaranteed: the namespace body is preserved bit-for-bit
between `Comma.lean` and `Comma_en.lean`.
-/

import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Grothendieck.Comma_en

open CategoryTheory

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {T : Type u₃} [Category.{v₃} T]
  {L : A ⥤ T} {R : B ⥤ T}

/-!
## 1. The comma object structure

An object of the comma category `Comma L R` is a triple `(a, b, f)` where
`a : A`, `b : B`, and `f : L.obj a ⟶ R.obj b` is a morphism in `T`. It
encodes an arrow "with source in the image of `L`, with target in the
image of `R`".
-/

-- The comma category `Comma L R`: objects = triples (a, b, f : L a ⟶ R b).
#check @CategoryTheory.Comma

-- A morphism of comma categories: a commutative square between two objects.
#check @CategoryTheory.CommaMorphism

-- The data of `Comma L R` as a category (identity + composition).
#check @CategoryTheory.commaCategory

/-!
## 2. The projections to the source categories

Two canonical forgetful functors project the comma category onto its
underlying categories:
  - `Comma.fst : Comma L R ⥤ A` forgets `b` and `f`, keeps `a`;
  - `Comma.snd : Comma L R ⥤ B` forgets `a` and `f`, keeps `b`.

The composite of these projections with `L` and `R` is related by a
natural transformation `Comma.natTrans : fst ⋙ L ⟶ snd ⋙ R` whose
component at an object `(a, b, f)` is precisely the arrow `f`.
-/

/-- The projection functor `Comma.fst : Comma L R ⥤ A`: forgets `b` and
    the arrow `f`, retaining only the source object `a : A`. -/
def fstFunctor : CategoryTheory.Comma L R ⥤ A :=
  CategoryTheory.Comma.fst L R

/-- The projection functor `Comma.snd : Comma L R ⥤ B`: forgets `a` and
    the arrow `f`, retaining only the target object `b : B`. -/
def sndFunctor : CategoryTheory.Comma L R ⥤ B :=
  CategoryTheory.Comma.snd L R

/-- The canonical natural transformation `fst ⋙ L ⟶ snd ⋙ R`: its
    component at `(a, b, f)` is the arrow `f` itself. This is what makes
    `Comma L R` the "universal category of arrows `L → R`". -/
def natTransCanonical :
    CategoryTheory.Comma.fst L R ⋙ L ⟶ CategoryTheory.Comma.snd L R ⋙ R :=
  CategoryTheory.Comma.natTrans L R

/-!
## 3. Fundamental special cases: slices and structured arrows

Specialized comma categories yield Grothendieck's fundamental constructions:
  - the **slice category** `Over X` (objects: morphisms with target `X`) =
    `Comma (𝟭 C) (functor.ofObj X)`;
  - the **coslice category** `Under X` (objects: morphisms with source `X`);
  - **structured arrows** `StructuredArrow` (case where one functor is the
    inclusion of an object).

These special cases are the standard encoding of families indexed by a
morphism in algebraic geometry (bundles, stacks).
-/

-- The slice category and structured arrows are special cases of the comma
-- category. Mathlib defines them in `Mathlib.CategoryTheory.Comma`.
#check @CategoryTheory.Over
#check @CategoryTheory.StructuredArrow

end Grothendieck.Comma_en
