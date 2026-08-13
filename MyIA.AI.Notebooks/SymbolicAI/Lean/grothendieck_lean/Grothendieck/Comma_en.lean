/-
Grothendieck tribute — Part 27: Comma categories

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

/-!
## 4. Bridge theorems: functorial law and natural transformation component

The comma category `Comma L R` is a full-fledged category: the projections
`fst` and `snd` are functors, and the canonical natural transformation
`natTrans : fst ⋙ L ⟶ snd ⋙ R` admits explicit components. The 4 bridges
below join the module's definitions with the underlying Mathlib 4 facts:

  - `map_id` / `map_comp`: structure fields of the `fstFunctor` (direct
    access `(fstFunctor).map_id X` / `(fstFunctor).map_comp f g`).
  - `natTrans_app`: `@[simp]` namespace lemma of `Mathlib.CategoryTheory.Comma`
    with 3 explicit arguments (`L R X`) — direct application.
  - `snd_map_comp`: explicit composition of the snd projection.

Namespace lemmas with explicit args = direct application (cf. lesson
L902 ★★ Tier 5: a `by rw [...]` defeats the LHS but doesn't generally
close the morphism equality). Functor structure fields are accessible
without prefix (`h.map_id X` vs `Functor.map_id h X`).
-/

/-- Bridge: the `Comma.fst` functor preserves identities. This is the
    `Functor.map_id` structure field, directly accessible. -/
theorem fst_map_id {X : CategoryTheory.Comma L R} :
    (fstFunctor).map (𝟙 X) = 𝟙 ((fstFunctor).obj X) :=
  (fstFunctor).map_id X

/-- Bridge: the `Comma.fst` functor preserves composition of morphisms.
    Structure field `Functor.map_comp`. -/
theorem fst_map_comp {X Y Z : CategoryTheory.Comma L R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (fstFunctor).map (f ≫ g) = (fstFunctor).map f ≫ (fstFunctor).map g :=
  (fstFunctor).map_comp f g

/-- Bridge: the component of `natTrans : fst ⋙ L ⟶ snd ⋙ R` at an object
    `(a, b, f)` is the arrow `f` itself. Namespace lemma `@[simp]`
    `Comma.natTrans_app` with 3 explicit arguments, direct application. -/
theorem natTrans_app_apply (X : CategoryTheory.Comma L R) :
    (natTransCanonical).app X = X.hom :=
  CategoryTheory.Comma.natTrans_app L R X

/-- Bridge: the composition `snd` (the second projection) on a morphism
    of `Comma L R` is the right component of the commutative square.
    This is the second half of the structure: the target category
    projection also preserves identities and composition. -/
theorem snd_map_comp {X Y Z : CategoryTheory.Comma L R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (sndFunctor).map (f ≫ g) = (sndFunctor).map f ≫ (sndFunctor).map g :=
  (sndFunctor).map_comp f g

end Grothendieck.Comma_en
