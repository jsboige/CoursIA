/-
Grothendieck Part 27 — The Grothendieck construction (fibered categories)
(English mirror of Construction.lean)

Alexander Grothendieck (1928-2014).

Extension Phase 2+ (#2159, Epic #1646).

The Grothendieck construction — the "yoga of functors" — is one of
Grothendieck's most fruitful ideas. To a functor `F : C ⥤ Cat` it
associates a category `∫ F` (the total category) equipped with a functor
`forget : ∫ F ⥤ C` (the fibration) whose fibers above each object `c : C`
recover the category `F(c)`. This is the language of fibered categories,
central to descent theory (SGA 1), algebraic stacks (stacks = fibered
categories in groupoids), and relative algebraic geometry (a scheme over S
is an object of the fiber of a fibration above S).

Grothendieck uses this construction to reify parameterised families of
objects: a family of objects of F indexed by the objects of C is no longer
an external collection but an internal object of ∫ F. Effective descent
(characterising which morphisms of C let us glue families) is then
expressible as a property of the fibration.

Mathlib 4 formalises this construction in
`Mathlib.CategoryTheory.Grothendieck`:
  - `CategoryTheory.Grothendieck : (C ⥤ Cat) → Type*` — the total category ∫ F
  - `CategoryTheory.Grothendieck.Hom` — the morphisms (base arrow + fiber arrow)
  - `CategoryTheory.Grothendieck.forget : ∫ F ⥤ C` — the forgetful functor (the fibration)
  - `CategoryTheory.Grothendieck.map : (F ⟶ G) → (∫ F ⥤ ∫ G)` — functoriality in F
  - `CategoryTheory.Grothendieck.transport` / `toTransport` — cartesian transport
  - `CategoryTheory.Grothendieck.isoMk` — an isomorphism from base + fiber isos
  - `CategoryTheory.FiberedCategory` — the language of fibrations/cartesian arrows

This module re-exposes these facts as an organised pedagogical tour for
learners encountering fibered categories for the first time.

Epic #1646, See #2159. No `sorry` at creation.

### i18n — convention #4980 ratified 2026-07-04

This module is the English mirror of `Construction.lean`. Theorem statements,
lemma names, Lean tactics and Mathlib references stay in English. Only the
**docstrings `/-- ... -/`** and **comments `-- ...`** differ between the two
files. Anti-§D byte-identity guaranteed.
-/

import Mathlib.CategoryTheory.Grothendieck

universe v v₂ u u₂

namespace Grothendieck.Construction_en

open CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (F : C ⥤ Cat.{v₂, u₂})

/-!
## 1. The total category ∫ F

To a functor `F : C ⥤ Cat`, the Grothendieck construction associates a
total category `∫ F` whose objects are pairs `(c, x)` with `c : C` and
`x : F(c)`, and whose morphisms `(c, x) ⟶ (d, y)` are pairs `(f, φ)` with
`f : c ⟶ d` in C and `φ : x ⟶ F(f)(y)` in the fiber.
-/

-- The total category ∫ F associated to the functor F : C ⥤ Cat.
#check @CategoryTheory.Grothendieck

-- The morphisms of ∫ F: a pair (base arrow, fiber arrow).
#check @CategoryTheory.Grothendieck.Hom

/-!
## 2. The forgetful functor (the fibration)

The functor `forget : ∫ F ⥤ C` forgets the fiber data and keeps only the
base. This is the structural functor of the construction: its fibers
(preimages of objects of C) recover exactly the categories `F(c)`. A
fibration is, in practice, "a functor that looks like a forget".
-/

-- The forgetful functor ∫ F ⥤ C (the fibration functor).
#check @CategoryTheory.Grothendieck.forget

/-!
## 3. Functoriality in F

The Grothendieck construction is itself functorial: a natural transformation
`α : F ⟶ G` induces a functor `∫ F ⥤ ∫ G` that preserves the base (commutes
with the two forgetful functors).
-/

-- The functorial action of a natural transformation α : F ⟶ G on ∫ F ⥤ ∫ G.
#check @CategoryTheory.Grothendieck.map

/-!
## 4. Cartesian transport

For an object `x : ∫ F` above `c` and an arrow `t : c ⟶ d` in C, the
transport `x.transport t` is the object above `d` obtained by applying
`F(t)` to the fiber of x. The morphism `toTransport` is the canonical
cartesian arrow `x ⟶ x.transport t`. Cartesian arrows are the "good"
morphisms of a fibration (those that lift exactly, in the descent sense).
-/

-- The transport of an object of ∫ F along an arrow of the base.
#check @CategoryTheory.Grothendieck.transport

-- The canonical cartesian arrow x ⟶ x.transport t induced by t.
#check @CategoryTheory.Grothendieck.toTransport

/-!
## 5. Isomorphisms in ∫ F

An isomorphism in ∫ F splits into an isomorphism of the base and an
isomorphism of the fiber — this is `isoMk`. This decomposition is central
to transporting structures along isos in the base (descent).
-/

-- Construction of an iso in ∫ F from a base iso + a fiber iso.
#check @CategoryTheory.Grothendieck.isoMk

/-!
## 6. Bridge theorems

Reformulations in the project namespace, bridging the Mathlib facts.
-/

/-- Bridge: the forgetful functor of the Grothendieck construction ∫ F ⥤ C.
    This is the canonical fibration functor whose fibers above each `c : C`
    recover the category `F(c)`. -/
def forget_family : CategoryTheory.Grothendieck F ⥤ C :=
  CategoryTheory.Grothendieck.forget F

/-- Bridge: the Grothendieck construction is functorial in F. A natural
    transformation α : F ⟶ G induces a functor ∫ F ⥤ ∫ G that commutes with
    the forgetful functors (preserves the base). -/
def map_family {G : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ G) :
    CategoryTheory.Grothendieck F ⥤ CategoryTheory.Grothendieck G :=
  CategoryTheory.Grothendieck.map α

/-- Bridge: the cartesian transport of an object of ∫ F along an arrow of
    the base. This is the lifting operation that defines the "fibered"
    character of the projection (existence of cartesian arrows). -/
def transport_family (x : CategoryTheory.Grothendieck F) {c : C}
    (t : (CategoryTheory.Grothendieck.forget F).obj x ⟶ c) :
    CategoryTheory.Grothendieck F :=
  CategoryTheory.Grothendieck.transport x t

end Grothendieck.Construction_en
