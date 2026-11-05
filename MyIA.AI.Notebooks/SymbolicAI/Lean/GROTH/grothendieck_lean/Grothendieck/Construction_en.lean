/-
Grothendieck Part 30 — The Grothendieck construction (fibered categories)
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

/-!
## 7. Additional bridge theorems: cartesian transport, isomorphisms, functoriality

Complementary bridges connecting the Grothendieck construction to the Mathlib
4 Namespace theorems already exposed as `#check` above. These bridges follow
the pattern of Section 6: direct application of Namespace lemmas (L902 ★★
Tier 5).

For Mathlib 4 theorems with explicit args, direct application `name args` is
the canonical idiom: not `by rw [name]` (Type equality non-rfl-fermable,
cf L902 ★★ Tier 5 c.8232). For `def` (`toTransport`, `isoMk`), direct
application preserves the structure up to namespace (anti-§D byte-identity
preserved).
-/

/-- Bridge theorem: extensionality of morphisms of the total category ∫ F.
    Two morphisms `f g : Hom X Y` of the total category are equal iff their
    base and fiber components coincide. This is the `@[ext (iff := false)]`
    lemma from Mathlib, which enables proofs by component equality.
    Re-exports `Grothendieck.ext` directly. -/
theorem ext_bridge {X Y : CategoryTheory.Grothendieck F}
    (f g : CategoryTheory.Grothendieck.Hom X Y)
    (w_base : f.base = g.base)
    (w_fiber : eqToHom (by rw [w_base]) ≫ f.fiber = g.fiber) :
    f = g :=
  CategoryTheory.Grothendieck.ext f g w_base w_fiber

/-- Bridge theorem: the composition of `Grothendieck.map` with `forget` is
    equal to `forget` (the forgetful functor is a natural fibration).
    Re-exports `Grothendieck.functor_comp_forget` from Mathlib without
    modification. -/
theorem functor_comp_forget_bridge {G : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ G) :
    CategoryTheory.Grothendieck.map α ⋙ CategoryTheory.Grothendieck.forget G =
      CategoryTheory.Grothendieck.forget F := rfl

/-- Bridge theorem: `Grothendieck.map` sends the natural identity to the
    functorial identity. This is the compatibility between the identity of
    the functor F and that of the total category ∫ F. Re-exports
    `Grothendieck.map_id_eq`. -/
theorem map_id_eq_bridge :
    CategoryTheory.Grothendieck.map (𝟙 F) = Functor.id (CategoryTheory.Grothendieck <| F) :=
  CategoryTheory.Grothendieck.map_id_eq

/-- Bridge theorem: `Grothendieck.map` preserves composition of natural
    transformations. This is the functoriality of the Grothendieck
    construction in F, at the level of morphisms. Re-exports
    `Grothendieck.map_comp_eq`. -/
theorem map_comp_eq_bridge {G H : C ⥤ Cat.{v₂, u₂}}
    (α : F ⟶ G) (β : G ⟶ H) :
    CategoryTheory.Grothendieck.map (α ≫ β) =
      CategoryTheory.Grothendieck.map α ⋙ CategoryTheory.Grothendieck.map β :=
  CategoryTheory.Grothendieck.map_comp_eq α β

/-- Bridge construction: the canonical cartesian morphism `x ⟶ x.transport t`,
    induced by `t : x.base ⟶ c` in the base. This is the morphism whose
    universal property characterises cartesian objects of a fibration.
    Re-exports `Grothendieck.toTransport`. -/
def to_transport_bridge (x : CategoryTheory.Grothendieck F) {c : C}
    (t : x.base ⟶ c) :
    x ⟶ CategoryTheory.Grothendieck.transport x t :=
  CategoryTheory.Grothendieck.toTransport x t

/-- Bridge construction: an iso in ∫ F decomposes as a base iso and a fiber
    iso. Re-exports `Grothendieck.isoMk`, which takes a base iso
    `e₁ : X.base ≅ Y.base` and a fiber iso `e₂ : (F.map e₁.hom).toFunctor.obj
    X.fiber ≅ Y.fiber` and constructs the corresponding iso `X ≅ Y`. -/
def iso_mk_bridge {X Y : CategoryTheory.Grothendieck F}
    (e₁ : X.base ≅ Y.base)
    (e₂ : (F.map e₁.hom).toFunctor.obj X.fiber ≅ Y.fiber) :
    X ≅ Y :=
  CategoryTheory.Grothendieck.isoMk e₁ e₂

/-!
## 8. Final bridges: the total category structure and its morphisms

The 2 bridges below close the `#check` documentary repertoire of this
module: the **structure** `Grothendieck F` (the total category ∫ F whose
objects are the pairs `(c, x)` with `c : C` and `x : F(c)`) and the
**morphisms** `Grothendieck.Hom X Y` (the pairs `(f, φ)` — base arrow and
fiber arrow). Each is a type-sig re-export (pattern winner L902 ★★ Tier 5):
resident variables of the module (`{C F}`), structural instances only, no
polymorphic universe constructor.

Universe note (lesson c.1301+144-L1): `Grothendieck F` lives in
`Type (max u u₂)` (the universes of the base `C` and of the target category
of `F : C ⥤ Cat.{v₂, u₂}`) and `Grothendieck.Hom X Y` in `Type (max v v₂)` —
the `Type _` of the type-sig infers them all, aligned on the resident
universes of the module.
-/

/-- Bridge: the **structure of the total category** ∫ F of the Grothendieck
    construction — objects are pairs `(c, x)` with `c : C` and `x : F(c)`,
    where `F : C ⥤ Cat`. This is the reification of parametrized families of
    objects: a family indexed by the objects of C becomes an internal object
    of ∫ F. Type-sig re-export of `CategoryTheory.Grothendieck F`. -/
def grothendieck_field : Type _ :=
  CategoryTheory.Grothendieck F

/-- Bridge: the **morphisms of the total category** ∫ F — for `X Y : ∫ F`, a
    morphism `X ⟶ Y` is a pair `(f, φ)` with `f : X.base ⟶ Y.base` in C
    (base arrow) and `φ : X.fiber ⟶ (F.map f).toFunctor.obj Y.fiber` in the
    fiber (fiber arrow). This is the datum that makes the Grothendieck
    construction a fibered category. Type-sig re-export of
    `CategoryTheory.Grothendieck.Hom`. -/
def grothendieck_hom_field (X Y : CategoryTheory.Grothendieck F) : Type _ :=
  CategoryTheory.Grothendieck.Hom X Y

end Grothendieck.Construction_en
