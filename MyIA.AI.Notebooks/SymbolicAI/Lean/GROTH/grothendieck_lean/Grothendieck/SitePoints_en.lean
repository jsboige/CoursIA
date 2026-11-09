/-
Grothendieck tribute — Part 15: Points of a site (fiber functors)
Alexandre Grothendieck (1928-2014).

Phase 9 extension (#2159, Epic #1646).

Part 14 (LeftExact.lean) showed that sheafification preserves finite limits,
making categories of sheaves finitary extensive, adhesive, and balanced.

This module introduces **Grothendieck points** (SGA 4 IV 6.3): a point of
a site (C, J) is a "fiber functor" Φ.fiber : C ⥤ Type that is cofiltered
and respects covering sieves. From it, we derive:

  - Φ.presheafFiber : the colimit fiber functor on presheaves
  - Φ.sheafFiber : the fiber functor restricted to sheaves
  - The category structure on points (morphisms = natural transformations
    in the opposite direction, SGA 4 IV 3.2)

A point Φ lets us "probe" sheaves stalkwise — the stalk (fiber) of a
sheaf F at Φ is Φ.sheafFiber.obj F. This is the categorical generalization
of the stalk of a sheaf on a topological space at a point.

We index Mathlib's `CategoryTheory.Sites.Point.Basic` and
`CategoryTheory.Sites.Point.Category` into the `Grothendieck_en` namespace.

Epic #1646, Phase 9 (#2159). All `sorry`s eliminated at creation.
-/

import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Category

universe v u w

namespace Grothendieck_en

open CategoryTheory
open CategoryTheory.Limits

/-!
## What is a point of a site?

In topology, a "point" x of a space X lets you evaluate functions at x,
giving a map Γ(U) → stalk_x for each open U. Grothendieck generalized
this to arbitrary sites: a point Φ of (C, J) gives a "fiber functor"
that evaluates sheaves at abstract "points", without requiring an
underlying topological space.

Formally, `GrothendieckTopology.Point J` is a structure consisting of:
  - `fiber : C ⥤ Type w` — a functor to types (the "stalk functor")
  - `isCofiltered` — the category of elements of `fiber` is cofiltered
    (this ensures exactness: fiber functors commute with finite limits)
  - `jointly_surjective` — every covering sieve hits every element of
    the fiber (this connects the topology to the fiber functor)

Reference: SGA 4 IV 6.3.
-/

-- A point of a site (C, J) is a fiber functor Φ : C ⥤ Type satisfying
-- cofilteredness and a coverage condition. It generalizes the notion
-- of "point" in topology to arbitrary sites.
-- This is `GrothendieckTopology.Point` from Mathlib's Sites.Point.Basic.
#check @GrothendieckTopology.Point

/-!
## The presheaf fiber functor

Given a point Φ, the presheaf fiber functor evaluates a presheaf P at
Φ by taking the colimit of P over the category of elements of Φ.fiber.

Intuitively: Φ.presheafFiber.obj P is the "stalk of P at Φ", defined as
a filtered colimit over all pairs (X, x) where X : C and
x : Φ.fiber.obj X.
-/

-- The presheaf fiber functor: evaluates presheaves at a point.
-- Defined as the colimit `(Cᵒᵖ ⥤ A) ⥤ A` obtained by composing
-- the whiskering of `CategoryOfElements.π Φ.fiber` with `colim`.
#check @GrothendieckTopology.Point.presheafFiber

-- The canonical map from P.obj (op X) to the fiber of P at Φ,
-- given a witness x : Φ.fiber.obj X. This is the colimit inclusion.
#check @GrothendieckTopology.Point.toPresheafFiber

/-!
## The sheaf fiber functor

Restricting the presheaf fiber functor to the subcategory of sheaves
gives Φ.sheafFiber : Sheaf J A ⥤ A. This is the key functor for
studying sheaves "stalkwise".

Because the fiber functor commutes with colimits and finite limits
(under suitable assumptions on A), it preserves exact sequences,
making it a key tool in sheaf cohomology.
-/

-- The sheaf fiber functor: evaluates sheaves at a point.
-- This is the restriction of presheafFiber to the full subcategory of sheaves.
-- Concretely `sheafFiber = sheafToPresheaf ⋙ presheafFiber` BY DEFINITION
-- (Mathlib `CategoryTheory.Sites.Point.Basic`): evaluating a sheaf at a point Φ
-- is evaluating its underlying presheaf at Φ. We promote the `#check` into a
-- proven canonical iso below.

/-- The sheaf fiber functor factors through the presheaf fiber functor via
    the embedding "sheaf ↦ underlying presheaf" `sheafToPresheaf`. Evaluating
    a sheaf at a point therefore amounts to evaluating the underlying presheaf
    at that same point: this is exactly the definition of `sheafFiber` as
    `sheafToPresheaf ⋙ presheafFiber` given by Mathlib in
    `CategoryTheory.Sites.Point.Basic`. The canonical iso is obtained via
    `sheafToPresheafCompPresheafFiberIso` (a reflexivity). -/
noncomputable def sheaf_fiber_presheaf_fiber_iso {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (Φ : GrothendieckTopology.Point.{w} J) :
    sheafToPresheaf J (Type (max u w)) ⋙ Φ.presheafFiber ≅ Φ.sheafFiber :=
  Φ.sheafToPresheafCompPresheafFiberIso

/-!
## Morphisms between points

Points of a site form a category (SGA 4 IV 3.2). A morphism
Φ₁ ⟶ Φ₂ is a natural transformation
Φ₂.fiber ⟶ Φ₁.fiber (note the reversal of direction!).

This reversal is natural: a "map of spaces" f : X → Y induces
a map on stalks in the opposite direction (pullback along f).
-/

-- A morphism between points consists of a natural transformation
-- between fiber functors, in the opposite direction.
#check @GrothendieckTopology.Point.Hom

/-!
## The trivial and discrete topologies

For the trivial topology (⊥), every presheaf is a sheaf, so fiber
functors coincide with evaluation functors at objects.

For the discrete topology (⊤), only the terminal presheaf is a sheaf,
making the theory of points less interesting.
-/

-- The trivial Grothendieck topology (coarsest): every presheaf is a sheaf.
#check @GrothendieckTopology.trivial

-- The discrete Grothendieck topology (finest): only representable presheaves.
#check @GrothendieckTopology.discrete

/-!
## The coverage condition

The `jointly_surjective` condition ensures that covering sieves hit
every element of the fiber. This connects the topology to the stalkwise
perspective: if R is a covering sieve of X, then for every x in the
fiber of X, there exists a morphism f : Y ⟶ X in R and y in the fiber
of Y such that Φ.fiber.map f y = x.
-/

-- The coverage condition: every covering sieve hits every element of the fiber.
#check @GrothendieckTopology.Point.jointly_surjective

/-!
## Bridge theorems: the fiber of a representable presheaf

For a representable presheaf `yoneda.obj X`, the fiber at a point Φ
recovers the value of the fiber functor at X:
  Φ.presheafFiber.obj (yoneda.obj X) ≅ Φ.fiber.obj X

This bridges the Yoneda perspective (presheaves as "generalized objects")
with the stalkwise perspective (points as "probes").

Note: this requires `LocallySmall.{w} C` to match universe levels
between `shrinkYoneda` and `Φ.fiber`.
-/

/-- The fiber of the (shrunk) Yoneda embedding at a point recovers the
    fiber functor value. This is `shrinkYonedaCompPresheafFiberIso` from Mathlib:
    `shrinkYoneda ⋙ Φ.presheafFiber ≅ Φ.fiber`.
    It shows that the presheaf fiber functor extends the fiber functor
    from objects to presheaves via the Yoneda embedding. -/
noncomputable def fiber_yoneda_iso {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [LocallySmall.{w} C]
    (Φ : GrothendieckTopology.Point.{w} J) :
    shrinkYoneda.{w} ⋙ Φ.presheafFiber ≅ Φ.fiber :=
  Φ.shrinkYonedaCompPresheafFiberIso

/-!
## The presheaf fiber as a colimit

The fiber Φ.presheafFiber.obj P is defined as a colimit over the
category of elements of Φ.fiber. Mathlib provides:
  - `presheafFiberCocone P` : the canonical cocone
  - `isColimitPresheafFiberCocone P` : it is a colimit

These allow constructing maps *from* the fiber using the universal
property of colimits.
-/

/-- The colimit cocone that defines the presheaf fiber.
    Uses `presheafFiberCocone` from Mathlib. -/
noncomputable def presheaf_fiber_cocone {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (Φ : GrothendieckTopology.Point.{w} J) (P : Cᵒᵖ ⥤ Type (max u w)) :
    Cocone ((CategoryOfElements.π Φ.fiber).op ⋙ P) :=
  Φ.presheafFiberCocone P

/-- The presheaf fiber cocone is a colimit. This gives the universal
    property: any compatible family of elements indexed by (X, x) extends
    uniquely to a map from the fiber.
    Uses `isColimitPresheafFiberCocone` from Mathlib. -/
noncomputable def is_colimit_presheaf_fiber {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (Φ : GrothendieckTopology.Point.{w} J) (P : Cᵒᵖ ⥤ Type (max u w)) :
    IsColimit (Φ.presheafFiberCocone P) :=
  Φ.isColimitPresheafFiberCocone P

/-!
## Extensionality for fiber maps

Two maps from the fiber of a presheaf agree if they agree on all
"germs" (X, x) : for every X : C and x : Φ.fiber.obj X, the maps
agree after precomposing with the canonical inclusion.
-/

/-- Extensionality for maps from the presheaf fiber: two maps f, g from
    Φ.presheafFiber.obj P agree iff they agree on all toPresheafFiber inclusions.
    Uses `presheafFiber_hom_ext` from Mathlib. -/
theorem presheaf_fiber_hom_ext {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (Φ : GrothendieckTopology.Point.{w} J) {P : Cᵒᵖ ⥤ Type (max u w)}
    {T : Type (max u w)} {f g : Φ.presheafFiber.obj P ⟶ T}
    (h : ∀ (X : C) (x : Φ.fiber.obj X),
      Φ.toPresheafFiber X x P ≫ f = Φ.toPresheafFiber X x P ≫ g) :
    f = g :=
  Φ.presheafFiber_hom_ext h

/-!
## Naturality of `toPresheafFiber` along morphisms of `C`

For any morphism `f : X ⟶ Y` in the base category and any element
`x : Φ.fiber.obj X`, the application `toPresheavFiber X x P : P.obj (op X) ⟶ Φ.fiber`
commutes with `P.map f.op`. This is the naturality of the cocone `presheafFiberCocone`
with respect to morphisms of `C`.

This is `toPresheafFiber_w` from Mathlib.
-/

/-- Naturality of `toPresheafFiber` along a morphism of the base category:
    for `f : X ⟶ Y` and `x : Φ.fiber.obj X`, the equality
    `P.map f.op ≫ toPresheafFiber X x = toPresheafFiber Y (Φ.fiber.map f x)`
    relates the action of the presheaf (pullback P.map) to the fiber functor.
    Uses `toPresheafFiber_w` from Mathlib. -/
theorem to_presheaf_fiber_w {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (Φ : GrothendieckTopology.Point.{w} J) {X Y : C} (f : X ⟶ Y)
    (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ Type (max u w)) :
    P.map f.op ≫ Φ.toPresheafFiber X x P = Φ.toPresheafFiber Y (Φ.fiber.map f x) P :=
  Φ.toPresheafFiber_w f x P

/-!
## Naturality of `toPresheafFiber` along presheaf morphisms

For any presheaf morphism `g : P ⟶ Q`, the inclusion into the fiber
`toPresheafFiber X x` commutes with `presheafFiber.map g`. This is the naturality
of the colimit cocone with respect to presheaf morphisms.

This is `toPresheafFiber_naturality` from Mathlib.
-/

/-- Naturality of `toPresheafFiber` along a presheaf morphism:
    for `g : P ⟶ Q`, we have `toPresheafFiber X x P ≫ presheafFiber.map g =
    g.app (op X) ≫ toPresheafFiber X x Q`.
    Uses `toPresheafFiber_naturality` from Mathlib. -/
theorem to_presheaf_fiber_naturality {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (Φ : GrothendieckTopology.Point.{w} J) {P Q : Cᵒᵖ ⥤ Type (max u w)}
    (g : P ⟶ Q) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x P ≫ Φ.presheafFiber.map g =
      g.app (Opposite.op X) ≫ Φ.toPresheafFiber X x Q :=
  Φ.toPresheafFiber_naturality g X x

/-!
## The trivial and discrete topologies in the topology lattice

The trivial topology (the coarsest) coincides with the minimum element
of the lattice of Grothendieck topologies; the discrete topology (the finest)
coincides with the maximum element. These two identities anchor the extreme
topologies in the language of order, making their canonical role transparent.

These are `trivial_eq_bot` and `discrete_eq_top` from Mathlib (CategoryTheory.Sites.Grothendieck).
-/

/-- The trivial topology is the minimum element of the topology lattice:
    `trivial C = ⊥`. Every set is covering for the trivial topology, so
    every presheaf is a sheaf — which makes the trivial topology "the coarsest".
    Uses `trivial_eq_bot` from Mathlib. -/
theorem trivial_topology_eq_bot (C : Type u) [Category.{v} C] :
    GrothendieckTopology.trivial C = ⊥ :=
  CategoryTheory.GrothendieckTopology.trivial_eq_bot

/-- The discrete topology is the maximum element of the topology lattice:
    `discrete C = ⊤`. Only the maximal sieve is covering, so only the
    terminal presheaf is a sheaf — which makes the discrete topology "the finest".
    Uses `discrete_eq_top` from Mathlib. -/
theorem discrete_topology_eq_top (C : Type u) [Category.{v} C] :
    GrothendieckTopology.discrete C = ⊤ :=
  CategoryTheory.GrothendieckTopology.discrete_eq_top

/-!
## 10. Bridges: the abstract shape of Grothendieck points

The 7 bridges below close the `#check` documentary repertoire of this
module: the **structure** `Point` (the "stalk functor" `Φ.fiber`, cofiltered
and meeting every covering sieve), the **presheaf fiber functor**
`Φ.presheafFiber` (the colimit over the category of elements) with its
**canonical inclusion** `Φ.toPresheafFiber`, the **category of points**
`Point.Hom` (morphisms between points, SGA 4 IV 3.2), the **trivial** and
**discrete** topologies, and the **coverage condition** `jointly_surjective`
(SGA 4 IV 6.3). Each is a type-sig re-export of the Mathlib API (pattern
winner L902 ★★ Tier 5): resident arguments (`{C : Type u} [Category.{v} C]`
plus `(Φ : GrothendieckTopology.Point.{w} J)`), structural instances only,
no polymorphic universe constructor.

Universe note (lesson c.1301+143-L1): `Point.{w} J` lives in
`Type (max (max u v) (w + 1))` — the third universe `w` is that of the
fibers (`Φ.fiber : C ⥤ Type w`). The presheaf fiber functor additionally
requires cocompleteness of the target (`HasColimitsOfSize`), which the
category of types `Type (max u w)` always satisfies; it is `noncomputable`
(a colimit has no canonical choice).
-/

/-- Bridge: the **structure of a point** of a site `(C, J)` — a functor
    `Φ.fiber : C ⥤ Type w` whose category of elements is cofiltered (which
    ensures exactness: commutation with finite limits) and which meets
    every covering sieve. This is the Grothendieck generalization of the
    point of a topological space (SGA 4 IV 6.3). Type-sig re-export of
    `GrothendieckTopology.Point.{w} J`. -/
def point_field {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) : Type _ :=
  GrothendieckTopology.Point.{w} J

/-- Bridge: the **presheaf fiber functor** at a point `Φ` — evaluates a
    presheaf `P` by taking the colimit of `P` over the category of elements
    of `Φ.fiber`. Intuitively, `presheafFiber.obj P` is the "stalk of P at
    Φ", the filtered colimit over all pairs `(X, x)` with `x : Φ.fiber.obj X`.
    Type-sig re-export of `GrothendieckTopology.Point.presheafFiber` (the
    target type is the category of types in our fiber universe
    `Type (max u w)`). -/
noncomputable def presheaf_fiber_field {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (Φ : GrothendieckTopology.Point.{w} J) :
    (Cᵒᵖ ⥤ Type (max u w)) ⥤ Type (max u w) :=
  Φ.presheafFiber

/-- Bridge: the **canonical inclusion** into the fiber — for a witness
    `x : Φ.fiber.obj X`, the morphism `P.obj (op X) ⟶ Φ.presheafFiber.obj P`
    sending a section to the class of `(X, x)` in the colimit. This is the
    leg of the colimit cocone that defines `presheafFiber`. Type-sig
    re-export of `GrothendieckTopology.Point.toPresheafFiber`. -/
noncomputable def to_presheaf_fiber_field {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (Φ : GrothendieckTopology.Point.{w} J)
    (X : C) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ Type (max u w)) :
    P.obj (Opposite.op X) ⟶ Φ.presheafFiber.obj P :=
  Φ.toPresheafFiber X x P

/-- Bridge: **morphisms between points** of a site — a natural
    transformation in the reverse direction between the fiber functors
    (SGA 4 IV 3.2). The points of a site form a category: this is what
    allows comparing the "probes" of a site with each other. Type-sig
    re-export of `GrothendieckTopology.Point.Hom`. -/
def point_hom_field {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (Φ₁ Φ₂ : GrothendieckTopology.Point.{w} J) :
    Type _ :=
  GrothendieckTopology.Point.Hom Φ₁ Φ₂

/-- Bridge: the **trivial topology** on `C` — the coarsest one: every
    sieve is covering, so every presheaf is a sheaf (cf
    `trivial_topology_eq_bot`: `trivial C = ⊥`). Type-sig re-export of
    `GrothendieckTopology.trivial`. -/
def trivial_field (C : Type u) [Category.{v} C] :
    GrothendieckTopology C :=
  GrothendieckTopology.trivial C

/-- Bridge: the **discrete topology** on `C` — the finest one: only the
    maximal sieve is covering, so only the terminal presheaf is a sheaf
    (cf `discrete_topology_eq_top`: `discrete C = ⊤`). Type-sig re-export
    of `GrothendieckTopology.discrete`. -/
def discrete_field (C : Type u) [Category.{v} C] :
    GrothendieckTopology C :=
  GrothendieckTopology.discrete C

/-- Bridge: the **coverage condition** of a point (SGA 4 IV 6.3) — for
    every object `X` and every covering sieve `R ∈ J X`, every element
    `x : Φ.fiber.obj X` comes from an element of the fiber above a covering
    arrow: `∃ Y f, R.arrows f ∧ ∃ y, Φ.fiber.map f y = x`. This is what
    links the topology to the fiber functor — without it, the fiber
    functor would not "see" coverings. Type-sig re-export of the field
    `GrothendieckTopology.Point.jointly_surjective`. -/
def jointly_surjective_field {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (Φ : GrothendieckTopology.Point.{w} J) :
    ∀ {X : C}, ∀ R ∈ J X, ∀ x : Φ.fiber.obj X,
      ∃ (Y : C) (f : Y ⟶ X), ∃ (_ : R.arrows f), ∃ y : Φ.fiber.obj Y,
        Φ.fiber.map f y = x :=
  Φ.jointly_surjective

end Grothendieck_en
