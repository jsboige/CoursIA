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
`CategoryTheory.Sites.Point.Category` into the `Grothendieck` namespace.

Epic #1646, Phase 9 (#2159). All `sorry`s eliminated at creation.
-/
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
#check @GrothendieckTopology.Point.sheafFiber

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

end Grothendieck_en

