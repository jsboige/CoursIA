/-
Grothendieck Part 19 -- Conservative families of points

Part 18 (ConstantSheaf.lean) introduced the constant sheaf functor and its
adjunction with global sections.

This module introduces **conservative families of points** (SGA 4 IV 6.5):
a family P of points of a site (C, J) is conservative if the corresponding
fiber functors Sheaf J (Type w) ⥤ Type w jointly reflect isomorphisms.
This is the abstract formulation of the principle that "enough points detect
everything" -- the categorical generalization of "enough stalks detect
isomorphisms/monos/epis".

Key constructions bridged from Mathlib (`CategoryTheory.Sites.Point.Conservative`):

  - `ObjectProperty.IsConservativeFamilyOfPoints` : the core structure
  - `jointlyReflectIsomorphisms` : fiber functors jointly reflect isos (general A)
  - `jointlyReflectMonomorphisms` : fiber functors jointly reflect monos
  - `jointlyReflectEpimorphisms` : fiber functors jointly reflect epis
  - `jointlyFaithful` : fiber functors are jointly faithful
  - `mk'` : constructor via covering sieve condition (SGA 4 IV 6.5 (a))
  - `jointly_reflect_ofArrows_mem` : detection of covering sieves via points
  - `GrothendieckTopology.HasEnoughPoints` : site has enough points

Plus skyscraper sheaves from `CategoryTheory.Sites.Point.Skyscraper`:
  - `skyscraperPresheaf` / `skyscraperSheaf` : skyscraper constructions
  - `skyscraperSheafAdjunction` : fiber ⊣ skyscraper adjunction
  - `presheafToSheafCompSheafFiberIso` : fiber as localization

This is a key ingredient for understanding when a topos has "enough points"
and for the theory of stalkwise detection of morphism properties.

Epic #1646, See #2159. All `sorry`s eliminated at creation.
-/

import Mathlib.CategoryTheory.Sites.Point.Conservative

universe v v' u u' w

namespace Grothendieck.Conservative

open CategoryTheory Category Opposite Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (P : ObjectProperty (GrothendieckTopology.Point.{w} J))

/-! ## 1. Conservative families of points

A family P of points is "conservative" if the fiber functors
`Sheaf J (Type w) ⥤ Type w` corresponding to the points in P
jointly reflect isomorphisms. This is `ObjectProperty.IsConservativeFamilyOfPoints`
from Mathlib, tagged as Stacks 00YK (1).

Intuitively: a morphism f : F ⟶ G between sheaves is an iso iff
it induces an iso on every stalk (fiber) at every point in P.
-/

-- A conservative family of points: fiber functors jointly reflect isomorphisms.
#check @ObjectProperty.IsConservativeFamilyOfPoints

/-! ## 2. Consequences for general coefficient categories

When the coefficient category A has suitable properties (concrete, AB5, etc.),
conservativity implies that the fiber functors Sheaf J A ⥤ A jointly
reflect isomorphisms, monomorphisms, and epimorphisms, and are jointly faithful.
-/

-- Fiber functors jointly reflect isomorphisms (general A).
#check @ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectIsomorphisms

-- Fiber functors jointly reflect monomorphisms (AB5 coefficient category).
#check @ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectMonomorphisms

-- Fiber functors jointly reflect epimorphisms (with sheafify + products).
#check @ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectEpimorphisms

-- Fiber functors are jointly faithful.
#check @ObjectProperty.IsConservativeFamilyOfPoints.jointlyFaithful

/-! ## 3. Detection via covering sieves (SGA 4 IV 6.5 (a))

The constructor `mk'` shows that P is a conservative family if:
for any sieve S on X, if for every point Phi in P the maps in S
are jointly surjective on fibers, then S is J-covering.

This is the practical criterion: to check conservativity, verify
the covering sieve condition pointwise.
-/

-- Constructor: conservative family via covering sieve condition.
#check @ObjectProperty.IsConservativeFamilyOfPoints.mk'

/-! ## 4. Detection of covering sieves via points

When P is conservative, a family of arrows {f_i : U_i ⟶ X} covers X
(ie. generates a J-covering sieve) iff for every point Phi in P
and every x in the fiber of X, some f_i hits x.
-/

-- Covering sieves detected via fiberwise joint surjectivity.
#check @ObjectProperty.IsConservativeFamilyOfPoints.jointly_reflect_ofArrows_mem

-- Variant for small families of points.
#check @ObjectProperty.IsConservativeFamilyOfPoints.jointly_reflect_ofArrows_mem_of_small

/-! ## 5. Local surjectivity detection

A morphism of presheaves is locally surjective iff it is surjective
on fibers at every point in a conservative family.
-/

-- Local surjectivity detected fiberwise via conservative family.
#check @ObjectProperty.IsConservativeFamilyOfPoints.jointly_reflect_isLocallySurjective

/-! ## 6. W iff iso on all fibers

For a morphism f : F ⟶ G of presheaves, f belongs to J.W (the class
of morphisms inverted by sheafification) iff f induces an iso on
fibers at every point in the conservative family.
-/

-- J.W membership detected fiberwise.
#check @ObjectProperty.IsConservativeFamilyOfPoints.W_iff

/-! ## 7. HasEnoughPoints

A site (C, J) "has enough points" if there exists a small conservative
family of points. This is the condition ensuring that stalkwise reasoning
is complete: everything detectable stalkwise is true.
-/

-- A site has enough points if there exists a small conservative family.
#check @GrothendieckTopology.HasEnoughPoints

/-! ## 8. Skyscraper sheaves and the fiber-skyscraper adjunction

Given a point Phi and an object M : A, the skyscraper sheaf at M
(with respect to Phi) is the sheaf that sends X : C to the product
of copies of M indexed by Phi.fiber.obj X. The skyscraper sheaf
functor is right adjoint to the sheaf fiber functor:

  Phi.sheafFiber ⊣ Phi.skyscraperSheafFunctor
-/

-- The skyscraper presheaf functor.
#check @GrothendieckTopology.Point.skyscraperPresheafFunctor

-- The skyscraper presheaf with value M.
#check @GrothendieckTopology.Point.skyscraperPresheaf

-- The skyscraper presheaf is a sheaf.
#check @GrothendieckTopology.Point.isSheaf_skyscraperPresheaf

-- The skyscraper sheaf functor: A ⥤ Sheaf J A.
#check @GrothendieckTopology.Point.skyscraperSheafFunctor

-- The skyscraper sheaf with value M.
#check @GrothendieckTopology.Point.skyscraperSheaf

-- The adjunction: fiber functor ⊣ skyscraper sheaf functor (presheaf level).
#check @GrothendieckTopology.Point.skyscraperPresheafAdjunction

-- The adjunction: fiber functor ⊣ skyscraper sheaf functor (sheaf level).
#check @GrothendieckTopology.Point.skyscraperSheafAdjunction

/-! ## 9. Fiber functor as localization

The fiber functor on sheaves is obtained from the fiber functor on presheaves
by localization with respect to J.W. The isomorphism
`presheafToSheafCompSheafFiberIso` witnesses this.
-/

-- The fiber functor on sheaves as a localization of the presheaf fiber.
#check @GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso

-- J.W is inverted by the presheaf fiber functor.
#check @GrothendieckTopology.Point.W_isInvertedBy_presheafFiber

/-! ## 10. Bridge theorems

Bridge theorems connecting conservative families to concrete verification.
-/

/-- Bridge theorem: when P is a conservative family of points, the fiber
    functors at points in P jointly reflect isomorphisms for sheaves with
    values in a general category A (given suitable assumptions on A).
    This is the primary consequence of conservativity. -/
theorem jointly_reflect_iso_bridge {A : Type u'} [Category.{v'} A]
    [LocallySmall.{w} C] [HasColimitsOfSize.{w, w} A]
    {FC : A → A → Type*} {CC : A → Type w}
    [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory.{w} A FC]
    [(forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{w, w} (forget A)]
    [J.HasSheafCompose (forget A)]
    (hP : P.IsConservativeFamilyOfPoints) :
    JointlyReflectIsomorphisms
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := A)) :=
  hP.jointlyReflectIsomorphisms A

/-- Bridge theorem: a conservative family of points makes the fiber functors
    jointly faithful. This means: if two morphisms agree on all stalks
    (fibers at all points in P), they are equal. -/
theorem jointly_faithful_bridge {A : Type u'} [Category.{v'} A]
    [LocallySmall.{w} C] [HasColimitsOfSize.{w, w} A]
    {FC : A → A → Type*} {CC : A → Type w}
    [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory.{w} A FC]
    [(forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{w, w} (forget A)]
    [J.HasSheafCompose (forget A)]
    [AB5OfSize.{w, w} A] [HasFiniteLimits A]
    (hP : P.IsConservativeFamilyOfPoints) :
    JointlyFaithful
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := A)) :=
  hP.jointlyFaithful A

/-- Bridge construction: the skyscraper sheaf adjunction for a point Phi.
    Phi.sheafFiber is left adjoint to Phi.skyscraperSheafFunctor. -/
noncomputable def skyscraper_adjunction_bridge {A : Type u'} [Category.{v'} A]
    [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    (Φ : GrothendieckTopology.Point.{w} J) :
    Φ.sheafFiber (A := A) ⊣ Φ.skyscraperSheafFunctor :=
  Φ.skyscraperSheafAdjunction

end Grothendieck.Conservative
