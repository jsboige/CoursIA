/-
Grothendieck tribute — Part 2: Schemes
Alexandre Grothendieck (1928-2014).

Grothendieck's most transformative idea: replace varieties by *schemes* — locally
ringed spaces that are locally affine (isomorphic to Spec R for a commutative ring R).
This gives a single framework for arithmetic and geometry.

Mathlib 4 formalizes schemes as `AlgebraicGeometry.Scheme`, extending
`LocallyRingedSpace` with the local-affineness condition.

Epic #1646. All `sorry`s eliminated at creation.
-/

import Mathlib.AlgebraicGeometry.Scheme

namespace Grothendieck

open AlgebraicGeometry

/-!
## The type of schemes

`Scheme` is the type of schemes. It carries a category structure.
Every scheme has an underlying locally ringed space, topological space, and
presheaf of commutative rings.
-/

/-- Schemes form a category. -/
example : Category Scheme := inferInstance

/-- Every scheme has an underlying topological space. -/
example (X : Scheme) : TopCat :=
  X.toLocallyRingedSpace.toSheafedSpace.toPresheafedSpace.1.1

/-- The structure sheaf of a scheme is a sheaf of commutative rings. -/
example (X : Scheme) :
    X.toLocallyRingedSpace.toSheafedSpace.1 :=
  X.toLocallyRingedSpace.toSheafedSpace.val

/-!
## Spec: from rings to spaces

The Spec construction turns a commutative ring into an affine scheme.
It is the left adjoint to the global sections functor Γ.
-/

/-- Spec is a functor from (CommRingCat)ᵒᵖ to Scheme. -/
example : CommRingCatᵒᵖ ⥤ Scheme := Scheme.Spec

/-!
## Basic properties

Schemes have an order structure from specialization, and morphisms
between schemes respect the sheaf structure.
-/

/-- An isomorphism of schemes induces a homeomorphism of underlying spaces. -/
example {X Y : Scheme} (i : X ≅ Y) : X.1.1.1.1 ≃ₜ Y.1.1.1.1 :=
  Scheme.homeoOfIso i

/-- The forgetful functor from schemes to locally ringed spaces is fully faithful. -/
example : Scheme.forgetToLocallyRingedSpace.FullyFaithful :=
  Scheme.forgetToLocallyRingedSpace.fullyFaithful

/-!
## The big picture: from rings to spaces and back

The Spec-Γ adjunction is the heart of algebraic geometry:
  - Spec : CommRingCatᵒᵖ → Scheme  (ring to space)
  - Γ     : Scheme → CommRingCatᵒᵖ  (space to ring, global sections)

For affine schemes, these are inverse equivalences.
-/

/-- Every scheme has global sections (the ring Γ(X, ⊤)). -/
example (X : Scheme) : CommRingCat :=
  Scheme.Γ.obj (Opposite.op X)

end Grothendieck
