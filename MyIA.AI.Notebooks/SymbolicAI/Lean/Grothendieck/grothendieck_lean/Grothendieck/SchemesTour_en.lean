/-
Grothendieck tribute — Part 2: Schemes
Alexandre Grothendieck (1928-2014).

Grothendieck's most transformative idea: replace varieties by *schemes* — locally
ringed spaces that are locally affine (isomorphic to Spec R for a commutative ring R).
This gives a single framework for arithmetic and geometry.

Mathlib 4 formalizes schemes as `AlgebraicGeometry.Scheme`, extending
`LocallyRingedSpace` with the local-affineness condition.

Epic #1646. All `sorry`s eliminated at creation.

### i18n — convention #4980 ratified 2026-07-04

This module is paired with its French canonical version in the sibling file
`SchemesTour.lean` (sibling pair model, see PR #6154 on `Utility.lean`).
Only **docstrings `/-- ... -/`** and **comments `-- ...`** differ between the
two files; theorem statements, lemma names, Lean tactics and Mathlib
references stay in English (Mathlib 4, standard tactic DSL).
Anti-§D byte-identity guaranteed: signatures and proof bodies are
byte-identical between `SchemesTour_en.lean` and `SchemesTour.lean`.

Sub-grain Phase 2+ (#2159, Epic #1646) — c.8267+3: 6 reusable Mathlib
bridges inside the `Grothendieck_en` namespace (homogeneity with other
Grothendieck modules: `SitePoints`, `SheafBasics`, `MayerVietorisSquare`,
`Adjunction`, `Limits`, `KanExtensions`). Replaces the pedagogical
`example`s with canonical bridges.
-/

import Mathlib.AlgebraicGeometry.Scheme

namespace Grothendieck_en

open AlgebraicGeometry CategoryTheory

/-!
## The type of schemes

`Scheme` is the type of schemes. It carries a category structure.
Every scheme has an underlying locally ringed space, topological space, and
presheaf of commutative rings.
-/

-- The type of schemes
#check @AlgebraicGeometry.Scheme

-- The forgetful functor from schemes to topological spaces
#check @Scheme.forgetToTop

/-!
## Spec: from rings to spaces

The Spec construction turns a commutative ring into an affine scheme.
It is the left adjoint to the global sections functor Γ.
-/

/-- Spec is a functor from CommRingCatᵒᵖ to Scheme.
    Marked `noncomputable` because `Scheme.Spec` is noncomputable. -/
noncomputable example : CommRingCatᵒᵖ ⥤ Scheme := Scheme.Spec

/-!
## Basic properties

Schemes have an order structure from specialization, and morphisms
between schemes respect the sheaf structure.
-/

/-- An isomorphism of schemes induces a homeomorphism of underlying spaces.
    Note: `Scheme.homeoOfIso` returns `X ≃ₜ Y` (carriers). -/
noncomputable example {X Y : Scheme} (i : X ≅ Y) : X ≃ₜ Y :=
  Scheme.homeoOfIso i

-- The forgetful functor from schemes to locally ringed spaces (fully faithful)
#check @Scheme.forgetToLocallyRingedSpace

-- The FullyFaithful type for the forgetful functor
#check Scheme.forgetToLocallyRingedSpace.FullyFaithful

/-!
## The big picture: from rings to spaces and back

The Spec-Γ adjunction is the heart of algebraic geometry:
  - Spec : CommRingCatᵒᵖ → Scheme  (ring to space)
  - Γ     : Schemeᵒᵖ → CommRingCat  (space to ring, global sections)

For affine schemes, these are inverse equivalences.
-/

/-- Every scheme has global sections (the ring Γ(X)).
    Note: `Scheme.Γ` has domain `Schemeᵒᵖ`. -/
example (X : Scheme) : CommRingCat :=
  Scheme.Γ.obj (Opposite.op X)

/-!
## Canonical Mathlib bridges

The following bridges re-expose, from inside the `Grothendieck_en` namespace,
lemmas from Mathlib 4 (`Mathlib.AlgebraicGeometry.Scheme`,
`Mathlib.AlgebraicGeometry.Spec`). They serve two purposes:

  1. **Pedagogical reference**: a learner reading the `Grothendieck_en`
     namespace finds the canonical statements of schemes without having
     to navigate the `Mathlib.AlgebraicGeometry.*` hierarchy.
  2. **In-module reuse**: sibling modules (`Subcanonical`, `ZariskiSite`,
     `Calibration`, `MathlibMap`) can cite these bridges instead of
     repeating the `AlgebraicGeometry.Scheme.*` qualification.

The bodies are trivial (`@[simp]` lemmas or `rfl` in Mathlib) — the value
is **referencing**, not computation.
-/

/-- **Continuity of a scheme morphism.** A scheme morphism `f : X ⟶ Y`
    is continuous (between the underlying topological spaces):
    `f : X ⟶ Y` ⇒ `Continuous f` — this is precisely the definition of a
    scheme morphism viewed as a continuous map between the underlying
    `TopCat`. -/
theorem scheme_hom_continuous {X Y : Scheme} (f : X ⟶ Y) : Continuous f :=
  Scheme.Hom.continuous f

/-- **Symmetry of the induced homeomorphism.** If `e : X ≅ Y` is a scheme
    isomorphism, then the inverse of the homeomorphism
    `homeoOfIso e : X ≃ₜ Y` coincides with the homeomorphism built from
    `e.symm`. This is the canonical symmetric coherence of
    `Scheme.homeoOfIso`. -/
theorem scheme_homeoOfIso_symm {X Y : Scheme} (e : X ≅ Y) :
    (Scheme.homeoOfIso e).symm = Scheme.homeoOfIso e.symm :=
  Scheme.homeoOfIso_symm e

/-- **Coefficient of the symm of the homeomorphism.** Applying the
    homeomorphism built from `e.symm` to a point `x` gives back
    `e.inv x`, i.e. the image under the forgetful functor to `TopCat` of
    the inverse of the isomorphism `e`. -/
theorem scheme_coe_homeoOfIso_symm {X Y : Scheme} (e : X ≅ Y) :
    ⇑(Scheme.homeoOfIso e.symm) = e.inv :=
  Scheme.coe_homeoOfIso_symm e

/-- **Composition of forgetful functors.** The forgetful functor
    `Scheme → TopCat` followed by `TopCat → Type` coincides with the
    direct forgetful functor `Scheme → Type` defined as `Scheme.forget`.
    This is the coherence of the two forgetful paths to `Type u`. -/
theorem scheme_forgetToTop_comp_forget :
    Scheme.forgetToTop ⋙ CategoryTheory.forget TopCat = Scheme.forget :=
  Scheme.forgetToTop_comp_forget

/-- **Compatibility of the preimage with composition.** The preimage of
    an open set `U` under a composed morphism `f ≫ g` coincides with
    the preimage of the preimage: `(f ≫ g)⁻¹ᵁ U = f⁻¹ᵁ (g⁻¹ᵁ U)`. -/
theorem scheme_comp_preimage {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) :
    (f ≫ g) ⁻¹ᵁ U = f ⁻¹ᵁ (g ⁻¹ᵁ U) :=
  Scheme.Hom.comp_preimage f g U

/-- **Identity of the Spec functor on objects.** The scheme morphism
    `Spec.topMap (𝟙 R)` coincides with the identity on `Spec R` — this
    is the identity law of the Spec functor (in its `Spec.toTop` component,
    `CommRingCatᵒᵖ → TopCat`). -/
theorem spec_topMap_id (R : CommRingCat) :
    Spec.topMap (𝟙 R) = 𝟙 (Spec.topObj R) :=
  Spec.topMap_id R

end Grothendieck_en
