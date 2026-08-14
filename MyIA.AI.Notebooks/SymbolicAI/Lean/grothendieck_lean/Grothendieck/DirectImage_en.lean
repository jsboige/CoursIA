/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Grothendieck tribute — Part 33: Direct image and inverse image of sheaves

Phase 5 extension (#2159, Epic #1646).

Parts 1-29 established the foundations: categories, sieves, topologies, lattice
laws, pullback identities, sheaf bases, covering closure, calibration,
subcanonicality, dense topologies, sheaves, internal hom, Cech cohomology,
Mayer-Vietoris limit.

This module introduces the **direct image / inverse image** pair of sheaves of
modules on schemes: for a scheme morphism `f : X ⟶ Y`, the **direct image**
functor `f_* : X.Modules ⥤ Y.Modules` (pushforward) and the **inverse image**
functor `f^* : Y.Modules ⥤ X.Modules` (pullback), tied by the **fundamental
adjunction `f^* ⊣ f_*`**.

This adjunction is the cornerstone of sheaf transport along morphisms in
algebraic geometry: it is the simplest instance of Grothendieck's "six
operations" formalism (SGA 4, SGA 5). It states that morphisms of sheaves of
modules `f^* G ⟶ M` (on X) are in natural bijection with morphisms `G ⟶ f_* M`
(on Y).

Key constructions bridged from Mathlib (`AlgebraicGeometry.Modules.Sheaf`):

  - `Scheme.Modules X`        : the abelian category of `𝒪ₓ`-modules on a scheme X
  - `pushforward f`           : the direct image functor `f_* : X.Modules ⥤ Y.Modules`
  - `pullback f`              : the inverse image functor `f^* : Y.Modules ⥤ X.Modules`
  - `pullbackPushforwardAdjunction f` : the adjunction `f^* ⊣ f_*`
  - `pushforwardId X`         : `f_*` along the identity identifies to the identity functor
  - `pushforwardComp f g`     : `f_*` then `g_*` identifies to `(g ∘ f)_*`
  - `pullbackId X`, `pullbackComp f g` : the analogues for `f^*`

Epic #1646, Phase 5 (#2159). All `sorry`s eliminated at creation.

### Accessibility note (Epics #1452/#1453)

This module exposes **8 `#check` verifications** on the direct image / inverse
image pair, organised into 6 thematic sections: (1) the category of `𝒪ₓ`-modules
on a scheme, (2) the direct image `f_*`, (3) the inverse image `f^*`, (4) the
fundamental adjunction `f^* ⊣ f_*`, (5) the functoriality identities of the
direct image `f_*` (identity, composition), (6) the functoriality identities of
the inverse image `f^*` (dual analogue).

### i18n — convention #4980 ratified 2026-07-04

This substantial module is paired with its French canonical counterpart in the
sibling file `DirectImage.lean` (sibling pair model, see PR #6154 for the pilot
on `Utility.lean` and #6275/#6277/#6280/#6284 for the rollout continuation).
Namespace suffix `_en` applied to the EN file (anti-collision, per code-style.md
#4980). The `#check`s, signatures, variables and universes are **byte-identical**
between the two files; only the docstrings `/-- ... -/` and comments `-- ...`
differ.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf

universe u

namespace Grothendieck.DirectImage_en

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme (Modules)
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules (pullbackId pullbackComp)

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-!
## Section 1: The category of sheaves of modules on a scheme

For a scheme `X`, the type `X.Modules` is the abelian category of sheaves of
modules over the structure sheaf `𝒪ₓ`. This is the natural setting where the
direct and inverse image live: they are functors between such categories,
parametrised by a scheme morphism `f : X ⟶ Y`.
-/

-- The category of 𝒪ₓ-modules on a scheme X (abelian category).
#check (Scheme.Modules X : Type _)

/-!
## Section 2: The direct image (pushforward, `f_*`)

For a scheme morphism `f : X ⟶ Y`, the **direct image** `f_*` sends an
`𝒪ₓ`-module `M` to the `𝒪_Y`-module `f_* M` whose sections over an open set
`U` of `Y` are the sections of `M` over the preimage `f ⁻¹ᵁ U`.

This is the natural way to *push forward* a sheaf along `f`.
-/

-- The direct image functor f_* : from 𝒪ₓ-modules to 𝒪_Y-modules.
#check (pushforward f : X.Modules ⥤ Y.Modules)

/-!
## Section 3: The inverse image (pullback, `f^*`)

The **inverse image** `f^*` is the left adjoint of `f_*`: it *pulls back* a
`𝒪_Y`-module to `X`. Geometrically, `f^* G` represents the sheaf `G` seen on
the source space `X` via the morphism `f`.
-/

-- The inverse image functor f^* : from 𝒪_Y-modules to 𝒪ₓ-modules.
#check (pullback f : Y.Modules ⥤ X.Modules)

/-!
## Section 4: The fundamental adjunction `f^* ⊣ f_*`

The central result: the inverse image is left adjoint to the direct image.
Morphisms of `𝒪ₓ`-modules `f^* G ⟶ M` are in natural correspondence with
morphisms of `𝒪_Y`-modules `G ⟶ f_* M`. This adjunction is the heart of sheaf
transport in algebraic geometry and the simplest ancestor of Grothendieck's six
operations formalism.
-/

-- The fundamental adjunction: f^* is left adjoint to f_*.
#check (pullbackPushforwardAdjunction f : pullback f ⊣ pushforward f)

/-!
## Section 5: Functoriality identities of the direct image `f_*`

The direct image `f_*` behaves well with respect to identity and composition of
scheme morphisms: pushing forward along the identity is the identity, and
pushing forward along `f` then `g` identifies to the pushforward along the
composite `f ≫ g`.
-/

-- f_* along the identity identifies to the identity functor.
#check (pushforwardId X : pushforward (𝟙 X) ≅ 𝟭 _)

-- f_* then g_* identifies to the pushforward of the composite (f ≫ g)_*.
#check (pushforwardComp f g : pushforward f ⋙ pushforward g ≅ pushforward (f ≫ g))

/-!
## Section 6: Functoriality identities of the inverse image `f^*`

The inverse image `f^*` satisfies the dual identities: pulling back along the
identity is the identity, and pulling back along `f ≫ g` identifies to pulling
back along `g` then `f` (note the reversed order: `pullback g ⋙ pullback f`,
since `f^*` is contravariant in `f`).
-/

-- f^* along the identity identifies to the identity functor.
#check pullbackId X

-- f^* of the composite: pullback g then pullback f = pullback (f ≫ g) (reversed order, contravariance).
#check pullbackComp f g

/-!
## Section 7: Bridge theorems: functorial law on pushforward and pullback

The functors `pushforward f` and `pullback f` are full-fledged `Functor`s:
they preserve identities and composition (the `Functor.map_id` and
`Functor.map_comp` fields of the structure). The 4 bridges below join
the module's definitions with the underlying Mathlib 4 facts:

  - `pushforward_map_id` / `pushforward_map_comp`: structure fields of
    the `pushforward f` functor (direct access
    `(pushforward f).map_id X` / `(pushforward f).map_comp f g`).
  - `pullback_map_id` / `pullback_map_comp`: symmetric structure fields
    of the `pullback f` functor.

For `Functor` structure fields (L902 ★★ Tier 5), direct application
`(F).map_id X` / `(F).map_comp f g` is the canonical idiom (not
`by rw [Functor.map_id]`, which defeats the LHS but doesn't close the
goal on Type equality, nor `rfl`, which is PROVABLE only for
definitional equalities).
-/

/-- Bridge: the `pushforward f` functor preserves identities. This is the
    `Functor.map_id` structure field, directly accessible. -/
theorem pushforward_map_id {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) :
    (pushforward f).map (𝟙 M) = 𝟙 ((pushforward f).obj M) :=
  (pushforward f).map_id M

/-- Bridge: the `pushforward f` functor preserves composition of morphisms.
    Structure field `Functor.map_comp`. -/
theorem pushforward_map_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) :
    (pushforward f).map (φ ≫ ψ) =
      (pushforward f).map φ ≫ (pushforward f).map ψ :=
  (pushforward f).map_comp φ ψ

/-- Bridge: the `pullback f` functor preserves identities. Structure field
    `Functor.map_id`. Dual of `pushforward_map_id`. -/
theorem pullback_map_id {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Y.Modules) :
    (pullback f : Y.Modules ⥤ X.Modules).map (𝟙 G) =
      𝟙 ((pullback f : Y.Modules ⥤ X.Modules).obj G) :=
  (pullback f : Y.Modules ⥤ X.Modules).map_id G

/-- Bridge: the `pullback f` functor preserves composition of morphisms.
    Structure field `Functor.map_comp`. Dual of `pushforward_map_comp`. -/
theorem pullback_map_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    {G H K : Y.Modules} (φ : G ⟶ H) (ψ : H ⟶ K) :
    (pullback f : Y.Modules ⥤ X.Modules).map (φ ≫ ψ) =
      (pullback f : Y.Modules ⥤ X.Modules).map φ ≫
        (pullback f : Y.Modules ⥤ X.Modules).map ψ :=
  (pullback f : Y.Modules ⥤ X.Modules).map_comp φ ψ


/-- Bridge: the identity morphism of the category `X.Modules` applied to
    sections equals the identity of the section ring. This is Mathlib 4's
    `AlgebraicGeometry.Scheme.Modules.Hom.id_app` lemma:
    `((𝟙 M : M ⟶ N).app U = 𝟙 _)`. -/

theorem id_app_field (X : Scheme.{u}) (M : X.Modules) (U : X.Opens) :
    (𝟙 M : M ⟶ M).app U = 𝟙 (Γ(M, U)) :=
  @AlgebraicGeometry.Scheme.Modules.Hom.id_app X U M

/-- Bridge: the composition of morphisms of `X.Modules` is computed
    pointwise as the composition of section morphisms. This is Mathlib 4's
    `Hom.comp_app` lemma: `(φ ≫ ψ).app U = φ.app U ≫ ψ.app U`. -/

theorem comp_app_field (X : Scheme.{u}) {M N K : X.Modules} (φ : M ⟶ N)
    (ψ : N ⟶ K) (U : X.Opens) :
    (φ ≫ ψ).app U = φ.app U ≫ ψ.app U :=
  @AlgebraicGeometry.Scheme.Modules.Hom.comp_app X M N K U φ ψ

/-- Bridge: the addition of morphisms of `X.Modules` is computed
    pointwise as the addition of section morphisms. This is Mathlib 4's
    `Hom.add_app` lemma: `(φ + ψ).app U = φ.app U + ψ.app U`. -/

theorem add_app_field (X : Scheme.{u}) {M N : X.Modules} (φ ψ : M ⟶ N)
    (U : X.Opens) :
    (φ + ψ).app U = φ.app U + ψ.app U :=
  @AlgebraicGeometry.Scheme.Modules.Hom.add_app X M N U φ ψ

/-- Bridge: the scalar action of a structure-sheaf section on a morphism of
    `X.Modules` is computed pointwise. This is Mathlib 4's `Hom.app_smul`
    lemma: `φ.app U (r • x) = r • φ.app U x`. -/

theorem app_smul_field (X : Scheme.{u}) {M N : X.Modules} (φ : M ⟶ N)
    (U : X.Opens) (r : Γ(X, U)) (x : Γ(M, U)) :
    φ.app U (r • x) = r • φ.app U x :=
  @AlgebraicGeometry.Scheme.Modules.Hom.app_smul X M N U φ r x

/-- Bridge: the zero morphism `0 : M ⟶ N` applies to the zero of sections.
    This is Mathlib 4's `Hom.zero_app` lemma:
    `(0 : M ⟶ N).app U = 0`. -/

theorem zero_app_field (X : Scheme.{u}) {M N : X.Modules} (U : X.Opens) :
    (0 : M ⟶ N).app U = 0 :=
  @AlgebraicGeometry.Scheme.Modules.Hom.zero_app X M N U

/-- Bridge: a morphism of `X.Modules` is an isomorphism iff its
    components on each open set are isomorphisms of section rings. This is
    Mathlib 4's `Hom.isIso_iff_isIso_app` lemma:
    `IsIso φ ↔ ∀ U, IsIso (φ.app U)`. -/

theorem isIso_iff_isIso_app_field (X : Scheme.{u}) {M N : X.Modules}
    (φ : M ⟶ N) :
    IsIso φ ↔ ∀ (U : X.Opens), IsIso (φ.app U) :=
  @AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_app X M N φ

end Grothendieck.DirectImage_en
