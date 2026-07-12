/-
Grothendieck tribute — Part 14: Left exactness of sheafification
Alexandre Grothendieck (1928-2014).

Phase 8 extension (#2159, Epic #1646).

Part 13 (Sheafification.lean) introduced the sheafification functor and its
universal property: `presheafToSheaf ⊣ sheafToPresheaf`.

This module records the **exactness properties** of sheafification, following
Mathlib's `CategoryTheory.Sites.LeftExact`:

  - Sheafification preserves finite limits (it is left exact).
  - The plus construction preserves finite limits.
  - Categories of sheaves inherit exactness properties from the target:
    they are finitary extensive, adhesive, and balanced.

These are all instances (typeclass resolution), so our bridge theorems
simply re-expose them in the `Grothendieck` namespace with doc strings
explaining their significance.

Universe note: same as Part 13 — `Type (max u v)` for presheaves on
`C : Type u` with `[Category.{v} C]`, via `HasSheafify J (Type (max u v))`
from LeftExact.lean.

Epic #1646, Phase 8 (#2159). All `sorry`s eliminated at creation.
-/

import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LeftExact

universe v u

namespace Grothendieck

open CategoryTheory
open CategoryTheory.Limits

/-!
## The plus construction preserves finite limits

The "plus construction" `P ↦ P⁺` is the first step of sheafification.
Applying it twice gives the sheafification. That `plusFunctor` preserves
finite limits is the technical heart of left exactness: it means the
construction respects products, equalizers, and pullbacks.

For `Type (max u v)`-valued presheaves, all the required instances
(`HasFiniteLimits`, `PreservesFiniteLimits (forget)`, etc.) are
provided by Mathlib's type-theoretic machinery.
-/

/-- The plus construction `J.plusFunctor` preserves finite limits
    for Type-valued presheaves. This is the key intermediate result:
    sheafification = plus ∘ plus, so if plus preserves finite limits,
    so does sheafification.
    Uses `preserveFiniteLimits_plusFunctor` from Mathlib's LeftExact. -/
instance plus_preserves_finite_limits {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    PreservesFiniteLimits (J.plusFunctor (Type (max u v))) :=
  inferInstance

/-!
## presheafToSheaf preserves finite limits

The concrete sheafification functor `presheafToSheaf` (which goes from
presheaves to sheaves, unlike `sheafification` which is the endofunctor
on presheaves) also preserves finite limits.
-/

/-- The concrete sheafification functor `presheafToSheaf` preserves
    finite limits. This is the version stated for the functor landing
    in the category of sheaves (rather than the endofunctor on presheaves).
    Uses `presheafToSheaf_preservesFiniteLimits` from Mathlib. -/
instance presheaf_to_sheaf_left_exact {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    PreservesFiniteLimits (presheafToSheaf J (Type (max u v))) :=
  inferInstance

/-!
## Categories of sheaves are finitary extensive

A category is **finitary extensive** when pullbacks along coproduct
inclusions exist and the fibration structure is well-behaved. Since
sheafification is a left exact localization, the category of sheaves
inherits finitary extensivity from the target category.

For `Type`-valued sheaves, this means finite coproducts in `Sheaf J`
behave like disjoint unions with well-behaved pullbacks.
-/

/-- The category of Type-valued sheaves on a site is finitary extensive.
    This follows from the reflective localization given by sheafification.
    Uses `SheafOfTypes.finitary_extensive` from Mathlib. -/
instance sheaf_finitary_extensive {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    FinitaryExtensive (Sheaf J (Type (max u v))) :=
  inferInstance

/-!
## Categories of sheaves are adhesive

A category is **adhesive** if it has pullbacks, pushouts along
monomorphisms, and van Kampen colimits. Categories of sheaves on a site
inherit adhesivity from the target via the reflective localization.
-/

/-- The category of Type-valued sheaves on a site is adhesive.
    Uses `SheafOfTypes.adhesive` from Mathlib. -/
instance sheaf_adhesive {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    Adhesive (Sheaf J (Type (max u v))) :=
  inferInstance

/-!
## Categories of sheaves are balanced

A category is **balanced** if every morphism that is both monic and epic
is already an isomorphism. For categories of sheaves of types, this
means a sheaf morphism that is injective and surjective on sections
is necessarily an isomorphism.
-/

/-- The category of Type-valued sheaves on a site is balanced.
    A morphism that is both monic and epic is an isomorphism.
    Uses `SheafOfTypes.balanced` from Mathlib. -/
instance sheaf_balanced {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    Balanced (Sheaf J (Type (max u v))) :=
  inferInstance

end Grothendieck
