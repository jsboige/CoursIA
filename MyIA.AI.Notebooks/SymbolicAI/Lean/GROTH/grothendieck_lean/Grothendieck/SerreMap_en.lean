/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Mirror — `Grothendieck.SerreMap` : the Serre side of the bridge, mapped in Mathlib

A living index of what Mathlib 4 (toolchain v4.33.0) provides of the Serre
side of the Serre–Grothendieck common language: Serre classes, localisation,
perfectness, the Serre construction of Lie algebras, the Serre derivative,
the fundamental domain, DVRs. Each `#check` verifies that the definition
exists and is accessible from the current imports; each `example`
instantiates a theorem on a concrete case. The final section lists, in the
spirit of `Grothendieck.MathlibMap_en`, what Mathlib does NOT have yet.

Epic #16334 (grain 9, decorrelated track). No `sorry` at creation.

### i18n — convention #4980 ratified 2026-07-04

This module is paired with its French canonical counterpart in the sibling
file `SerreMap.lean` (sibling pair model). The `#check`/`example` statements
stay in English (Mathlib 4, standard tactic DSL); only the **docstrings
`/- ... -/`** and the **comments `-- ...`** differ between the two files.
Anti-§D byte-identity guaranteed: the statements are identical between
`SerreMap_en.lean` and `SerreMap.lean`, only the comments differ.
-/

import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
import Mathlib.Algebra.Category.Grp.IsFinite
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.Modular
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.Lie.SerreConstruction

namespace Grothendieck_en

/-!
## Serre classes — the definition and its closure

A Serre class is a class of objects stable under subobjects, quotients and
extensions: the language in which Serre reformulated sheaf cohomology
(FAC, 1955) and which Grothendieck would exploit to localise abelian
categories. Mathlib defines it as an object property in an abelian category,
with the "two-out-of-three" characterisation on short exact sequences.
-/

#check @CategoryTheory.ObjectProperty.IsSerreClass                 -- the class of Serre classes
#check @CategoryTheory.ObjectProperty.prop_iff_of_shortExact  -- two-out-of-three on a short exact sequence
#check @CategoryTheory.ObjectProperty.prop_X₂_of_exact        -- stability through the middle term of an exact sequence

-- (Basic.lean also instantiates the two trivial cases: the universal class ⊤
--  and the class of zero objects IsZero — anonymous instances, resolved by inferInstance)

/-!
### Instantiated example: finite abelian groups

The first historical example (finite abelian groups form a Serre class)
lives in Mathlib as an instance — the mini-proof below is the instance
resolution itself.
-/

#check @AddCommGrpCat.isFinite                                     -- ObjectProperty AddCommGrpCat : finiteness
#check @AddCommGrpCat.prop_isFinite_iff                             -- isFinite M ↔ Finite M

example : (AddCommGrpCat.isFinite : CategoryTheory.ObjectProperty AddCommGrpCat).IsSerreClass := inferInstance

/-!
## Serre localisation and the Serre quotient

Quotienting an abelian category by a Serre class is the founding gesture of
sheaf theory: see only the morphisms whose cone lives in the class. Mathlib
constructs the localised category and proves it abelian; the
Gabriel–Popescu theorem provides the embedding counterpart.
-/

#check @CategoryTheory.ObjectProperty.SerreClassLocalization.abelian -- the localised category is abelian
#check @CategoryTheory.IsGrothendieckAbelian.GabrielPopescu.full    -- the embedding functor is full
#check @CategoryTheory.IsGrothendieckAbelian.GabrielPopescu.preservesFiniteLimits      -- ... and left exact
#check @CategoryTheory.IsGrothendieckAbelian.GabrielPopescu.preservesInjectiveObjects  -- ... and preserves injectives

/-!
## Perfectness in the sense of Serre

A ring of characteristic p is *perfect in the sense of Serre* when Frobenius
is bijective — the definition of *Local Algebra* / *Corps locaux*. Mathlib
carries the definition and the theorem that every finite field is perfect.
-/

#check @PerfectRing            -- perfect ring in Serre's sense (bijective Frobenius)
#check @PerfectRing.toPerfectField -- a Serre-perfect field is a perfect field
#check @PerfectField.ofFinite  -- every finite field is perfect

-- The statement `PerfectField (ZMod 7)` already requires `Field (ZMod 7)`,
-- which requires `Fact (Nat.Prime 7)` (Mathlib idiom, cf.
-- GroupTheory/SpecificGroups/Quaternion.lean).
instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

example : PerfectField (ZMod 7) := PerfectField.ofFinite

/-!
## The Serre construction — Lie algebras and Serre relations

From a Cartan matrix, the Serre construction manufactures the Lie algebra
as a quotient of the free Lie algebra by the Serre relations
([E_i, F_i] = H_i, ad(E_i)^{1-A_ij}(E_j) = 0, etc.) — reference: Serre,
*Complex Semisimple Lie Algebras*, ch. VI, appendix. Mathlib implements
the full construction and derives the exceptional algebras from it.
-/

#check @Matrix.ToLieAlgebra     -- the Lie algebra of a Cartan matrix via the Serre relations
#check @LieAlgebra.e₆           -- the exceptional algebras, built by the Serre construction
#check @LieAlgebra.g₂

/-!
## The Serre derivative — modular forms

The derivative ∂_k = D − (k/12)·E₂· maps M_k into M_{k+2}: the operator
that makes differentiating modular forms compatible with modularity
(*A Course in Arithmetic*, ch. VII). Mathlib provides the full API.
-/

#check @Derivative.serreDerivative            -- ∂_k F = D F − k·12⁻¹·E₂·F
#check @Derivative.serreDerivative_mul        -- the weighted Leibniz rule
#check @Derivative.serreDerivative_mdifferentiable -- ∂_k preserves differentiability

/-!
## The fundamental domain — *A Course in Arithmetic*, ch. VII

The classification of pairs (z ∈ 𝒟, g•z ∈ 𝒟) in the fundamental domain of
SL(2, ℤ) follows Theorem VII.1 of the *Cours d'arithmétique*: it is the key
to the unique representation of modular forms.
-/

#check @ModularGroup.cases_of_mem_fd_smul_mem_fd  -- classification of z, g in the fundamental domain

/-!
## The discrete valuation ring — *Corps locaux*

The definition of a DVR as a principal ring with a unique nonzero prime
ideal is the one from Serre's *Corps locaux*; Mathlib carries it as is.
-/

#check @IsDiscreteValuationRing  -- the definition, in Serre's sense
#check @IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime  -- DVR ⟺ PID with a unique nonzero prime ideal

/-!
## What Mathlib does NOT have yet (state v4.33.0)

The central "Serre theorems" absent from Mathlib at this version:
  - **The R1 + S2 normality criterion** (normal = regular in codim 1 +
    Cohen-Macaulay in codim 2) — absent.
  - **GAGA** (the algebraic/analytic comparison theorems, 1956) — absent.
  - **Serre duality** (for coherent sheaves) — absent.
  - **FAC** (finiteness of coherent sheaf cohomology) — absent: the sheaf
    language lives in this lake, not the finiteness theorems.
  - **Serre's conjecture** (every finitely generated projective module over
    a polynomial ring is free — became Quillen–Suslin) — absent.
  - **The Hochschild–Serre spectral sequence** — explicit TODO in
    `RepresentationTheory/Homological/GroupCohomology/Basic.lean`.
  - **The Serre class of Noetherian objects** — explicit TODO in
    `CategoryTheory/Subobject/NoetherianObject.lean`.
  - **The presentation theorem by Serre relations** (the Lie algebra of a
    root system IS the Serre quotient — the construction exists via Geck,
    the isomorphism is not proved).
-/

end Grothendieck_en
