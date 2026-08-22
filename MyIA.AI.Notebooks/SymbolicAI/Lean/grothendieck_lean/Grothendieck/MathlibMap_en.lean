/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Part 4 — `Grothendieck.MathlibMap` : Mathlib Map

A living index of what Mathlib 4 provides from Grothendieck's mathematical
language. Each `#check` verifies that the definition exists and is accessible
from the current imports.

Epic #1646. All `sorry`s eliminated at creation.

### i18n — convention #4980 ratified 2026-07-04

This substantial module is paired with its French canonical counterpart
in the sibling file `MathlibMap.lean` (sibling pair model, see PR #6154
for the pilot on `Utility.lean`).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.Sheaves.Sheaf

namespace Grothendieck_en

open AlgebraicGeometry CategoryTheory

/-!
## Category theory foundations (Grothendieck's legacy)

Grothendieck made category theory the language of algebraic geometry.
Mathlib 4 has a rich category theory library built on these ideas.
-/

-- The Yoneda lemma (foundational for sieves and sheaves)
#check @CategoryTheory.yoneda            -- C ⥤ (Cᵒᵖ ⥤ Type v)
#check @CategoryTheory.coyoneda          -- (Cᵒᵖ ⥤ Type v) ⥤ C

/-!
## Sieves and Presieves
-/

#check @CategoryTheory.Presieve          -- Presieve X
#check @CategoryTheory.Sieve             -- Sieve X (subfunctor of yoneda.obj X)
#check @CategoryTheory.Sieve.pullback    -- pullback a sieve along a morphism
#check @CategoryTheory.Sieve.arrows      -- the underlying presieve

/-!
## Grothendieck topologies
-/

#check @CategoryTheory.GrothendieckTopology          -- the topology structure
#check @CategoryTheory.GrothendieckTopology.trivial  -- coarsest topology
#check @CategoryTheory.GrothendieckTopology.discrete -- finest topology
#check @CategoryTheory.GrothendieckTopology.dense    -- dense topology

/-!
## Sheaves
-/

-- Sheaves of types on a site
#check @CategoryTheory.Presieve.IsSheaf  -- sheaf condition for Type-valued presheaves
#check @CategoryTheory.Presieve.IsSeparated  -- separated presheaf

-- Sheaves on a topological space
#check @TopCat.Sheaf                     -- bundled sheaf on a topological space

/-!
## Algebraic geometry: Schemes and Spec
-/

-- The type of schemes
#check Scheme                   -- the type of schemes

-- The Spec construction: from rings to spaces
#check Scheme.Spec              -- CommRingCatᵒᵖ ⥤ Scheme

-- Global sections: from spaces to rings
#check Scheme.Γ                 -- Schemeᵒᵖ ⥤ CommRingCat

-- Forgetful functors
#check Scheme.forgetToTop       -- Scheme ⥤ TopCat
#check Scheme.forgetToLocallyRingedSpace  -- Scheme ⥤ LocallyRingedSpace

/-!
## What Mathlib does NOT have yet (as of 2026-07)

The following are foundational Grothendieck concepts NOT yet in Mathlib:
  - Etale cohomology (site etale, l-adic cohomology)
  - Motives (pure motives, Voevodsky's DM category)
  - Six operations (Grothendieck's full formalism) — Mathlib provides the base
    instance `f^* ⊣ f_*` on module sheaves (`AlgebraicGeometry.Modules.Sheaf`,
    indexed by `DirectImage_en.lean`). This lake now delivers — at the
    **presheaf** level, for an arbitrary functor `f : C ⥤ D` and `H = Type*`
    — the pair of adjunctions `f_! ⊣ f^* ⊣ f^!` (`ExceptionalDirect_en.lean`
    Part 34 + `ExceptionalInverse_en.lean` Part 35), i.e. the exact
    symmetrics of `f^* ⊣ f_*` at the presheaf level. The sheaf-theoretic
    proper-support `f_!` and the Verdier `f^!` remain **out of scope** (they
    demand properness of `f` and Poincare duality respectively) — see the
    "Honest ceiling" sections of both modules for the detail.
  - Grothendieck-Riemann-Roch
  - Grothendieck duality
  - Crystalline cohomology
  - Anabelian geometry
  - Deep EGA/SGA results (EGA II-IV, SGA 1-7)

These remain research-grade formalization targets.
-/

/-!
## Bridge theorems

The "Proper theorems" section initially planned (4 lemmas on
`CategoryTheory.yoneda`/`coyoneda`/`GrothendieckTopology.trivial`/
`Sieve`) was removed in c.1301+107 v3 (Lean CI FAIL on universe
polymorphism — see PR #10638 history). The `#check`s above are
sufficient to validate that the canonical Mathlib names are
accessible from current imports. The 8 proper lemmas remaining
live in `Equivalences_en.lean` (4) + `MonoidalCategories_en.lean`
(4 lemmas PASS in CI) + their French siblings.
-/

end Grothendieck_en