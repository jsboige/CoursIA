/-
Grothendieck tribute — Part 4: Mathlib Map
Alexandre Grothendieck (1928-2014).

A living index of what Mathlib 4 provides from Grothendieck's mathematical
language. Each `#check` verifies that the definition exists and is accessible
from the current imports.

Epic #1646. All `sorry`s eliminated at creation.
-/

import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.Sheaves.Sheaf

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

open AlgebraicGeometry CategoryTheory

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
## What Mathlib does NOT have yet (as of 2026-05)

The following are foundational Grothendieck concepts NOT yet in Mathlib:
  - Etale cohomology (site etale, l-adic cohomology)
  - Motives (pure motives, Voevodsky's DM category)
  - Six operations (Grothendieck's formalism)
  - Grothendieck-Riemann-Roch
  - Grothendieck duality
  - Crystalline cohomology
  - Anabelian geometry
  - Deep EGA/SGA results (EGA II-IV, SGA 1-7)

These remain research-grade formalization targets.
-/
