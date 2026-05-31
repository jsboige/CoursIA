/-
Grothendieck tribute — Part 4: Mathlib Map
Alexandre Grothendieck (1928-2014).

A living index of what Mathlib 4 provides from Grothendieck's mathematical
language. Each `#check` verifies that the definition exists and is accessible
from the current imports.

Epic #1646. All `sorry`s eliminated at creation.
-/

import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.Topology.Sheaves.Sheaf

namespace Grothendieck

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

#check @CategoryTheory.Presieve          -- C → Type _  (set of arrows with codomain X)
#check @CategoryTheory.Sieve             -- subfunctor of yoneda.obj X
#check @CategoryTheory.Sieve.pullback    -- pullback a sieve along a morphism

/-!
## Grothendieck topologies
-/

#check @CategoryTheory.GrothendieckTopology          -- the topology structure
#check @GrothendieckTopology.trivial                  -- coarsest topology
#check @GrothendieckTopology.discrete                 -- finest topology
#check @GrothendieckTopology.dense                    -- dense topology

/-!
## Sheaves
-/

-- Sheaves of types on a site
#check @CategoryTheory.Presieve.IsSheaf  -- sheaf condition for Type-valued presheaves
#check @CategoryTheory.Presieve.IsSeparated  -- separated presheaf

-- Sheaves on a topological space
#check @TopCat.Sheaf                     -- bundled sheaf on a topological space
#check @TopCat.Presheaf.IsSheaf          -- sheaf condition for topological spaces

/-!
## Algebraic geometry: Spec and Schemes
-/

-- The Spec construction
#check @AlgebraicGeometry.Spec           -- CommRingCatᵒᵖ ⥤ Scheme

-- Schemes
#check @AlgebraicGeometry.Scheme         -- the type of schemes
#check @AlgebraicGeometry.Scheme.Spec    -- Spec as a functor to Scheme
#check @AlgebraicGeometry.Scheme.Γ       -- global sections functor

-- Zariski site
#check @AlgebraicGeometry.Scheme.zariskiPretopology  -- the pretopology
#check @AlgebraicGeometry.Scheme.zariskiTopology     -- the Grothendieck topology

/-!
## What Mathlib does NOT have yet (as of 2026-05)

The following are foundational Grothendieck concepts NOT yet in Mathlib:
  - Etale cohomology (site étale, ℓ-adic cohomology)
  - Motives (pure motives, Voevodsky's DM category)
  - Six operations (Grothendieck's formalism)
  - Grothendieck-Riemann-Roch
  - Grothendieck duality
  - Crystalline cohomology
  - Anabelian geometry
  - Deep EGA/SGA results (EGA II-IV, SGA 1-7)

These remain research-grade formalization targets.
-/

end Grothendieck
