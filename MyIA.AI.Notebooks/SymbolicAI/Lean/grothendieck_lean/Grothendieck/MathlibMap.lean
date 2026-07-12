/-
Grothendieck tribute — Part 4: Mathlib Map
Alexandre Grothendieck (1928-2014).

A living index of what Mathlib 4 provides from Grothendieck's mathematical
language. Each `#check` verifies that the definition exists and is accessible
from the current imports.

Epic #1646. All `sorry`s eliminated at creation.
-/

/-
  `Grothendieck.MathlibMap` — Cartographie Mathlib
  ================================================
  Hommage à Grothendieck — Partie 4 : Cartographie Mathlib
  Alexandre Grothendieck (1928-2014).

  Un index vivant de ce que Mathlib 4 fournit depuis le langage mathématique
  de Grothendieck. Chaque `#check` vérifie que la définition existe et est
  accessible depuis les imports courants.

  Ce module couvre :
    1. Les fondations de la théorie des catégories (l'héritage de Grothendieck)
    2. Les cribles (Sieves) et précaractères (Presieves)
    3. Les topologies de Grothendieck
    4. Les faisceaux (Sheaves) — de types, sur espaces topologiques
    5. La géométrie algébrique : Schemes, Spec, sections globales, foncteurs
       d'oubli
    6. Ce que Mathlib n'a PAS ENCORE (état 2026-05) — cibles de formalisation
       de niveau recherche : cohomologie étale, motifs, six opérations,
       Riemann-Roch, dualité de Grothendieck, cohomologie cristalline,
       géométrie anabélienne, résultats profonds EGA/SGA.

  Epic #1646. Tous les `sorry`s éliminés à la création.

  ### i18n — convention #4980 ratifiée 2026-07-04

  Ce sous-module suit l'option A (bilingue inline FR/EN), variante pragmatique
  c.376-c.381 (deux blocs `/` top-level distincts, sans `---` interne) : le
  bloc EN existant est préservé verbatim ci-dessus, le bloc FR miroir est
  ajouté juste après sans séparateur `---`. Convention sibling pair
  (`<Foo>_en.lean` à part) réservée aux modules de substance (cf c.374
  `Astar_en.lean`) ; pour les modules de cartographie comme `MathlibMap`,
  l'inline FR+EN est le bon compromis (peu de code, deux langues côte à côte).
  Les énoncés `#check @...` restent en anglais (Mathlib 4, tactic DSL standard).
  Seules les **docstrings `/-- ... -/`** et les **commentaires `-- ...`**
  bilingues sont ajoutées. Anti-§D byte-identity garanti : le namespace body
  est préservé bit-pour-bit.

  ### c.382 — continuité registre `grothendieck_lean` Phase 2+ ouvert post-c.381

  c.381 = 1ᵉʳ sous-module rollout `grothendieck_lean` Phase 2+ (YonedaLemma,
  PR #6197 OPEN MERGEABLE, lemme de Yoneda = THE foundational theorem of
  category theory). c.382 = **2ᵉ sous-module rollout Phase 2+** =
  **continuité registre `grothendieck_lean` ouvert** (PIVOT L335 strict c.381
  autorise continuer sur même registre tant que backlog substantiel — donc
  suite rollout `grothendieck_lean` Phase 2+ est naturel). MathlibMap =
  satellite cartographie Mathlib 4, **analogue structurel** de c.377
  `conway_lean/Conway/MathlibMap` (premier sous-module rollout conway_lean
  Phase 1+, satellite cartographie Mathlib 4 aussi). Backlog c.383+ :
  `Grothendieck/{Sheafification,SitePoints,Conservative,MayerVietorisSquare,
  SheafBasics,SieveLattice,CategoryAndSites,YonedaLemma_lemmas,
  SheafCohomology/*,Calibration,SchemesTour,Subcanonical,ZariskiSite,
  DenseTopology,SieveGenerate,LeftExact,SheafHom,SieveOps,CoverageGen,
  CanonicalProps,ConstantSheaf}.lean` (20 sous-modules backlog Phase 2+).

  Cross-références : c.366 `#6111` `Conway.lean` racine bilingue (MERGED) +
  c.367 `#6115` `Grothendieck.lean` racine bilingue (MERGED, option A) +
  c.373 `#6156` `Knots.lean` racine bilingue (OPEN) + c.374 `#6163` `Astar`
  sibling pair (OPEN) + c.375 `#6171` `Knots` sub-modules 5/6 (OPEN) +
  c.376 `#6173` `Knots/Invariant` 6/6 (OPEN) + c.377 `#6178` `MathlibMap`
  bilingue (premier sous-module rollout conway_lean, PIVOT L335 strict) +
  c.378 `#6182` `LookAndSay` bilingue (suite rollout conway_lean) +
  c.379 `#6190` `Fractran` bilingue (machine universelle Turing-complète) +
  c.380 `#6194` `Doomsday` bilingue (algorithme Doomsday + 4 `#eval!` cas
  réels) + c.381 `#6197` `YonedaLemma` bilingue (lemme fondamental théorie
  des catégories, PIVOT L335 strict vers grothendieck_lean Phase 2+) +
  **c.382 `MathlibMap` bilingue (cette PR, satellite cartographie Mathlib
  4 = analogue structurel de c.377 conway_lean/MathlibMap)** ← continuité
  registre `grothendieck_lean` Phase 2+ ouvert post-c.381.
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
