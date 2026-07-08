/-
Grothendieck tribute — Mathlib tour of Grothendieck's mathematical language
Alexandre Grothendieck (1928-2014).

This workspace is a pedagogical homage showing how much of Grothendieck's
mathematical language already lives in Mathlib 4:

  - Categories, functors, natural transformations
  - Sieves and Grothendieck topologies (trivial, discrete, dense)
  - Sheaves on a site
  - Schemes (locally ringed spaces locally Spec R)
  - Zariski topology as a Grothendieck topology
  - Local properties of morphisms (etale, smooth, separated)

This is NOT an attempt to formalize EGA/SGA. It is a curated tour
for learners encountering these concepts through Lean for the first time.

Epic #1646. All `sorry`s eliminated at creation.
-/

import Grothendieck.CategoryAndSites
import Grothendieck.SchemesTour
import Grothendieck.ZariskiSite
import Grothendieck.MathlibMap
import Grothendieck.Calibration
import Grothendieck.SieveLattice
import Grothendieck.SheafBasics
import Grothendieck.SieveOps
import Grothendieck.CoverageGen
import Grothendieck.CanonicalProps
import Grothendieck.SieveGenerate
import Grothendieck.DenseTopology
import Grothendieck.Sheafification
import Grothendieck.LeftExact
import Grothendieck.Subcanonical
import Grothendieck.SitePoints
import Grothendieck.SheafHom
import Grothendieck.ConstantSheaf
import Grothendieck.Conservative
import Grothendieck.SheafCohomology.Basic
import Grothendieck.MayerVietorisSquare
import Grothendieck.SheafCohomology.MayerVietoris
import Grothendieck.SheafCohomology.Cech
import Grothendieck.YonedaLemma
