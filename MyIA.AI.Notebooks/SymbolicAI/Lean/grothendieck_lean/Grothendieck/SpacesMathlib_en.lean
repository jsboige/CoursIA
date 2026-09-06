/-
Grothendieck tribute — Part 70: the bridge to Mathlib.

Alexandre Grothendieck (1928-2014).

Phase 2 extension (#2159, Epic #1646).

Part 68 (`Spaces.lean`) built by hand, in the lake's own language, the
Grothendieck topology of open covers of a topological space. Mathlib states
the very same construction in `Mathlib.CategoryTheory.Sites.Spaces`
(`Opens.grothendieckTopology`). This module closes the loop: the two
definitions are EQUAL — not isomorphic, not equivalent: equal, because
Part 68 faithfully transcribed the same sieve specification.

The equality is no curiosity: `TopCat.Presheaf.IsSheaf`, Mathlib's sheaf
condition for a topological space, is DEFINED as the sheaf condition for
`Opens.grothendieckTopology ↑X` (`Mathlib.Topology.Sheaves.Sheaf`). The
corollary `isSheaf_opensTopology_iff` therefore says exactly this: a
presheaf is a sheaf on the own site `(Opens T, opensTopology T)` if and
only if it is a sheaf in the usual topological sense — the founding case of
Mac Lane – Moerdijk, and the gateway from the whole Mathlib corpus
(`Topology.Sheaves`: sheafification, stalks, étale spaces, points functor)
to the lake's site, with no translation.

  - `opensTopology_eq` : `opensTopology T = Opens.grothendieckTopology T` ;
  - `opensPretopology_eq` : the same coincidence on the pretopology side ;
  - `isSheaf_opensTopology_iff_types` : transport of the sheaf condition
    (sheaves of types) ;
  - `isSheaf_opensTopology_iff` : the central result, valued in an
    arbitrary category ;
  - `coversTop_opensTopology_iff` : transport of the notion of covering
    family.

References:
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Ch. II.
  - Mathlib, `CategoryTheory.Sites.Spaces`, `Topology.Sheaves.Sheaf`.

i18n convention (EPIC #4980 ratified 2026-07-04): this module is twinned
with `SpacesMathlib.lean`. Statements, proofs and Lean names stay
identical; only docstrings and comments differ.

Epic #1646, Phase 2 (#2159). No `sorry` introduced.
-/

import Grothendieck.Spaces
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.Topology.Sheaves.Sheaf

namespace Grothendieck.SpacesMathlib_en

open CategoryTheory TopologicalSpace CategoryTheory.Limits

universe u w w'

section Contenu

variable (T : Type u) [TopologicalSpace T]

/-- **Equality of the topologies**: the hand-defined topology of Part 68 is
exactly Mathlib's `Opens.grothendieckTopology` topology. Part 68
transcribed the same sieve specification ("every point of the target open
belongs to the domain of an arrow of the sieve"); the data field `sieves`
coincides definitionally and the proof fields fall by proof irrelevance. -/
theorem opensTopology_eq :
    opensTopology T = Opens.grothendieckTopology T :=
  rfl

/-- **Equality of the pretopologies**: the own pretopology of open covers
(`opensPretopology`, Part 68) is exactly Mathlib's `Opens.pretopology`
pretopology — the data field `coverings` carries the same specification. -/
theorem opensPretopology_eq :
    opensPretopology T = Opens.pretopology T :=
  rfl

variable {T}

/-- Transport of the sheaf condition for sheaves of types: being a sheaf
for the own topology or for Mathlib's is the same thing. -/
theorem isSheaf_opensTopology_iff_types (P : (Opens T)ᵒᵖ ⥤ Type*) :
    Presheaf.IsSheaf (opensTopology T) P ↔
      Presheaf.IsSheaf (Opens.grothendieckTopology T) P := by
  rw [opensTopology_eq]

/-- **Central result**: the sheaf condition on the site
`(Opens T, opensTopology T)` is exactly Mathlib's usual sheaf condition for
a topological space. `TopCat.Presheaf.IsSheaf` is defined as
`Presheaf.IsSheaf (Opens.grothendieckTopology ↑X)`
(`Mathlib.Topology.Sheaves.Sheaf`), and the bridge `opensTopology_eq`
transports one into the other: the whole `Topology.Sheaves` corpus
(sheafification, stalks, étale spaces, points functor) applies to the own
site with no translation. -/
theorem isSheaf_opensTopology_iff {C : Type w} [Category.{w'} C]
    (F : TopCat.Presheaf C (TopCat.of T)) :
    Presheaf.IsSheaf (opensTopology T) F ↔ TopCat.Presheaf.IsSheaf F := by
  rw [opensTopology_eq]
  rfl

/-- Transport of the notion of covering family: `CoversTop` for the own
topology is `CoversTop` for Mathlib's. Combined with the two `IsOpenCover`
characterizations (Part 68's `coversTop_isOpenCover_iff` and Mathlib's
`Opens.coversTop_iff`), both worlds state the same notion of cover. -/
theorem coversTop_opensTopology_iff {ι : Type*} (U : ι → Opens T) :
    (opensTopology T).CoversTop U ↔ (Opens.grothendieckTopology T).CoversTop U := by
  rw [opensTopology_eq]

end Contenu

end Grothendieck.SpacesMathlib_en
