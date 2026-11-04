/-
Grothendieck tribute — Part 71: subcanonicity of the open-cover topology.

Alexandre Grothendieck (1928-2014).

Phase 2 extension (#2159, Epic #1646).

A Grothendieck topology is *subcanonical* when every representable presheaf
is a sheaf (Mathlib: `Subcanonical`). For the site of open sets of a
topological space, this is the founding fact that lets one view each open
set `U` as the sheaf it represents: the Yoneda embedding factors through the
category of sheaves (Mathlib: `GrothendieckTopology.yoneda`).

The proof is pointwise: gluing a compatible family of sections of the
representable `yoneda.obj U` along a covering sieve `S` is done point by
point — each point of `X` lies in the domain of an arrow of `S`, the family
supplies a section above that domain (hence an arrow to `U` containing the
point) — and the uniqueness is the uniqueness of arrows between open sets
(the category `Opens T` is thin).

References:
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Ch. II §1 (subcanonical sites).
  - Mathlib, `CategoryTheory.Sites.Canonical` (class `Subcanonical`,
    constructor `Subcanonical.of_isSheaf_yoneda_obj`).
  - Part 68 (`Grothendieck.Spaces`): the `opensTopology` construction.

i18n convention (EPIC #4980 ratified 2026-07-04): this module is twinned
with `SpacesSubcanonical.lean`. Statements, proofs and Lean names stay
identical; only docstrings and comments differ.

Epic #1646, Phase 2 (#2159). No `sorry` introduced.
-/

import Grothendieck.Spaces
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.SheafOfTypes

namespace Grothendieck.SpacesSubcanonical_en

open CategoryTheory TopologicalSpace

universe u

section Contenu

variable (T : Type u) [TopologicalSpace T]

/-- Central lemma: for any open set `U`, the representable presheaf
`yoneda.obj U` is a sheaf for the topology `opensTopology`. The gluing is
pointwise — each point of `X` is covered by an arrow of the sieve, whose
section of the compatible family gives membership in `U` — and the
uniqueness is the uniqueness of arrows between open sets (thin category). -/
theorem isSheaf_yoneda_opensTopology (U : Opens T) :
    Presieve.IsSheaf (opensTopology T) (yoneda.obj U) := by
  intro X S hS xf _hcomp
  have hXU : X ≤ U := by
    intro p hp
    obtain ⟨W, f, hf, hpW⟩ := hS p hp
    have hsec : W ⟶ U := show W ⟶ U from xf f hf
    exact hsec.le hpW
  refine ⟨homOfLE hXU, ?amal, ?uniq⟩
  · intro Y f hf
    apply Subsingleton.elim (α := Y ⟶ U)
  · intro t' _ht'
    apply Subsingleton.elim (α := X ⟶ U)

/-- **Central result**: the topology `opensTopology` is subcanonical. Every
representable presheaf on the site of open sets of a topological space is a
sheaf — each open set is therefore seen as a sheaf, and the Yoneda embedding
factors through the category of sheaves (see `GrothendieckTopology.yoneda`
in Mathlib, available from this instance). -/
theorem opensTopology_subcanonical : GrothendieckTopology.Subcanonical (opensTopology T) :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ fun U => isSheaf_yoneda_opensTopology T U

end Contenu

end Grothendieck.SpacesSubcanonical_en
