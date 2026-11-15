/-
Grothendieck tribute — Part 66: the topology spectrum of a presheaf.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

The driving question: **for which topologies is a given presheaf a sheaf?**
Part 63 (`SheafCondition.lean`) characterized the equalizer condition for a
FIXED topology; Part 7 (`SheafBasics.lean`) showed that `IsSheaf` descends
along `J₁ ≤ J₂` (`isSheaf_of_le`). This module turns the question onto the
topology coordinate — the "spectrum" `Spec(P) = {J | P is a sheaf for J}`:

  - `isSheaf_const_unit`: the constant singleton presheaf is a sheaf for
    EVERY topology — its spectrum is the whole lattice. This is the
    terminal-object warm-up of the sheaf world: no data to glue, hence no
    gluing can ever fail.
  - `isSheaf_inf`: the spectrum is stable under binary infima — if `P` is a
    sheaf for `J₁` and for `J₂`, it is a sheaf for `J₁ ⊓ J₂`.
  - `isSheaf_iInf`: the indexed version — the spectrum is stable under
    arbitrary (nonempty) infima. The `Nonempty ι` hypothesis is necessary:
    over an empty family, `⨅ i, J i` is the maximal topology (every sieve
    covers), for which not every presheaf is a sheaf.

All three proofs are direct compositions: `Subsingleton` for the first,
`Grothendieck.TopologyLattice.inf_covering` / `iInf_covering` (from the
lake, decomposition of membership in the infimum) for the other two.

References:
  - Stacks Project, tag 00Z8 ("sheaves and sieves").
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Ch. III §4 — the dependence of the sheaf condition on the topology.
  - M. Kashiwara, P. Schapira, *Categories and Sheaves* [KS06] §17.

i18n convention (EPIC #4980, ratified 2026-07-04): this module is the
English sibling of the canonical French file `SheafTopologySpectrum.lean`
(sibling pair model, see PR #6154 for the pilot on `Utility.lean`).
Theorem statements, lemma names, Lean tactics and Mathlib references stay
in English (Mathlib 4, standard tactic DSL). Only docstrings `/-- ... -/`
and comments `-- ...` differ between the two files. Anti-§D byte-identity
guaranteed: the namespace body is preserved bit-for-bit (statements and
proofs byte-identical between `SheafTopologySpectrum.lean` and
`SheafTopologySpectrum_en.lean`).

Epic #1646, Phase 2 (#2159). All `sorry`s eliminated at creation.
-/

import Grothendieck.SheafBasics
import Grothendieck.TopologyLattice
import Mathlib.CategoryTheory.Sites.SheafOfTypes

namespace Grothendieck_en

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

section Contenu

variable {C : Type u} [Category.{v} C]

/-- **The constant singleton presheaf is a sheaf for every topology.**

For the constant functor on `PUnit` (the "data-free" presheaf), the sheaf
condition is vacuous: every compatible family amalgamates at the unique
element, and the amalgamation is unique because all values are singletons.
The topology spectrum of this presheaf is therefore the whole lattice —
the primitive form of the fact that the terminal object of the presheaf
topos is a sheaf. Reference: MM92 Ch. III §4. -/
theorem isSheaf_const_unit (J : GrothendieckTopology C) :
    Presieve.IsSheaf J ((Functor.const Cᵒᵖ).obj PUnit.{max v u + 1}) := by
  haveI : ∀ Z : Cᵒᵖ, Subsingleton (((Functor.const Cᵒᵖ).obj PUnit.{max v u + 1}).obj Z) :=
    fun _ => inferInstanceAs (Subsingleton PUnit)
  intro X S hS x hx
  refine ⟨PUnit.unit, ?_, ?_⟩
  · intro Y f hf
    exact Subsingleton.elim _ _
  · intro t ht
    exact Subsingleton.elim _ _

/-- **The topology spectrum of a presheaf is stable under binary infima.**

If `P` is a sheaf for `J₁` and for `J₂`, it is a sheaf for `J₁ ⊓ J₂`:
covering by the infimum is covering by both (lake's `TopologyLattice`
part, `inf_covering`), and the finer hypothesis already suffices. This is
the "spectrum" version of Part 7's `isSheaf_of_le`: the set of topologies
for which `P` is a sheaf is a sublattice for infima. Reference: MM92
Ch. III §4. -/
theorem isSheaf_inf {J₁ J₂ : GrothendieckTopology C} {P : Cᵒᵖ ⥤ Type (max v u)}
    (h₁ : Presieve.IsSheaf J₁ P) (_h₂ : Presieve.IsSheaf J₂ P) :
    Presieve.IsSheaf (J₁ ⊓ J₂) P := by
  intro X S hS
  exact h₁ S (Grothendieck.TopologyLattice.inf_covering S |>.1 hS).1

/-- **The topology spectrum is stable under arbitrary (nonempty) infima.**

If `P` is a sheaf for each `J i`, it is a sheaf for `⨅ i, J i`. The
`Nonempty ι` hypothesis is necessary: over an empty family the infimum is
the maximal topology (every sieve covers), which does not admit every
presheaf as a sheaf. Reference: MM92 Ch. III §4. -/
theorem isSheaf_iInf {ι : Type*} [Nonempty ι] {J : ι → GrothendieckTopology C}
    {P : Cᵒᵖ ⥤ Type (max v u)}
    (h : ∀ i, Presieve.IsSheaf (J i) P) :
    Presieve.IsSheaf (⨅ i, J i) P := by
  intro X S hS
  exact h (Classical.arbitrary ι) S ((Grothendieck.TopologyLattice.iInf_covering J S).1 hS (Classical.arbitrary ι))

end Contenu

end Grothendieck_en
