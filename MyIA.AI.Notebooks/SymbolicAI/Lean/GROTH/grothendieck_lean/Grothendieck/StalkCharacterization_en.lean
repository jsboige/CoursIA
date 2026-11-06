/-
Grothendieck tribute — Part 76: a sheaf is exactly a separated presheaf that
glues.

Alexandre Grothendieck (1928-2014).

Phase 2 extension (#2159, Epic #1646).

Parts 74 and 75 established the two halves separately. Part 74 showed that
germs detect equality of sections of a sheaf, and Part 75 that every locally
representable family of germs comes from a unique section. This part assembles
them into the equivalence that grounds them:

  `IsSheaf F  ↔  <separation by germs>  ∧  <gluing of locally representable
  families>`

This is the classical characterization of a sheaf as a separated presheaf
satisfying the gluing of locally defined sections (Mac Lane–Moerdijk [MM92]
II.6, Stacks 00AK).

The forward direction merely restates the two previous Parts. The converse is
the only place in the lake where the sheaf condition is **derived** rather than
consumed: Part 75 needed `IsSheaf` as a hypothesis, the present part produces
it. One builds the family of germs read off the local representatives of a
compatible covering family, feeds it to the gluing supplied by the hypothesis,
and separation does the rest — it yields both that the resulting section
restricts to each representative, and that it is the only one to do so.

Neither hypothesis is superfluous: separation is uniqueness, gluing supplies
existence.

References:
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92], Chap. II
    §6 (sheaves and étale spaces).
  - Stacks Project, tag 00AK (sheaves and gluing).
  - Mathlib, `Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing`
    (`IsSheafUniqueGluing`, `isSheaf_of_isSheafUniqueGluing_types`, consumed
    in `Mathlib/Topology/Sheaves/LocalPredicate.lean:246`).
  - Parts 74 (`Grothendieck.StalkSeparated`, separation) and 75
    (`Grothendieck.StalkGluing`, gluing).

The i18n convention (EPIC #4980, ratified 2026-07-04) pairs this module with
`StalkCharacterization.lean`. Lean statements, proofs, and names remain
identical; only docstrings and comments differ.

Epic #1646, Phase 2 (#2159). No `sorry` introduced.
-/

import Grothendieck.StalkSeparated
import Grothendieck.StalkGluing
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

universe u

namespace Grothendieck.StalkCharacterization_en

open CategoryTheory Opposite TopCat TopologicalSpace TopologicalSpace.Opens

section Contenu

variable (T : Type u) [TopologicalSpace T]

/-- **Separation by germs**: two sections of a presheaf having the same germ at
every point of an open set are equal. Part 74 established this conclusion for
a sheaf; it is promoted here to a property of the presheaf itself, so that it
can be taken as a hypothesis. -/
def GermSeparated (F : TopCat.Presheaf (Type u) (TopCat.of T)) : Prop :=
  ∀ (U : Opens T) (s t : F.obj (op U)),
    (∀ (x : T) (hx : x ∈ U), F.germ U x hx s = F.germ U x hx t) → s = t

/-- **Gluing of germs**: every locally representable family of germs (in the
sense of Part 75) comes from a section. Part 75 proved this existence for a
sheaf **and** gave uniqueness; only existence is kept here, uniqueness being
exactly the separation above. -/
def GermGluing (F : TopCat.Presheaf (Type u) (TopCat.of T)) : Prop :=
  ∀ (U : Opens T) (a : GermFamily T F U),
    GermFamily.IsLocallyRepresentable T F U a →
      ∃ s : F.obj (op U), ∀ p : {x : T // x ∈ U}, F.germ U p.1 p.2 s = a p

/-- The germ form of compatibility: two members of a compatible family have the
same germ at every point of their intersection. This is the ingredient that
makes the family of germs built on a covering family well defined — two local
representatives of the same point agree locally, hence in germ. -/
theorem germ_eq_of_isCompatible
    (F : TopCat.Presheaf (Type u) (TopCat.of T)) {ι : Type*}
    (U : ι → Opens T) (sf : ∀ i, F.obj (op (U i)))
    (hc : TopCat.Presheaf.IsCompatible F U sf)
    {i j : ι} {x : T} (hi : x ∈ U i) (hj : x ∈ U j) :
    F.germ (U i) x hi (sf i) = F.germ (U j) x hj (sf j) := by
  have hmem : x ∈ U i ⊓ U j := ⟨hi, hj⟩
  rw [← F.germ_res_apply (infLELeft (U i) (U j)) x hmem (sf i),
    ← F.germ_res_apply (infLERight (U i) (U j)) x hmem (sf j), hc i j]

/-- **Characterization of a sheaf by its stalks**: a type-valued presheaf on a
topological space is a sheaf if and only if germs detect equality of sections
(separation) and every locally representable family of germs comes from a
section (gluing).

This is the capstone of the vein opened by Parts 72-75, and the only place in
the lake where the sheaf condition is derived from elementary properties
rather than postulated. -/
theorem isSheaf_iff_germSeparated_and_germGluing
    (F : TopCat.Presheaf (Type u) (TopCat.of T)) :
    TopCat.Presheaf.IsSheaf F ↔ GermSeparated T F ∧ GermGluing T F := by
  constructor
  · intro hF
    refine ⟨?_, ?_⟩
    · intro U s t h
      exact eq_of_germ_eq_of_isSheaf T F hF fun x hx => h x hx
    · intro U a ha
      exact (existsUnique_section_of_isLocallyRepresentable T F hF U a ha).exists
  · rintro ⟨hsep, hglu⟩
    refine TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types F ?_
    intro ι U sf hc
    classical
    -- witness index chosen for each point of the total open set
    let k : {x : T // x ∈ iSup U} → ι := fun p =>
      Classical.choose (Opens.mem_iSup.mp p.2)
    have hk : ∀ p : {x : T // x ∈ iSup U}, p.1 ∈ U (k p) := fun p =>
      Classical.choose_spec (Opens.mem_iSup.mp p.2)
    -- the family of germs read off the local representatives
    let a : GermFamily T F (iSup U) := fun p => F.germ (U (k p)) p.1 (hk p) (sf (k p))
    -- it is locally representable, with the representatives of `sf` as witnesses
    have hlr : GermFamily.IsLocallyRepresentable T F (iSup U) a :=
      ⟨fun p => U (k p), fun p => Opens.leSupr U (k p), fun p => hk p,
        fun p => sf (k p), fun p x hx =>
          germ_eq_of_isCompatible T F U sf hc hx
            (hk ⟨x, (Opens.leSupr U (k p)).le hx⟩)⟩
    obtain ⟨s, hs⟩ := hglu (iSup U) a hlr
    refine ⟨s, ?_, ?_⟩
    · -- `s` restricts to each `U i`: the germs agree, separation concludes
      intro i
      apply hsep (U i)
      intro x hx
      rw [F.germ_res_apply (Opens.leSupr U i) x hx s,
        hs ⟨x, (Opens.leSupr U i).le hx⟩]
      exact germ_eq_of_isCompatible T F U sf hc
        (hk ⟨x, (Opens.leSupr U i).le hx⟩) hx
    · -- uniqueness: two gluings have the same germs, separation concludes
      intro t ht
      apply hsep (iSup U)
      intro x hx
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
      rw [hs ⟨x, hx⟩, ← F.germ_res_apply (Opens.leSupr U i) x hi t, ht i]
      exact germ_eq_of_isCompatible T F U sf hc hi (hk ⟨x, hx⟩)

end Contenu

end Grothendieck.StalkCharacterization_en
