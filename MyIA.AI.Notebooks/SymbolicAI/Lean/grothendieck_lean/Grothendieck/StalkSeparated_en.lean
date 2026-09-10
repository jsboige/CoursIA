/-
Grothendieck tribute — Part 74: stalks detect equality of sections.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

Part 72 (`Stalks`) computed stalks on the opens site, and Part 73
(`StalkPoints`) identified the stalk with the fibre functor of the point of
the site. This part establishes the **detection** property: two sections of
a **separated** type-valued presheaf with equal germs at every point are
equal.

  `eq_of_germ_eq_of_isSeparated : (∀ x ∈ U, germ_x s = germ_x t) → s = t`

The assembly rests on two levers, both already available:

  - `TopCat.Presheaf.germ_eq` (Mathlib, valid for ANY presheaf): equal
    germs at `x` yield a neighbourhood `W ∋ x` on which the restrictions of
    `s` and `t` coincide;
  - `Presheaf.IsSeparated` (Mathlib's bundled separatedness predicate, whose
    core is `IsSeparatedFor.ext`): for a separated presheaf, two sections
    whose restrictions agree on every arrow of a covering sieve are equal.

The witness sieve is built by hand: the neighbourhoods `V p` chosen by the
axiom of choice cover `U`, and the sieve "be dominated by one of the `V p`"
covers `U` for `opensTopology T` (Part 70, where membership is read
through `mem_opensTopology_iff`).

Two corollaries complete the tranche:

  - `eq_of_germ_eq_of_isSheaf`: for a sheaf OF TYPES, the same conclusion
    with no limit assumptions — where Mathlib's `section_ext` requires
    `[HasLimits C]` etc., separatedness suffices here: every sheaf is
    separated (`Presheaf.IsSheaf.isSeparated`), and the Part 70 bridge
    (`isSheaf_opensTopology_iff`) transports Mathlib's sheaf condition to
    the own site;
  - `injective_germ_family_of_isSeparated`: combinatorial restatement —
    the "family of germs" map `s ↦ (germ_x s)ₓ` is injective. This is the
    pointwise brick of the sheaves ↔ étale spaces dictionary begun in
    Parts 72-73: a section is determined by its germinal values.

References:
  - SGA 4, II.5 (separatedness condition on a site).
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Chap. II §6 (sections equal iff locally equal).
  - Mathlib, `Mathlib.Topology.Sheaves.Stalks` (`germ_eq`, and
    `section_ext` — the sheaf version, of which this is the separated
    relaxation).
  - Part 70 (`Grothendieck.SpacesMathlib`): `opensTopology_eq`,
    `isSheaf_opensTopology_iff`.
  - Part 72 (`Grothendieck.Stalks`): concrete germs and stalks.
  - Part 73 (`Grothendieck.StalkPoints`): the stalk as fibre functor.

i18n convention (EPIC #4980 ratified 2026-07-04): this module is twinned
with `StalkSeparated.lean`. Statements, proofs and Lean names remain
identical; only docstrings and comments differ.

Epic #1646, Phase 2 (#2159). No `sorry` introduced.
-/

import Grothendieck.Spaces
import Grothendieck.SpacesMathlib
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.Topology.Sheaves.Stalks

universe u

namespace Grothendieck.StalkSeparated_en

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

section Contenu

variable (T : Type u) [TopologicalSpace T]

/-- **Stalks detect equality of sections (separated case)**: two sections
of a type-valued presheaf separated for the opens topology, with equal
germs at every point of `U`, are equal. The proof chooses, for each point,
a neighbourhood where the restrictions coincide (`germ_eq` — valid for any
presheaf), forms the sieve of opens dominated by one of these
neighbourhoods — a covering sieve for `opensTopology T` — and concludes by
applying the bundled separatedness predicate (`Presheaf.IsSeparated`, whose
core is `IsSeparatedFor.ext`). This is the separated relaxation of
Mathlib's `section_ext`, which requires a full sheaf. Reference: [MM92]
Chap. II §6. -/
theorem eq_of_germ_eq_of_isSeparated (F : TopCat.Presheaf (Type u) (TopCat.of T))
    (hF : Presheaf.IsSeparated (J := opensTopology T) F)
    {U : Opens T} {s t : F.obj (op U)}
    (h : ∀ (x : T) (hx : x ∈ U),
      TopCat.Presheaf.germ (X := TopCat.of T) F U x hx s =
        TopCat.Presheaf.germ (X := TopCat.of T) F U x hx t) :
    s = t := by
  classical
  -- For each point `p` of `U`, choose a neighbourhood `V p` where `s` and
  -- `t` coincide (germ_eq, two arrows `V p ⟶ U` since both sections live on `U`).
  choose V m i₁ i₂ heq using fun (p : {x : T // x ∈ U}) =>
    TopCat.Presheaf.germ_eq (X := TopCat.of T) F p.1 p.2 p.2 s t (h p.1 p.2)
  -- The sieve of opens dominated by one of the `V p` covers `U`.
  refine hF U ⟨fun (Y : Opens T) _ => ∃ p : {x : T // x ∈ U}, Y ≤ V p, ?sieve⟩ ?mem s t ?ext
  · -- downward closure: compose the inclusions of opens.
    intro Y Z f hf g
    obtain ⟨p, hp⟩ := hf
    exact ⟨p, g.le.trans hp⟩
  · rw [mem_opensTopology_iff]
    intro x hx
    exact ⟨V ⟨x, hx⟩, i₁ ⟨x, hx⟩, ⟨⟨x, hx⟩, le_refl _⟩, m ⟨x, hx⟩⟩
  · -- on every arrow of the sieve, the restrictions coincide (through `V p`).
    rintro Y f ⟨p, hYV⟩
    have hf₁ : f = homOfLE hYV ≫ i₁ p := Subsingleton.elim _ _
    have hf₂ : f = homOfLE hYV ≫ i₂ p := Subsingleton.elim _ _
    calc F.map f.op s
        = F.map ((homOfLE hYV ≫ i₁ p).op) s := by rw [hf₁]
      _ = (F.map (i₁ p).op ≫ F.map (homOfLE hYV).op) s := by
          rw [op_comp, Functor.map_comp]
      _ = F.map (homOfLE hYV).op (F.map (i₁ p).op s) := rfl
      _ = F.map (homOfLE hYV).op (F.map (i₂ p).op t) := by rw [heq p]
      _ = (F.map (i₂ p).op ≫ F.map (homOfLE hYV).op) t := rfl
      _ = F.map ((homOfLE hYV ≫ i₂ p).op) t := by
          rw [op_comp, Functor.map_comp]
      _ = F.map f.op t := by rw [hf₂]

/-- **Sheaf corollary**: for a sheaf of types, the same conclusion with no
limit assumption at all — where Mathlib's `section_ext` requires
`[HasLimits C]` and friends, separatedness suffices here: every sheaf is
separated (`Presheaf.IsSheaf.isSeparated`), and the Part 70 bridge
(`isSheaf_opensTopology_iff`) transports Mathlib's sheaf condition to the
own site. -/
theorem eq_of_germ_eq_of_isSheaf (F : TopCat.Presheaf (Type u) (TopCat.of T))
    (hF : TopCat.Presheaf.IsSheaf F)
    {U : Opens T} {s t : F.obj (op U)}
    (h : ∀ (x : T) (hx : x ∈ U),
      TopCat.Presheaf.germ (X := TopCat.of T) F U x hx s =
        TopCat.Presheaf.germ (X := TopCat.of T) F U x hx t) :
    s = t :=
  eq_of_germ_eq_of_isSeparated T F ((isSheaf_opensTopology_iff F).mpr hF).isSeparated h

/-- **A section is determined by its family of germs**: for a separated
type-valued presheaf, the map sending a section over `U` to its family of
germs at the points of `U` is injective. Combinatorial restatement of the
main theorem — the pointwise brick of the sheaves ↔ étale spaces dictionary
started in Parts 72-73. -/
theorem injective_germ_family_of_isSeparated (F : TopCat.Presheaf (Type u) (TopCat.of T))
    (hF : Presheaf.IsSeparated (J := opensTopology T) F) (U : Opens T) :
    Function.Injective (fun (s : F.obj (op U)) (p : {x : T // x ∈ U}) =>
      TopCat.Presheaf.germ (X := TopCat.of T) F U p.1 p.2 s) := by
  intro s t hst
  refine eq_of_germ_eq_of_isSeparated T F hF ?_
  intro x hx
  exact congrFun hst ⟨x, hx⟩

end Contenu

end Grothendieck.StalkSeparated_en