/-
Grothendieck tribute — Part 75: gluing families of germs.

Alexandre Grothendieck (1928-2014).

Phase 2 extension (#2159, Epic #1646).

Part 74 established injectivity of the map sending a section to its family of
germs. This part formalizes the correct converse: an arbitrary family of germs
need not come from a section, but it does as soon as it is **locally
representable** by sections.

The proof chooses the local representatives supplied by the hypothesis. On
each intersection, their restrictions have equal germs; Part 74
therefore makes them equal. The sheaf condition in its unique-gluing form
(`existsUnique_gluing'`) then produces a global section. Its germs are the
prescribed family, and uniqueness follows again from Part 74.

References:
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Chap. II §6 (sheaves and étale spaces).
  - Mathlib, `Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing`.
  - Part 74 (`Grothendieck.StalkSeparated`): detection by germs.

Stacks correspondence (group #14 of #28537 — “the stalks”, measured 26/11)
---------------------------------------------------------------------------
The reading of `AxiomMath/Stacks` is done on the **local tree**
`StacksFrontier/Topology/Sheaves/` (sparse clone of the whole folder): the
coverage is far wider here than in the surveys of 22/11 and 25/11, which
could only read a few files through the `contents` API (GitHub's recursive
tree is truncated and `Topology/Sheaves` does not appear in it). An “absent”
verdict therefore means: **no statement of that name anywhere in
`Topology/Sheaves/`**.

| Statement | Class | Stacks referent | What our version adds |
|---|---|---|---|
| `GermFamily` | **covered** | `Stalk/Separated.lean:65` `toStalkProduct` (EGA IV 21.9.1) | the dependency on the subtype `{x // x ∈ U}` |
| `GermFamily.IsLocallyRepresentable` | absent | none (`LocallyRepresentable`, `germFamily`: 0 results); nearest: `Glueing/Sheaf.lean:232` `gluedPresheaf` (00AL) | gluing a family of **germs**, where Stacks glues sections |
| `germFamily_isLocallyRepresentable` | absent | none | the triviality of the case “the family comes from a section” |
| `existsUnique_gluing'_of_isSheaf` | partial | `Glueing/Sheaf.lean:240` `gluedPresheaf_isSheaf`; `:278` `glued` (00AL) | the variant with an explicit target, with no limit-preservation assumption |
| `existsUnique_section_of_isLocallyRepresentable` | absent | none | the **reconstruction** of the section from its germs (the reverse direction of the dictionary) |
| `surjective_germ_family_to_locallyRepresentable` | absent | none | the formulation “section ↦ family of germs” |

The i18n convention (EPIC #4980, ratified 2026-07-04) pairs this module with
`StalkGluing.lean`. Lean statements, proofs, and names remain identical; only
docstrings and comments differ.

Epic #1646, Phase 2 (#2159). No `sorry` introduced.
-/

import Grothendieck.StalkSeparated_en
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

universe u

namespace Grothendieck.StalkGluing_en

open CategoryTheory Opposite TopCat TopologicalSpace TopologicalSpace.Opens
open Grothendieck.StalkSeparated_en

section Contenu

variable (T : Type u) [TopologicalSpace T]

/-- The family of germs of a presheaf `F` at the points of an open set `U`.

Stacks correspondence — **COVERED**:
`StacksFrontier/Topology/Sheaves/Stalk/Separated.lean:65` (`toStalkProduct
(U : Opens X) : F.obj (Opposite.op U) → ∀ x : U, F.stalk x.1`, EGA
IV 21.9.1) is the same family of germs — the type `∀ x : U` is the
non-dependent version of our `∀ p : {x // x ∈ U}`. What our version adds:
the **dependency** on the subtype `{x : T // x ∈ U}`, which keeps the
membership in `U` in the type. -/
abbrev GermFamily (F : TopCat.Presheaf (Type u) (TopCat.of T)) (U : Opens T) :=
  ∀ p : {x : T // x ∈ U}, F.stalk p.1

/-- A family of germs on `U` is **locally representable** if every point
`p : U` has an open neighbourhood `V p ⟶ U` and a section on `V p` whose germ
at every point of `V p` is the value prescribed by the family. This condition
is entirely local: it assumes no section on `U`.

Stacks correspondence — **ABSENT**: no statement of that name anywhere in
`StacksFrontier/Topology/Sheaves/` (searches for `LocallyRepresentable` and
`germFamily`: 0 results). The nearest counterpart is the gluing datum
`Glueing/Sheaf.lean:232` (`gluedPresheaf (D : GlueData X U)`, Stacks 00AL),
which glues **restriction isomorphisms** between sheaves over a covering —
not a family of germs. The difference is the **object** being glued: germs
here, sections there. -/
def GermFamily.IsLocallyRepresentable
    (F : TopCat.Presheaf (Type u) (TopCat.of T)) (U : Opens T)
    (a : GermFamily T F U) : Prop :=
  ∃ (V : {x : T // x ∈ U} → Opens T)
    (iVU : ∀ p, V p ⟶ U)
    (_hmem : ∀ p, p.1 ∈ V p)
    (sf : ∀ p, F.obj (op (V p))),
      ∀ (p) (x : T) (hx : x ∈ V p),
        F.germ (V p) x hx (sf p) = a ⟨x, (iVU p).le hx⟩

/-- The family of germs of a section is locally representable.

Stacks correspondence — **ABSENT**: corollary of the previous one — the
local representability of a family of germs has no named statement at
Stacks (search for `germFamily` over the whole tree
`StacksFrontier/Topology/Sheaves/`: 0 results). What our version adds: the
**triviality** of the case “the family comes from a section” — the local
representative is the section itself, restricted to `U`. -/
theorem germFamily_isLocallyRepresentable
    (F : TopCat.Presheaf (Type u) (TopCat.of T)) (U : Opens T)
    (s : F.obj (op U)) :
    GermFamily.IsLocallyRepresentable T F U
      (fun p => F.germ U p.1 p.2 s) := by
  refine ⟨fun _ => U, fun _ => 𝟙 U, fun p => p.2, fun _ => s, ?_⟩
  intro p x hx
  congr 1

/-- A unique-gluing variant with an explicit target open set for sheaves of
types. Unlike `TopCat.Sheaf.existsUnique_gluing'`, it starts directly from a
presheaf equipped with its sheaf property and requires no general
limit-preservation assumptions.

Stacks correspondence — **PARTIAL**: Stacks 00AL builds the glued sheaf of
a gluing datum (`Glueing/Sheaf.lean:232` `gluedPresheaf`, `:240`
`gluedPresheaf_isSheaf`, `:278` `glued`). Same core — the unique gluing of
compatible data — but two frames: Stacks glues **sheaves** over a
**covering** by means of restriction isomorphisms satisfying the cocycle
condition, we glue **compatible sections** of a **presheaf** in the sense
of `IsCompatible`, with no general limit-preservation assumption. What our
version adds: the variant with an explicit target and the absence of those
assumptions. -/
theorem existsUnique_gluing'_of_isSheaf
    (F : TopCat.Presheaf (Type u) (TopCat.of T)) (hF : TopCat.Presheaf.IsSheaf F)
    {ι : Type*} (V : ι → Opens T) (U : Opens T) (iVU : ∀ i, V i ⟶ U)
    (hcover : U ≤ iSup V) (sf : ∀ i, F.obj (op (V i)))
    (hcompatible : TopCat.Presheaf.IsCompatible F V sf) :
    ∃! s : F.obj (op U), ∀ i, F.map (iVU i).op s = sf i := by
  have hU : U = iSup V := le_antisymm hcover (iSup_le fun i => (iVU i).le)
  obtain ⟨gl, hgl, huniq⟩ := hF.isSheafUniqueGluing_types sf hcompatible
  refine ⟨F.map (eqToHom hU).op gl, ?_, ?_⟩
  · intro i
    rw [← ConcreteCategory.comp_apply, ← F.map_comp]
    exact hgl i
  · intro t ht
    convert! congr_arg (F.map (eqToHom hU).op)
      (huniq (F.map (eqToHom hU.symm).op t) fun i => _) <;>
        rw [← ConcreteCategory.comp_apply, ← F.map_comp]
    · simp
    · exact ht i

/-- **Gluing germs**: every locally representable family of germs of a
Type-valued sheaf comes from a unique global section. Existence glues the local
representatives; uniqueness is exactly the detection of sections by their
germs established in Part 74.

Stacks correspondence — **ABSENT**: the gluing of a locally representable
**family of germs** has no named statement at Stacks (search for
`germFamily`: 0 results; `Glueing/Sheaf.lean` glues sections given over a
covering, not germs reconstructing a section). This is the **reverse
direction** of the dictionary: Stacks goes from the local section to the
sheaf, we go from the germs to the global section. What our version adds:
the reconstruction itself, and the uniqueness that follows from it through
the detection of Part 74. -/
theorem existsUnique_section_of_isLocallyRepresentable
    (F : TopCat.Presheaf (Type u) (TopCat.of T)) (hF : TopCat.Presheaf.IsSheaf F)
    (U : Opens T) (a : GermFamily T F U)
    (ha : GermFamily.IsLocallyRepresentable T F U a) :
    ∃! s : F.obj (op U), ∀ p : {x : T // x ∈ U}, F.germ U p.1 p.2 s = a p := by
  classical
  rcases ha with ⟨V, iVU, hmem, sf, hsf⟩
  have hcover : U ≤ iSup V := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩
  have hcompatible : TopCat.Presheaf.IsCompatible F V sf := by
    intro p q
    apply eq_of_germ_eq_of_isSheaf T F hF
    intro x hx
    rw [F.germ_res_apply (infLELeft (V p) (V q)) x hx,
      F.germ_res_apply (infLERight (V p) (V q)) x hx]
    calc
      F.germ (V p) x ((inf_le_left : V p ⊓ V q ≤ V p) hx) (sf p) =
          a ⟨x, (iVU p).le ((inf_le_left : V p ⊓ V q ≤ V p) hx)⟩ :=
        hsf p x ((inf_le_left : V p ⊓ V q ≤ V p) hx)
      _ = a ⟨x, (iVU q).le ((inf_le_right : V p ⊓ V q ≤ V q) hx)⟩ := by
        congr 1
      _ = F.germ (V q) x ((inf_le_right : V p ⊓ V q ≤ V q) hx) (sf q) :=
        (hsf q x ((inf_le_right : V p ⊓ V q ≤ V q) hx)).symm
  obtain ⟨s, hs, _⟩ :=
    existsUnique_gluing'_of_isSheaf T F hF V U iVU hcover sf hcompatible
  have hsg : ∀ p : {x : T // x ∈ U}, F.germ U p.1 p.2 s = a p := by
    intro p
    calc
      F.germ U p.1 p.2 s = F.germ (V p) p.1 (hmem p) (F.map (iVU p).op s) :=
        (F.germ_res_apply (iVU p) p.1 (hmem p) s).symm
      _ = F.germ (V p) p.1 (hmem p) (sf p) := by rw [hs p]
      _ = a ⟨p.1, (iVU p).le (hmem p)⟩ := hsf p p.1 (hmem p)
      _ = a p := by congr 1
  refine ⟨s, hsg, ?_⟩
  intro t ht
  apply eq_of_germ_eq_of_isSheaf T F hF
  intro x hx
  exact (ht ⟨x, hx⟩).trans (hsg ⟨x, hx⟩).symm

/-- Surjectivity restatement: the “section to family of germs” map is
surjective onto the subtype of locally representable families.

Stacks correspondence — **ABSENT**: surjectivity restatement of the
previous one; no statement of that name at Stacks (search for `germFamily`
over the whole tree `StacksFrontier/Topology/Sheaves/`: 0 results). What our
version adds: the formulation “section ↦ family of germs”, which makes the
sheaves ↔ étale spaces dictionary explicit. -/
theorem surjective_germ_family_to_locallyRepresentable
    (F : TopCat.Presheaf (Type u) (TopCat.of T)) (hF : TopCat.Presheaf.IsSheaf F)
    (U : Opens T) :
    Function.Surjective
      (fun (s : F.obj (op U)) =>
        (⟨fun p => F.germ U p.1 p.2 s,
          germFamily_isLocallyRepresentable T F U s⟩ :
          {a : GermFamily T F U // GermFamily.IsLocallyRepresentable T F U a})) := by
  intro a
  obtain ⟨s, hs, _⟩ :=
    existsUnique_section_of_isLocallyRepresentable T F hF U a.1 a.2
  refine ⟨s, Subtype.ext ?_⟩
  funext p
  exact hs p

end Contenu

end Grothendieck.StalkGluing_en
