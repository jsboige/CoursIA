/-
Grothendieck tribute — Part 72: germs and stalks on the site of open sets.

Alexandre Grothendieck (1928-2014).

Phase 2 extension (#2159, Epic #1646).

The stalk of a presheaf `F` at a point `x` is the colimit of the sections
over the open neighbourhoods of `x`: two sections have the same germ when
they agree on a small enough neighbourhood. Part 70 established that the
topology `opensTopology` is exactly Mathlib's — the underlying presheaves
are definitionally the same, and the whole `TopCat.Presheaf` API (stalks,
germs, `germ_res`, `stalk_hom_ext`) applies verbatim to presheaves on the
own site.

The new result of this part is the complete computation of the stalk of a
representable. For an open set `U`, the presheaf `yoneda.obj U` (a sheaf,
by the subcanonicity of Part 71) has a stalk at `x` which is a singleton
exactly when `x ∈ U`, and empty otherwise: the stalk of a representable
detects membership of the point. This is the first link of the sheaves ↔
étale spaces dictionary — the fibre at `x` of the étale space of the sheaf
represented by `U` is `U` itself.

The proof fetches every element of the stalk as the germ of a section
(`exists_germ_eq`: the `germ` arrows are jointly surjective onto the
colimit), then identifies that germ with the germ of the identity of `U`
by restriction (`germ_res`): a section of the representable above a
neighbourhood `W` is an arrow `W ⟶ U`, the inclusion of a neighbourhood
contained in `U`.

References:
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Ch. II §3 (germs and sheaves on a space).
  - Mathlib, `Mathlib.Topology.Sheaves.Stalks` (stalks and germs:
    `exists_germ_eq`, `germ_res`).
  - Part 70 (`Grothendieck.SpacesMathlib`): the equality bridge between
    the topologies, which makes Mathlib's API applicable to the own site.
  - Part 71 (`Grothendieck.SpacesSubcanonical`): subcanonicity —
    `yoneda.obj U` is a sheaf.

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
| `unique_stalk_yoneda` | absent | nearest: `Skyscraper/Stalk.lean:36` `skyscraperPresheafStalkOfSpecializes` (009B) | the **uniqueness** and the description of the element (the germ of the identity of `U`) |
| `isEmpty_stalk_yoneda` | absent | nearest: `Skyscraper/Stalk.lean:41` `skyscraperPresheafStalkOfNotSpecializes` (009B) | the **argument** for emptiness, where Stacks states an equality of groups |
| `nonempty_stalk_yoneda_iff` | absent | none | the whole chain “membership ⇔ non-emptiness” |

i18n convention (EPIC #4980 ratified 2026-07-04): this module is twinned
with `Stalks.lean`. Statements, proofs and Lean names stay identical; only
docstrings and comments differ.

Epic #1646, Phase 2 (#2159). No `sorry` introduced.
-/

import Grothendieck.Spaces_en
import Mathlib.Topology.Sheaves.Stalks

namespace Grothendieck.Stalks_en

open CategoryTheory TopologicalSpace
open Grothendieck_en

universe u

section Contenu

variable (T : Type u) [TopologicalSpace T]

/-- **Stalk of a representable, interior case**: at a point `x ∈ U`, the
stalk of the presheaf `yoneda.obj U` — viewed as a presheaf on the space
`T` through the Part 70 bridge — is a singleton, whose unique element is
the germ of the identity of `U`. Every element of the stalk is the germ of
a section (`exists_germ_eq`); such a section above a neighbourhood `W ∋ x`
is an arrow `W ⟶ U`, and its germ identifies with the germ of `𝟙 U` by
restriction (`germ_res`).

Stacks correspondence — **ABSENT**: Stacks does not compute the stalk of a
representable. The only statement of the same shape — “the stalk is a
trivially computable object detecting membership” — is the one of the
**skyscraper**: `StacksFrontier/Topology/Sheaves/Skyscraper/Stalk.lean:36`
(`skyscraperPresheafStalkOfSpecializes`, tag 009B) says that the stalk of
the skyscraper presheaf at `x` is the underlying group when `x` specializes
the point, and `:41` (`skyscraperPresheafStalkOfNotSpecializes`) that it is
empty otherwise. Same architecture, different object: the skyscraper rather
than the representable. What our version adds: the **uniqueness** and the
**description** of the element — the germ of the identity of `U` — where
Stacks only gives the equality of the stalk with a group. -/
@[reducible]
noncomputable def unique_stalk_yoneda (U : Opens T) {x : T} (hx : x ∈ U) :
    Unique (TopCat.Presheaf.stalk (X := TopCat.of T) (yoneda.obj U) x) := by
  have key : ∀ z : TopCat.Presheaf.stalk (X := TopCat.of T) (yoneda.obj U) x,
      z = TopCat.Presheaf.germ (X := TopCat.of T) (yoneda.obj U) U x hx (𝟙 U) := by
    intro z
    obtain ⟨W, hW, w, rfl⟩ :=
      TopCat.Presheaf.exists_germ_eq (X := TopCat.of T) (yoneda.obj U) z
    have w' : W ⟶ U := w
    have h := TopCat.Presheaf.germ_res_apply (X := TopCat.of T) (yoneda.obj U) w' x hW (𝟙 U)
    simp only [CategoryTheory.yoneda_obj_map] at h
    exact h
  exact ⟨⟨TopCat.Presheaf.germ (X := TopCat.of T) (yoneda.obj U) U x hx (𝟙 U)⟩, key⟩

/-- **Stalk of a representable, exterior case**: if `x ∉ U`, the stalk of
`yoneda.obj U` is empty — every germ comes from a section `W ⟶ U` above a
neighbourhood `W ∋ x`, which would force `x ∈ U`.

Stacks correspondence — **ABSENT**: same absence as above, the counterpart
being `Skyscraper/Stalk.lean:41` (`skyscraperPresheafStalkOfNotSpecializes`),
which empties the stalk of the skyscraper away from specializing points.
What our version adds: the **argument** for emptiness — an arrow `W ⟶ U`
above a neighbourhood of `x` would force `x ∈ U` — where Stacks states an
equality of groups. -/
theorem isEmpty_stalk_yoneda (U : Opens T) {x : T} (hx : x ∉ U) :
    IsEmpty (TopCat.Presheaf.stalk (X := TopCat.of T) (yoneda.obj U) x) := by
  refine ⟨fun z => ?_⟩
  obtain ⟨W, hW, w, -⟩ :=
    TopCat.Presheaf.exists_germ_eq (X := TopCat.of T) (yoneda.obj U) z
  have w' : W ⟶ U := w
  exact hx (w'.le hW)

/-- **The stalk of a representable detects membership** — junction with
Part 71: `yoneda.obj U` is a sheaf (subcanonicity of `opensTopology`), and
its stalk at `x` is inhabited exactly at the points of `U`. This is the
pointwise shadow of the fact that the sheaf represented by `U` "lives on
`U`": the fibre at `x` of the associated étale space is inhabited inside
`U`, empty outside.

Stacks correspondence — **ABSENT**: the “membership detector” of the
skyscraper (`Skyscraper/Stalk.lean:36` and `:41`) is the nearest statement;
no Stacks statement gives the equivalence “the stalk of the representable
is non-empty if and only if the point is in the open set”. What our version
adds: the **whole chain** — membership ⇔ non-emptiness — where Stacks gives
two disjoint facts (empty / non-empty) about another object. -/
theorem nonempty_stalk_yoneda_iff (U : Opens T) (x : T) :
    Nonempty (TopCat.Presheaf.stalk (X := TopCat.of T) (yoneda.obj U) x) ↔ x ∈ U := by
  constructor
  · rintro ⟨z⟩
    by_contra hx
    exact (isEmpty_stalk_yoneda T U hx).elim z
  · exact fun hx => ⟨(unique_stalk_yoneda T U hx).default⟩

end Contenu

end Grothendieck.Stalks_en
