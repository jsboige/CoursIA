/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Grothendieck tribute — Part 79 (EN sibling of `Grothendieck/Flasque.lean`): flasque sheaves,
from the topological to the site level.

Alexandre Grothendieck (1928-2014).

Phase 2 extension (#2159, Epic #1646).

A sheaf is **flasque** (flabby, SGA 4 II 3.2; MM92 II.3; Godement) when its
sections extend: any section over an "open subobject" extends to the whole.
Mathlib formalizes this notion for topological spaces
(`Mathlib.Topology.Sheaves.Flasque`, vendored):

  - `TopCat.Presheaf.IsFlasque F` : every restriction map `F.map i` is an
    epimorphism;
  - the instance `pushforward_isFlasque` : stability under direct image;
  - `isFlasque_skyscraperSheaf_of_epi_from` and
    `isFlasque_skyscraperSheaf_of_hasZeroObject` : the skyscraper sheaf is
    flasque.

What Mathlib states **nowhere** is the **site** version of flasqueness — the
reading that replaces "open contained in an open" by "sieve on an object",
that is, a subobject of the representable in the Grothendieck topology. This
is what this part introduces:

  `IsFlasqueSieves P` : every compatible family on **any** sieve `S` of `X` —
  covering or not — admits an amalgamation.

The recorded consequences:

  - `nonempty_obj_of_isFlasqueSieves` : even the **empty** sieve must
    amalgamate — hence `P.obj (op X)` is nonempty for every `X`. This is the
    subtlety the topological definition cannot see: the map towards the empty
    open is trivially epi there, whereas here the empty sieve demands the
    existence of a global section.
  - `isSheaf_of_isFlasqueSieves_of_isSeparated` : **flasque + separated ⇒
    sheaf**. Flasqueness provides the existence of the amalgamation (on every
    sieve, hence on the covering ones), separatedness provides uniqueness —
    the classical theorem, here by explicit chaining of `IsSeparated.isSheaf`.
  - `isFlasqueSieves_const_of_subsingleton` : the **constant** presheaf is
    flasque only if the value is a nonempty **subsingleton**. The
    `Subsingleton` condition is not prudence: two incomparable arrows of a
    sieve may carry distinct values, which no amalgamation can reconcile —
    compatibility only constrains arrows linked by factorization. This is the
    exact counterpart of the skyscraper sheaf: away from the point, the value
    is terminal, hence subsingleton — and this is precisely why the
    skyscraper is flasque (crossover Part 77).
  - `pushforward_isFlasque_bridge` : the bridge towards Mathlib's instance,
    read in the direct-image vocabulary of Part 33;
  - `isFlasque_skyscraper_bridge` : the bridge towards Mathlib's
    skyscraper-flasque theorem, read as an application of Part 77 — a
    skyscraper sheaf valued in a category with a zero object is flasque, and
    its support (Part 77: `closure {p₀}`) is carried by sections that extend
    everywhere.

The conceptual reading: flasqueness is the "existence" half of the sheaf
condition, paid on **all** sieves rather than on the covering ones only —
separatedness is the other half, and their union is the whole sheaf
condition. Part 63 decomposed that condition as a product-equalizer; this
part decomposes it as existence + uniqueness.

References:
  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §3 (flasque sheaves, "mous").
  - SGA 4, Exposé II (sites and sieves).
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Chap. II §3, Exercise 9 (flabby sheaves).
  - Mathlib, `Mathlib.Topology.Sheaves.Flasque` (vendored).
  - Part 33 (`Grothendieck.DirectImage`): the direct image `f_*`.
  - Part 63 (`Grothendieck.SheafCondition`): the product-equalizer condition.
  - Part 77 (`Grothendieck.Skyscraper`): the skyscraper sheaf and its support.

i18n convention (EPIC #4980 ratified 2026-07-04): this module is the English
canonical sibling of `Grothendieck/Flasque.lean` — `_en` suffix on the
namespace (`Grothendieck.Flasque_en`), mirror imports, translated docstrings
and comments. Theorem statements, Lean tactics, lemma names and Mathlib
references remain in English (Mathlib 4, standard tactic DSL). Only the
docstrings `/-- ... -/` and comments `-- ...` differ between the two files.
Anti-§D byte-identity guaranteed: the namespace body is preserved bit for bit
(statements and proofs byte-identical between `Flasque.lean` and
`Flasque_en.lean`).

Epic #1646, Phase 2 (#2159). All `sorry`s eliminated at creation.
-/

import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Topology.Sheaves.Skyscraper

namespace Grothendieck.Flasque_en

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

section Site

variable {C : Type u} [Category.{v} C]

/-- **Flasque at the level of sieves**: every compatible family on any sieve
`S` of `X` — covering or not — admits an amalgamation. This is the
"existence" half of the sheaf condition, required on all subobjects of the
representable rather than on the covering sieves only. -/
class IsFlasqueSieves (P : Cᵒᵖ ⥤ Type (max v u)) : Prop where
  /-- Every compatible family on every sieve amalgamates. -/
  amalgamates : ∀ {X : C} (S : Sieve X) (x : S.arrows.FamilyOfElements P),
    x.Compatible → ∃ t, x.IsAmalgamation t

theorem isFlasqueSieves_iff (P : Cᵒᵖ ⥤ Type (max v u)) :
    IsFlasqueSieves P ↔ ∀ {X : C} (S : Sieve X) (x : S.arrows.FamilyOfElements P),
      x.Compatible → ∃ t, x.IsAmalgamation t :=
  ⟨fun h => h.amalgamates, fun h => ⟨h⟩⟩

/-- The **empty** sieve must amalgamate its (empty) compatible family: a
flasque presheaf has sections over **every** object. Mathlib's topological
definition does not see this point — the restriction towards the empty open
is trivially epi there. -/
theorem nonempty_obj_of_isFlasqueSieves {P : Cᵒᵖ ⥤ Type (max v u)} [IsFlasqueSieves P]
    (X : C) : Nonempty (P.obj (op X)) := by
  obtain ⟨t, _⟩ := IsFlasqueSieves.amalgamates (P := P) (⊥ : Sieve X)
    (fun Y f hf => False.elim hf)
    (fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ _ _ => False.elim h₁)
  exact ⟨t⟩

/-- **Flasque + separated ⇒ sheaf**: flasqueness provides the existence of
the amalgamation on every sieve — hence on the covering ones —,
separatedness provides uniqueness. Explicit chaining of
`Presieve.IsSeparated.isSheaf`
(`Mathlib.CategoryTheory.Sites.SheafOfTypes`), whose amalgamation premise is
exactly the specialization of the `IsFlasqueSieves.amalgamates` field to the
covering sieves. -/
theorem isSheaf_of_isFlasqueSieves_of_isSeparated {J : GrothendieckTopology C}
    {P : Cᵒᵖ ⥤ Type (max v u)} [IsFlasqueSieves P] (hsep : Presieve.IsSeparated J P) :
    Presieve.IsSheaf J P :=
  hsep.isSheaf fun _ _ _ x hx => IsFlasqueSieves.amalgamates _ x hx

/-- The **constant** presheaf with value `A` is flasque as soon as `A` is a
nonempty subsingleton. The `Subsingleton` condition is necessary, not
prudence: two incomparable arrows of a same sieve may carry distinct values —
compatibility only constrains arrows linked by factorization, and no
amalgamation can then exist. -/
theorem isFlasqueSieves_const_of_subsingleton (A : Type (max v u))
    [Subsingleton A] [Nonempty A] : IsFlasqueSieves ((Functor.const Cᵒᵖ).obj A) where
  amalgamates := by
    intro X S x _
    refine ⟨Classical.choice ‹Nonempty A›, ?_⟩
    intro Y f _
    exact @Subsingleton.elim A _ _ _

end Site

section Topologique

open TopCat TopCat.Presheaf TopologicalSpace

variable {C : Type u} [Category.{v} C]

/-- Bridge towards Mathlib's instance: the direct image of a flasque presheaf
along a continuous map is flasque. Read in the vocabulary of Part 33
(`Grothendieck.DirectImage`), where the pair `f_* ⊣ f^*` is the first brick
of the six-operation formalism. -/
theorem pushforward_isFlasque_bridge {X Y : TopCat} {F : TopCat.Presheaf C X}
    [TopCat.Presheaf.IsFlasque F] (f : X ⟶ Y) :
    TopCat.Presheaf.IsFlasque ((TopCat.Presheaf.pushforward C f).obj F) :=
  TopCat.Presheaf.IsFlasque.pushforward_isFlasque F f

/-- Bridge towards Mathlib's skyscraper-flasque theorem: a skyscraper sheaf
valued in a category with a zero object is flasque. Crossover Part 77
(`Grothendieck.Skyscraper`): away from the point `p₀`, the value is terminal
— hence subsingleton, the exact situation of
`isFlasqueSieves_const_of_subsingleton` — and this is what makes extension
possible; the support (`closure {p₀}`, Part 77) is carried by sections that
extend everywhere. -/
theorem isFlasque_skyscraper_bridge {X : TopCat} (p₀ : ↑X)
    [(U : Opens ↑X) → Decidable (p₀ ∈ U)] (A : C) [HasZeroObject C] :
    (skyscraperSheaf p₀ A).IsFlasque :=
  isFlasque_skyscraperSheaf_of_hasZeroObject p₀ A

end Topologique

end Grothendieck.Flasque_en
