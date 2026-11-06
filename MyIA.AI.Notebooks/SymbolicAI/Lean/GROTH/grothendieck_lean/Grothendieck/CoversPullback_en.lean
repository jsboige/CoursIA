/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Grothendieck Homage — Part 40 : arrow-form laws under pullback

Alexandre Grothendieck (1928-2014).

Phase 5 extension (#2159, EPIC #1646).

Parts 1-39 established the foundations: categories, sieves,
topologies, lattice laws, pullback identities, sheaf bases,
covering closure, calibration, subcanonicality, dense topologies,
sheaves, internal hom, Cech cohomology, Mayer-Vietoris limit,
Kan extensions, adjunctions, monads, equivalences, monoidal categories,
limits and colimits, comma pairs, direct images, proper theorems on the
arrow form (`J.Covers S f`), on the bundled cover (`J.Cover X`), the
coherence laws of the pullback pseudo-functor (Part 37), the functor
laws of pullback (Part 38) and the lattice laws of topologies (Part 39).

Part 40 establishes the **laws of the arrow form `J.Covers S f` under
pullback**: Mathlib provides the topology axioms in arrow form
(`arrow_max`, `arrow_stable`, `arrow_trans`, `arrow_intersect`) and the
definitional `covers_iff`, but **does not provide** the behavior laws of
`J.Covers` with respect to operations on sieves and morphisms. This module
states and proves them:

  - `covers_mono` : the arrow form is monotone in the sieve —
    if `A ≤ B` and `A` covers `f`, then `B` covers `f`.
  - `covers_union` : the arrow form is stable under join —
    if `S` covers `f`, then `S ⊔ R` covers `f`.
  - `covers_pullback_comp` : **base change law** — covering the
    composite `g ≫ f` is equivalent to covering the pullback `S.pullback f`
    along `g`.
  - `covers_iso_cancel` : covering `g ≫ f` with `g` iso is equivalent to
    covering `f` (cancellation by isomorphism).
  - `covers_iso_covering` : an isomorphic arrow `e.hom` is covered by `S`
    if and only if `S` is covering.
  - `covers_bind` : **local character in arrow form** — if `S` covers `f`
    and, for every arrow `g` of `S`, the sieve `R g` is covering on its
    domain, then the bound sieve `Sieve.bind S R` covers `f`.
  - `covers_iff_exists_cover` : bridge to the bundled cover — `S` covers
    `f` if and only if `S.pullback f` contains a `J.Cover Y`.
  - `cover_pullback_covers` : the pullback of a cover `S.pullback f`
    covers the identity of `Y` — the `J.Covers` version of
    `J.Cover.pullback` (Part 38).

Each proof is a **real tactic proof** (DEEP vein): the topology axioms
(`superset_covering`, `pullback_mem_iff_of_isIso`,
`arrow_trans`) plus the laws of `Sieve.pullback` (`pullback_comp`,
`pullback_id`, `pullback_monotone`) and the adjunction law of the bind
(`Sieve.le_pullback_bind`). No proof is a re-export.

EPIC #1646, Phase 5 (#2159). All `sorry`s eliminated at creation.

### i18n convention (EPIC #4980 ratified by user 2026-07-04)

This module is paired with its French sibling in the sibling file
`CoversPullback.lean` (sibling pair model, see PR #6154 for the pilot on
`Utility.lean`). The `_en` namespace suffix is applied to the EN file
(anti-collision, per code-style.md #4980). Theorem statements, lemma names,
Lean tactics and Mathlib references remain in English; only the docstrings
`/-- ... -/` and comments `-- ...` differ between the two files
(byte-identity preservation).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck.CoversPullback_en

open CategoryTheory

/-!
## Section 1 : monotonicity and union

The arrow form `J.Covers S f` is defined by `S.pullback f ∈ J Y`
(Mathlib, `covers_iff`). Monotonicity in the sieve follows from the
monotonicity of sieve pullback (`Sieve.pullback_monotone`) and the axiom
`superset_covering`. The union is a special case.
-/

/-- The arrow form is monotone in the sieve : if `A ≤ B` and `A` covers `f`,
    then `B` covers `f`.
    Proof : reduce both members to memberships (`covers_iff`), then
    `superset_covering` with the monotonicity of pullback
    (`Sieve.pullback_monotone`). -/
theorem covers_mono {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (f : Y ⟶ X) {A B : Sieve X} (hAB : A ≤ B) (h : J.Covers A f) :
    J.Covers B f := by
  rw [GrothendieckTopology.covers_iff] at h ⊢
  exact J.superset_covering (Sieve.pullback_monotone f hAB) h

/-- The arrow form is stable under join : if `S` covers `f`,
    then `S ⊔ R` covers `f`.
    Proof : special case of `covers_mono` with `le_sup_left`. -/
theorem covers_union {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (f : Y ⟶ X) (S R : Sieve X) (hS : J.Covers S f) :
    J.Covers (S ⊔ R) f := by
  exact covers_mono J f (le_sup_left : S ≤ S ⊔ R) hS

/-!
## Section 2 : base change and isomorphisms

The composition law of `Sieve.pullback` (`Sieve.pullback_comp`) expresses
the base change : `S.pullback (g ≫ f) = (S.pullback f).pullback g`.
From it we derive the arrow-form base change (`covers_pullback_comp`)
and the cancellation by isomorphism (`covers_iso_cancel`), which uses the
Mathlib lemma `pullback_mem_iff_of_isIso`.
-/

/-- Base change law in arrow form : covering the composite `g ≫ f`
    is equivalent to covering the pullback `S.pullback f` along `g`.
    Proof : `covers_iff` on both members then `Sieve.pullback_comp`
    (definitional equality of the two sieves at stake). -/
theorem covers_pullback_comp {C : Type*} [Category C] {X Y Z : C}
    (J : GrothendieckTopology C) (f : Y ⟶ X) (g : Z ⟶ Y) (S : Sieve X) :
    J.Covers S (g ≫ f) ↔ J.Covers (S.pullback f) g := by
  rw [GrothendieckTopology.covers_iff, GrothendieckTopology.covers_iff,
    Sieve.pullback_comp]

/-- Cancellation by isomorphism : if `g` is an isomorphism, covering
    `g ≫ f` is equivalent to covering `f`.
    Proof : base change (`Sieve.pullback_comp`) then
    `pullback_mem_iff_of_isIso`, which reduces the pullback along an iso to
    the original membership. -/
theorem covers_iso_cancel {C : Type*} [Category C] {X Y Z : C}
    (J : GrothendieckTopology C) (f : Y ⟶ X) {g : Z ⟶ Y} [IsIso g] (S : Sieve X) :
    J.Covers S (g ≫ f) ↔ J.Covers S f := by
  rw [GrothendieckTopology.covers_iff, GrothendieckTopology.covers_iff,
    Sieve.pullback_comp]
  exact GrothendieckTopology.pullback_mem_iff_of_isIso (i := g) (S := S.pullback f)

/-- An isomorphic arrow `e.hom` is covered by `S` if and only if
    `S` is covering.
    Proof : `covers_iff` then `pullback_mem_iff_of_isIso`. -/
theorem covers_iso_covering {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (e : X ≅ Y) (S : Sieve Y) :
    J.Covers S e.hom ↔ S ∈ J Y := by
  rw [GrothendieckTopology.covers_iff]
  exact GrothendieckTopology.pullback_mem_iff_of_isIso (S := S)

/-!
## Section 3 : local character

The transitivity axiom `arrow_trans` says : if `S` covers `f` and every
arrow of `S` is covered by `R`, then `R` covers `f`. The bind form
`Sieve.bind S R` glues the sieves `R g` into a single sieve on `X` ; we show
that it inherits the covering of `f`. The brick is the adjunction law
`Sieve.le_pullback_bind : R g ≤ (Sieve.bind S R).pullback g` (the pullback
of the bind contains each component).
-/

/-- Local character in arrow form : if `S` covers `f` and, for every arrow
    `g : Z ⟶ X` of `S`, the sieve `R g` is covering on its domain
    (`R hg ∈ J Z`), then the bound sieve `Sieve.bind S R` covers `f`.
    Proof : `arrow_trans` from `S` to `Sieve.bind S R`, then for every arrow
    `g` of `S`, `superset_covering` with
    `Sieve.le_pullback_bind` (each `R g` is below the pullback of the bind). -/
theorem covers_bind {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (f : Y ⟶ X) (S : Sieve X) (R : ∀ ⦃Z : C⦄ ⦃g : Z ⟶ X⦄, S g → Sieve Z)
    (hS : J.Covers S f) (hR : ∀ ⦃Z : C⦄ (g : Z ⟶ X) (hg : S g), R hg ∈ J Z) :
    J.Covers (Sieve.bind S R) f := by
  refine GrothendieckTopology.arrow_trans (J := J) (f := f) (S := S) (R := Sieve.bind S R) hS ?_
  intro Z g hg
  rw [GrothendieckTopology.covers_iff]
  exact J.superset_covering (Sieve.le_pullback_bind S R g hg) (hR g hg)

/-!
## Section 4 : bridge to the bundled cover

The bundled cover `J.Cover X = { S : Sieve X // S ∈ J X }` (Part 38)
gathers the covering sieves with their membership proof. We relate the
arrow form to the subtype : `S` covers `f` if and only if the pullback
`S.pullback f` contains a cover.
-/

/-- `S` covers `f` if and only if `S.pullback f` contains a
    `J.Cover Y` (as a subsieve).
    Proof : forward direction — the cover `S.pullback f` itself is a
    `J.Cover Y` (`covers_iff`) ; reverse direction —
    `superset_covering` from the contained cover. -/
theorem covers_iff_exists_cover {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (S : Sieve X) (f : Y ⟶ X) :
    J.Covers S f ↔ ∃ T : J.Cover Y, (T : Sieve Y) ≤ S.pullback f := by
  constructor
  · intro h
    exact ⟨⟨S.pullback f, by simpa [GrothendieckTopology.covers_iff] using h⟩, le_rfl⟩
  · rintro ⟨T, hT⟩
    rw [GrothendieckTopology.covers_iff]
    exact J.superset_covering hT T.condition

/-- The pullback of a cover `S.pullback f` covers the identity of `Y`.
    Proof : `covers_iff` then `Sieve.pullback_id` (the pullback of the
    identity is the identity) and the subtype condition. -/
theorem cover_pullback_covers {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (S : J.Cover X) (f : Y ⟶ X) :
    J.Covers (S.pullback f) (𝟙 Y) := by
  rw [GrothendieckTopology.covers_iff, Sieve.pullback_id]
  exact (S.pullback f).condition

end Grothendieck.CoversPullback_en
