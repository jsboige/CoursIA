/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Grothendieck Homage — Part 41 : order laws of the arrow form

Alexandre Grothendieck (1928-2014).

Phase 5 extension (#2159, EPIC #1646).

Parts 1-40 established the foundations: categories, sieves, topologies,
lattice laws, pullback identities, sheaf bases, covering closure,
calibration, subcanonicality, dense topologies, sheaves, internal hom,
Cech cohomology, Mayer-Vietoris limit, Kan extensions, adjunctions, monads,
equivalences, monoidal categories, limits and colimits, comma pairs, direct
images, proper theorems on the arrow form (`J.Covers S f`), on the bundled
cover (`J.Cover X`), the coherence laws of the pullback pseudo-functor
(Part 37), the functor laws of pullback (Part 38), the lattice laws of
topologies (Part 39) and the laws of the arrow form under pullback (Part 40).

Part 41 establishes the **order laws of the arrow form `J.Covers S f`**:
Mathlib provides the topology axioms in arrow form (`arrow_max`,
`arrow_stable`, `arrow_trans`, `arrow_intersect`), the definitional
`covers_iff`, monotonicity in the sieve (`superset_covering`), the pullback
law (`pullback_stable`) and the lattice law `pullback_inter`, but **does not
provide** the behavior of `J.Covers` with respect to the bounds of the sieve
lattice (top, bottom, meet), the stability of every covering sieve, the
connection to sieve generation `Sieve.generate`, nor the compatibility of
pullback with meet. This module states and proves them:

  - `covers_top` : the top sieve covers every arrow.
  - `covers_bot_iff` : the bottom sieve covers `f` if and only if it is
    covering on the codomain.
  - `covers_of_covering` : a covering sieve of `X` covers every arrow to `X`
    (arrow form of `pullback_stable`).
  - `covers_inter_iff` : `S ⊓ R` covers `f` if and only if `S` and `R`
    cover `f` (converse of `arrow_intersect`).
  - `covers_generate_sieve` : covering the generated sieve
    `Sieve.generate S` is equivalent to covering `S` (a sieve equals the
    sieve it generates).
  - `covers_pullback_inter` : the pullback of `S ⊓ R` along `g ≫ f` covers
    exactly the meet of the pullbacks (compatibility law
    pullback / meet in arrow form).

Each proof is a **real tactic proof** (DEEP vein): the topology axioms
(`top_mem`, `pullback_stable`, `superset_covering`, `arrow_intersect`) plus
the laws of `Sieve.pullback` (`pullback_top`, `pullback_bot`,
`pullback_comp`, `pullback_inter`) and sieve generation
(`Sieve.generate_sieve`). No proof is a re-export.

EPIC #1646, Phase 5 (#2159). All `sorry`s eliminated at creation.

### i18n convention (EPIC #4980 ratified by user 2026-07-04)

This module is paired with its French sibling in the sibling file
`CoversOrder.lean` (sibling pair model, see PR #6154 for the pilot on
`Utility.lean`). The `_en` namespace suffix is applied to the EN file
(anti-collision, per code-style.md #4980). Theorem statements, lemma names,
Lean tactics and Mathlib references remain in English; only the docstrings
`/-- ... -/` and comments `-- ...` differ between the two files
(byte-identity preservation).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck.CoversOrder_en

open CategoryTheory

/-!
## Section 1 : bounds of the sieve lattice

The top sieve `⊤` is covering (`top_mem`) ; by definition of the arrow form
(`covers_iff`) and `Sieve.pullback_top`, it covers every arrow. The bottom
sieve `⊥` is a symmetric case : its pullback is the bottom, so it covers
only if it is already covering on the codomain.
-/

/-- The top sieve covers every arrow : `J.Covers ⊤ f` for every `f`.
    Proof : `covers_iff` then `Sieve.pullback_top`, and `top_mem`. -/
theorem covers_top {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (f : Y ⟶ X) : J.Covers (⊤ : Sieve X) f := by
  rw [GrothendieckTopology.covers_iff, Sieve.pullback_top]
  exact J.top_mem Y

/-- The bottom sieve covers `f : Y ⟶ X` if and only if it is covering on
    `Y` : `J.Covers ⊥ f ↔ ⊥ ∈ J Y`.
    Proof : `covers_iff` then `Sieve.pullback_bot` (the pullback of the
    bottom is the bottom). -/
theorem covers_bot_iff {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (f : Y ⟶ X) :
    J.Covers (⊥ : Sieve X) f ↔ ⊥ ∈ J Y := by
  rw [GrothendieckTopology.covers_iff, Sieve.pullback_bot]

/-!
## Section 2 : stability of a covering sieve

The axiom `pullback_stable` says that the pullback of a covering sieve is a
covering sieve. The arrow form is its direct reformulation : a covering
sieve of `X` covers every arrow to `X`.
-/

/-- A covering sieve of `X` covers every arrow to `X` :
    `S ∈ J X → J.Covers S f` (arrow form of `pullback_stable`).
    Proof : `covers_iff` then the axiom `J.pullback_stable`. -/
theorem covers_of_covering {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) {S : Sieve X} (hS : S ∈ J X) (f : Y ⟶ X) :
    J.Covers S f := by
  rw [GrothendieckTopology.covers_iff]
  exact J.pullback_stable f hS

/-!
## Section 3 : meet

The axiom `arrow_intersect` provides `J.Covers S f → J.Covers R f →
J.Covers (S ⊓ R) f`. The law `Sieve.pullback_inter` (the pullback of a meet
is the meet of the pullbacks) gives the converse : if `S ⊓ R` covers `f`,
then each factor covers `f`.
-/

/-- `S ⊓ R` covers `f` if and only if `S` and `R` cover `f`.
    Proof : forward direction — `arrow_intersect` ; converse direction —
    `covers_iff`, `Sieve.pullback_inter`, then `superset_covering` with
    `inf_le_left` and `inf_le_right`. -/
theorem covers_inter_iff {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (S R : Sieve X) (f : Y ⟶ X) :
    J.Covers (S ⊓ R) f ↔ J.Covers S f ∧ J.Covers R f := by
  constructor
  · intro h
    rw [GrothendieckTopology.covers_iff] at h ⊢
    rw [Sieve.pullback_inter] at h
    exact ⟨J.superset_covering inf_le_left h, J.superset_covering inf_le_right h⟩
  · rintro ⟨hS, hR⟩
    exact GrothendieckTopology.arrow_intersect (J := J) (f := f) (S := S) (R := R) hS hR

/-!
## Section 4 : generation and pullback

A sieve equals the sieve it generates (`Sieve.generate_sieve`) ; covering
one is equivalent to covering the other. Finally, the pullback of a meet
along a composite factors : `(S ⊓ R).pullback (g ≫ f)` is the pullback of
the meet of the pullbacks.
-/

/-- Covering the generated sieve `Sieve.generate S` is equivalent to
    covering `S`.
    Proof : `covers_iff` on both members then `Sieve.generate_sieve`. -/
theorem covers_generate_sieve {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (S : Sieve X) (f : Y ⟶ X) :
    J.Covers (Sieve.generate S) f ↔ J.Covers S f := by
  rw [GrothendieckTopology.covers_iff, GrothendieckTopology.covers_iff,
    Sieve.generate_sieve]

/-- Pullback / meet compatibility in arrow form : `S ⊓ R` covers `g ≫ f`
    if and only if `S.pullback f ⊓ R.pullback f` covers `g`.
    Proof : `covers_iff` on both members, `Sieve.pullback_comp` (base change
    of the composite) then `Sieve.pullback_inter` (the pullback of a meet is
    the meet of the pullbacks). -/
theorem covers_pullback_inter {C : Type*} [Category C] {X Y Z : C}
    (J : GrothendieckTopology C) (S R : Sieve X) (f : Y ⟶ X) (g : Z ⟶ Y) :
    J.Covers (S ⊓ R) (g ≫ f) ↔ J.Covers (S.pullback f ⊓ R.pullback f) g := by
  rw [GrothendieckTopology.covers_iff, GrothendieckTopology.covers_iff,
    Sieve.pullback_comp, ← Sieve.pullback_inter]

end Grothendieck.CoversOrder_en
