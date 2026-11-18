/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Part 44 : arrow form of the dense topology

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Parts 1-43 established the foundations: categories, sieves, topologies,
lattice laws, pullback identities, sheaf bases, covering closure,
calibration, subcanonicity, dense topologies, sheaves, internal hom,
Čech cohomology, Mayer-Vietoris limit, Kan extensions, adjunctions, monads,
equivalences, monoidal categories, the Grothendieck construction, the
direct/exceptional image, the arrow form of the covering, the coherence
laws of the pullback pseudo-functor and the indexed lattice laws.

This part completes the arrow form `J.Covers` for the extremal topologies.
For the **discrete** topology (`discrete = ⊤`) and the **trivial** topology
(`trivial = ⊥`), Mathlib already provides the arrow forms:
`top_covers : (⊤ : GrothendieckTopology C).Covers S f` and
`bot_covers : (⊥ : GrothendieckTopology C).Covers S f ↔ S f`. The real
gap is the arrow form of the **dense** topology: `dense_covering` is only
a pointwise statement (`S ∈ dense X ↔ ∀ {Y} (f : Y ⟶ X), ∃ …`).
Here we provide its arrow-form translation `dense.Covers S f`, the
stability under precomposition and the link with pointwise membership.

The guiding thread: every pointwise statement `S ∈ J X` admits an arrow-form
twin `J.Covers S f` (via `covers_iff`, `S.pullback f ∈ J Y`). Parts 39-43
showed the pattern for `⊓`, `⊔`, `sInf`, `sSup`, the pullback covering
and the order; here we apply it to the dense topology.
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck.CoversTopologies_en

open CategoryTheory

/-!
## Section 1 : the arrow form of the dense topology

The dense topology of Mathlib is defined pointwise:
`dense_covering : S ∈ dense X ↔ ∀ {Y} (f : Y ⟶ X), ∃ (Z) (g : Z ⟶ Y), S (g ≫ f)`.
Its arrow-form translation says that a sieve `S` covers a morphism
`f : Y ⟶ X` for `dense` if and only if every factorization of `f`
refines to a morphism of `S`: this is exactly the defining condition,
rewritten on `S.pullback f ∈ dense Y`.
-/

/-- Arrow form of `dense_covering`: `S` is dense above `f` if and only if
    every morphism `g` towards the domain of `f` admits a factorization
    whose composite lies in `S`.
    Proof: `covers_iff` reduces the left member to `S.pullback f ∈ dense Y`,
    then `dense_covering` unfolds the pointwise definition; the rewrite
    `(S.pullback f) (h ≫ g) = S (h ≫ g ≫ f)` (definition of the pullback
    of a sieve plus associativity) makes both members coincide. -/
theorem dense_covers_iff {C : Type*} [Category C] {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
    GrothendieckTopology.dense.Covers S f ↔
      ∀ {Z : C} (g : Z ⟶ Y), ∃ (W : C) (h : W ⟶ Z), S (h ≫ g ≫ f) := by
  rw [GrothendieckTopology.covers_iff, GrothendieckTopology.dense_covering]
  simp

/-!
## Section 2 : stability under precomposition

The topology property `pullback_stable` of `dense` says that a morphism
in `S.pullback f ∈ dense Y` is transported to `(S.pullback f).pullback g`.
By the identity `S.pullback (g ≫ f) = (S.pullback f).pullback g`
(`Sieve.pullback_comp`), this is exactly the stability of the arrow form:
if `S` is dense above `f`, it is dense above every `g ≫ f`.
-/

/-- The arrow form of `dense` is stable under precomposition: if `S` covers
    `f : Y ⟶ X` for `dense`, then `S` also covers `g ≫ f` for every
    `g : Z ⟶ Y`.
    Proof: `covers_iff` on both sides, then `Sieve.pullback_comp`
    identifies `S.pullback (g ≫ f)` with `(S.pullback f).pullback g`, and
    `pullback_stable g h` of the dense topology concludes. -/
theorem dense_covers_precomp {C : Type*} [Category C] {X Y Z : C} (S : Sieve X)
    (f : Y ⟶ X) (g : Z ⟶ Y) :
    GrothendieckTopology.dense.Covers S f → GrothendieckTopology.dense.Covers S (g ≫ f) := by
  intro h
  rw [GrothendieckTopology.covers_iff] at h ⊢
  rw [Sieve.pullback_comp]
  exact GrothendieckTopology.dense.pullback_stable g h

/-!
## Section 3 : identity and pointwise membership

`Sieve.pullback_id` makes the pullback along the identity trivial:
`S.pullback (𝟙 X) = S`. The arrow form of `dense` above `𝟙 X` therefore
falls back exactly on the pointwise membership `S ∈ dense X`.
-/

/-- The arrow form of `dense` above the identity coincides with pointwise
    membership: `dense.Covers S (𝟙 X) ↔ S ∈ dense X`.
    Proof: `covers_iff` then `Sieve.pullback_id`. -/
theorem dense_covers_id {C : Type*} [Category C] {X : C} (S : Sieve X) :
    GrothendieckTopology.dense.Covers S (𝟙 X) ↔ S ∈ GrothendieckTopology.dense X := by
  rw [GrothendieckTopology.covers_iff, Sieve.pullback_id]

/-- Every morphism of `S` is covered by `dense`: `S f → dense.Covers S f`.
    Proof: `S f` forces `S.pullback f = ⊤` (`Sieve.pullback_eq_top_of_mem`),
    and `⊤` belongs to every sieve of a topology (`top_mem`). -/
theorem dense_covers_of_mem {C : Type*} [Category C] {X Y : C} (S : Sieve X)
    {f : Y ⟶ X} (h : S f) :
    GrothendieckTopology.dense.Covers S f := by
  rw [GrothendieckTopology.covers_iff]
  rw [Sieve.pullback_eq_top_of_mem S h]
  exact GrothendieckTopology.top_mem GrothendieckTopology.dense Y

end Grothendieck.CoversTopologies_en
