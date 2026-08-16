/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Part 47 : arrow forms of the extremal topologies

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Parts 1-46 established the foundations: categories, sieves, topologies,
lattice laws, pullback identities, sheaf bases, covering closure,
calibration, subcanonicity, dense topologies, sheaves, internal hom,
Čech cohomology, Mayer-Vietoris limit, Kan extensions, adjunctions, monads,
equivalences, monoidal categories, the Grothendieck construction, the
direct/exceptional image, the arrow form of the covering, the coherence
laws of the pullback pseudo-functor, the indexed lattice laws, the arrow
form of the dense topologies and the arrow form of the
pushforward-pullback adjunction and of the bind.

This part applies the guiding thread "arrow form" to the two extremal
topologies of the complete lattice of topologies — the discrete topology
`⊤` (where every sieve is covering) and the trivial topology `⊥` (where only
the maximal sieve is covering) — and to the bridge between the arrow form and
the bundled type `J.Cover`. Mathlib defines these topologies
(`GrothendieckTopology.discrete`, `GrothendieckTopology.trivial`) and
identifies them with the top and bottom of the lattice through the
`CompleteLattice` instance, but no law gives their arrow form: `(⊤).Covers S f`
is always true, `(⊥).Covers S f` is equivalent to `S.pullback f = ⊤`. We fill
the gap with the monotonicity of the arrow form with respect to the order of
topologies (`monotone_covers`), the two extremal forms and the round-trip
between the arrow form and the bundled covers (`covers_of_cover`,
`cover_of_covers`, `covers_iff_cover`).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck.CoversExtremal_en

open CategoryTheory

/-!
## Section 1 : the order of topologies in arrow form

The order on topologies is the pointwise inclusion of the covering sieves
(`GrothendieckTopology.instLEGrothendieckTopology`). The arrow form is
monotone with respect to the topology: if `J₁ ≤ J₂` and `J₁` covers `f`,
then `J₂` covers `f`. This law, absent from Mathlib, relates the order of
the lattice of topologies to the covering relation.
-/

/-- The arrow form is monotone with respect to the topology: if `J₁ ≤ J₂`
    and `J₁` covers `f`, then `J₂` covers `f`. Proof: `covers_iff` reduces
    both members to the membership of the pullback in the covering sieves,
    then the pointwise inclusion carried by the order. -/
theorem monotone_covers {C : Type*} [Category C] {X Y : C} {J₁ J₂ : GrothendieckTopology C}
    (h : J₁ ≤ J₂) (S : Sieve X) (f : Y ⟶ X) (hC : J₁.Covers S f) : J₂.Covers S f := by
  rw [GrothendieckTopology.covers_iff] at hC ⊢
  exact (GrothendieckTopology.le_def.mp h) Y hC

/-!
## Section 2 : the discrete topology `⊤`

Mathlib defines `GrothendieckTopology.discrete`, the topology where every
sieve is covering, and the `CompleteLattice` instance identifies it with the
top of the lattice definitionally (`CompleteLattice.copy`, `discrete = ⊤`).
The arrow form is therefore trivial: `(⊤).Covers S f` is always true. This
is a fallback of the definition, but formulating it in arrow form unifies
the language of coverings and makes the extremal topology readable in the
same notation as the others.
-/

/-- The discrete topology covers everything: `(⊤).Covers S f ↔ True`.
    Proof: `covers_iff` then the membership in the top of the lattice, which
    is the discrete topology definitionally. -/
theorem discrete_covers_iff {C : Type*} [Category C] {X Y : C}
    (S : Sieve X) (f : Y ⟶ X) : (⊤ : GrothendieckTopology C).Covers S f ↔ True := by
  change (GrothendieckTopology.discrete C).Covers S f ↔ True
  rw [GrothendieckTopology.covers_iff]
  simp

/-- The discrete topology covers every arrow: `(⊤).Covers S f`.
    Proof: the equivalence `discrete_covers_iff`. -/
theorem discrete_covers {C : Type*} [Category C] {X Y : C}
    (S : Sieve X) (f : Y ⟶ X) : (⊤ : GrothendieckTopology C).Covers S f := by
  exact discrete_covers_iff S f |>.mp trivial

/-!
## Section 3 : the trivial topology `⊥`

Mathlib defines `GrothendieckTopology.trivial`, the topology where only the
maximal sieve is covering, and identifies it with the bottom of the lattice
(`trivial_eq_bot`, `trivial_covering`). The arrow form is therefore:
`(⊥).Covers S f` is equivalent to `S.pullback f = ⊤` — the pullback of `S`
along `f` is the maximal sieve, in other words `S` covers the codomain `Y`
only if its pullback is the trivial cover. We derive the fallbacks on the
identity (`S = ⊤`) and on the bottom sieve (`⊥` never covers).
-/

/-- The trivial topology covers `f` by `S` if and only if the pullback of
    `S` along `f` is the maximal sieve:
    `(⊥).Covers S f ↔ S.pullback f = ⊤`.
    Proof: `covers_iff`, then the bottom of the lattice is the trivial
    topology (`trivial_eq_bot`) whose covering sieves are the maximal ones
    (`trivial_covering`). -/
theorem trivial_covers_iff {C : Type*} [Category C] {X Y : C}
    (S : Sieve X) (f : Y ⟶ X) : (⊥ : GrothendieckTopology C).Covers S f ↔ S.pullback f = ⊤ := by
  change (GrothendieckTopology.trivial C).Covers S f ↔ S.pullback f = ⊤
  rw [GrothendieckTopology.covers_iff]
  rw [GrothendieckTopology.trivial_covering]

/-- In the trivial topology, the maximal sieve covers every arrow:
    `S = ⊤ → (⊥).Covers S f`.
    Proof: rewriting of `trivial_covers_iff` with `hS`, then
    `Sieve.pullback_top` (the pullback of the maximal sieve is the maximal
    sieve). -/
theorem trivial_covers_of_top {C : Type*} [Category C] {X Y : C}
    (S : Sieve X) (f : Y ⟶ X) (hS : S = ⊤) : (⊥ : GrothendieckTopology C).Covers S f := by
  rw [trivial_covers_iff S f, hS, Sieve.pullback_top]

/-- In the trivial topology, a sieve covers the identity if and only if it
    is maximal: `(⊥).Covers S (𝟙 X) ↔ S = ⊤`.
    Proof: `trivial_covers_iff` then `Sieve.pullback_id`. -/
theorem trivial_covers_id_iff {C : Type*} [Category C] {X : C}
    (S : Sieve X) : (⊥ : GrothendieckTopology C).Covers S (𝟙 X) ↔ S = ⊤ := by
  rw [trivial_covers_iff S (𝟙 X), Sieve.pullback_id]

/-- In the trivial topology, the bottom sieve never covers:
    `¬ (⊥).Covers ⊥ f`.
    Proof: `trivial_covers_iff` then `Sieve.pullback_bot` reduce to
    `⊥ ≠ ⊤` in the lattice of sieves, proved by applying both sieves to the
    identity `𝟙 Y`. -/
theorem trivial_bot_not_covers {C : Type*} [Category C] {X Y : C}
    (f : Y ⟶ X) : ¬ (⊥ : GrothendieckTopology C).Covers (⊥ : Sieve X) f := by
  rw [trivial_covers_iff (⊥ : Sieve X) f, Sieve.pullback_bot]
  intro h
  have h0 : (⊥ : Sieve Y) (𝟙 Y) = (⊤ : Sieve Y) (𝟙 Y) :=
    congrArg (fun T : Sieve Y => T (𝟙 Y)) h
  simp at h0

/-- The monotonicity relates the extremes: every cover of the trivial
    topology is a cover of the discrete topology:
    `(⊥).Covers S f → (⊤).Covers S f`.
    Proof: `monotone_covers` applied to `bot_le`. -/
theorem extremal_covers {C : Type*} [Category C] {X Y : C}
    (S : Sieve X) (f : Y ⟶ X) (h : (⊥ : GrothendieckTopology C).Covers S f) :
    (⊤ : GrothendieckTopology C).Covers S f := by
  exact
    monotone_covers (bot_le : (⊥ : GrothendieckTopology C) ≤ (⊤ : GrothendieckTopology C)) S f h

/-!
## Section 4 : the bridge between the arrow form and the bundled covers

Mathlib's `J.Cover X` is the subtype of the covering sieves of `X` — the
"bundled" cover. The arrow form and this presentation are two faces of the
same object: a bundled cover covers every arrow towards its object
(`covers_of_cover`, an instantiation of the arrow form of `pullback_stable`),
and conversely a cover in arrow form `J.Covers S f` generates the bundled
cover `S.pullback f` (`cover_of_covers`). The bidirectional bridge
`covers_iff_cover` closes the section: the arrow form is equivalent to the
existence of the underlying bundled cover.
-/

/-- A bundled cover covers every arrow towards its object:
    `(S : J.Cover X)` implies `J.Covers (S : Sieve X) f`.
    Proof: arrow form of `pullback_stable` — `S.condition` is the membership
    of the underlying sieve in the topology, and `pullback_stable` provides
    the membership of the pullback. -/
theorem covers_of_cover {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    {S : J.Cover X} (f : Y ⟶ X) : J.Covers (S : Sieve X) f := by
  rw [GrothendieckTopology.covers_iff]
  exact J.pullback_stable f S.condition

/-- The arrow form generates a bundled cover: if `J.Covers S f`, then
    `S.pullback f` is a cover of `Y`.
    Proof: construction by the subtype, the hypothesis being exactly the
    membership of the pullback in the topology (`covers_iff`). -/
def cover_of_covers {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (S : Sieve X) (f : Y ⟶ X) (h : J.Covers S f) : J.Cover Y :=
  ⟨S.pullback f, h⟩

/-- The underlying sieve of `cover_of_covers` is the pullback of `S`.
    Proof: `rfl` (the construction defines exactly this sieve). -/
theorem cover_of_covers_coe {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (S : Sieve X) (f : Y ⟶ X) (h : J.Covers S f) :
    (cover_of_covers J S f h : Sieve Y) = S.pullback f := rfl

/-- The arrow form is equivalent to the existence of the underlying bundled
    cover: `J.Covers S f ↔ ∃ T : J.Cover Y, (T : Sieve Y) = S.pullback f`.
    Proof: direct direction by `cover_of_covers`, converse by the condition
    of the bundled cover (the proof of `T` is the membership of the pullback
    in the topology). -/
theorem covers_iff_cover {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (S : Sieve X) (f : Y ⟶ X) :
    J.Covers S f ↔ ∃ T : J.Cover Y, (T : Sieve Y) = S.pullback f := by
  constructor
  · intro h
    exact ⟨cover_of_covers J S f h, rfl⟩
  · rintro ⟨T, hT⟩
    rw [GrothendieckTopology.covers_iff, ← hT]
    exact T.condition

end Grothendieck.CoversExtremal_en
