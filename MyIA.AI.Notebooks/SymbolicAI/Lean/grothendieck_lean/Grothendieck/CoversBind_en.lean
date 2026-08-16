/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Part 46 : arrow form of the indexed transitivity (bind)

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Parts 1-45 established the foundations: categories, sieves, topologies,
lattice laws, pullback identities, sheaf bases, covering closure,
calibration, subcanonicity, dense topologies, sheaves, internal hom,
Čech cohomology, Mayer-Vietoris limit, Kan extensions, adjunctions, monads,
equivalences, monoidal categories, the Grothendieck construction, the
direct/exceptional image, the arrow form of the covering, the coherence
laws of the pullback pseudo-functor, the indexed lattice laws, the arrow
form of the extremal topologies and the arrow form of the
pushforward-pullback adjunction.

This part applies the guiding thread "arrow form" to the indexed
transitivity of coverings — the "bind" of sieves. Mathlib provides the
pointwise transitivity `GrothendieckTopology.bind_covering` and the arrow
form of the transitivity at constant covering `GrothendieckTopology.arrow_trans`,
but no law relates the arrow form `J.Covers` to the indexed sieve
`Sieve.bind S T`. Here we fill the gap with `covers_bind` (the arrow form of
the indexed transitivity: if `S` covers `f` and each sieve `T hg` covers its
domain, then the bind covers `f`), its corollaries (`covers_of_bind`, the
reverse arrow form carried by the inclusion `bind_le`; `covers_bind_id`, the
pointwise fallback on the identity) and the two underlying sieve identities,
absent from Mathlib: `bind_le` (`Sieve.bind S T ≤ S`) and `bind_top` (the
bind by the top sieve is the identity).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck.CoversBind_en

open CategoryTheory

/-!
## Section 1 : the inclusion of the bind in the sieve

The sieve `Sieve.bind S T` is contained in `S`: every arrow of the bind is a
precomposition `k ≫ g` of an arrow `g ∈ S`, and a sieve is closed under
precomposition (`S.downward_closed`). The arrow form of this inclusion is
the natural converse of `covers_bind`: if the bind covers `f`, then `S`
covers `f` (a superset of a covering is a covering).
-/

/-- The bind is contained in the starting sieve: `Sieve.bind S T ≤ S`.
    Proof: an arrow of the bind is a precomposition `k ≫ g` of an arrow
    `g ∈ S`, and a sieve is closed under precomposition (`S.downward_closed`). -/
theorem bind_le {C : Type*} [Category C] {X : C} (S : Sieve X)
    (T : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y) : Sieve.bind S T ≤ S := by
  intro Y f hf
  rcases hf with ⟨Z, g, hg, k, hkT, rfl⟩
  exact S.downward_closed k g

/-- The arrow form of the inclusion: if the bind covers `f`, then `S` covers
    `f`. Proof: `covers_iff`, monotonicity of the pullback
    (`Sieve.pullback_monotone`) with `bind_le`, then `superset_covering`. -/
theorem covers_of_bind {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (S : Sieve X) (T : ∀ ⦃Z : C⦄ ⦃g : Z ⟶ X⦄, S g → Sieve Z) (f : Y ⟶ X)
    (h : J.Covers (Sieve.bind S T) f) : J.Covers S f := by
  rw [GrothendieckTopology.covers_iff] at h ⊢
  exact J.superset_covering (Sieve.pullback_monotone f (bind_le S T)) h

/-!
## Section 2 : the arrow form of the indexed transitivity

This is the central theorem of this part, the Mathlib gap. The pointwise
transitivity `bind_covering` and its arrow form at constant covering
`arrow_trans` are two extreme faces; `covers_bind` unites them: the indexing
is carried by `T : ∀ ⦃Z⦄ ⦃g : Z ⟶ X⦄, S g → Sieve Z`, and the covering
hypothesis becomes `∀ g ∈ S, J.Covers (T hg) (𝟙 Z)` — the arrow form of
`T hg ∈ J Z`, a sieve covering the identity of its object being equivalent
to belonging to the topology. The proof uses the transitivity of the
topology, via its arrow form `J.arrow_trans` specialized at
`R := Sieve.bind S T`, then the unit of the bind `Sieve.le_pullback_bind`
which relates each `T hg` to the pullback of the bind along the arrow `g`.
-/

/-- The arrow form of the indexed transitivity: if `S` covers `f` and each
    sieve `T hg` covers its domain — `J.Covers (T hg) (𝟙 Z)`, the arrow form
    of `T hg ∈ J Z` — then the bind `Sieve.bind S T` covers `f`.
    Proof: instantiation of Mathlib's arrow form of transitivity
    (`J.arrow_trans`, R := `Sieve.bind S T`); every arrow `g ∈ S` is lifted
    by the unit of the bind `Sieve.le_pullback_bind` — `T hg` is a subsieve
    of the pullback of the bind along `g` — and the indexed hypothesis `hT`. -/
theorem covers_bind {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (S : Sieve X) (f : Y ⟶ X) (hS : J.Covers S f)
    (T : ∀ ⦃Z : C⦄ ⦃g : Z ⟶ X⦄, S g → Sieve Z)
    (hT : ∀ ⦃Z : C⦄ ⦃g : Z ⟶ X⦄ (hg : S g), J.Covers (T hg) (𝟙 Z)) :
    J.Covers (Sieve.bind S T) f := by
  exact J.arrow_trans f S (Sieve.bind S T) hS (by
    intro Z g hg
    rw [GrothendieckTopology.covers_iff]
    have hTg : J.Covers (T hg) (𝟙 Z) := hT hg
    rw [GrothendieckTopology.covers_iff] at hTg
    rw [Sieve.pullback_id] at hTg
    exact J.superset_covering (Sieve.le_pullback_bind S T g hg) hTg)

/-!
## Section 3 : the pointwise fallback

When the arrow is the identity `𝟙 X`, the arrow form falls back on the
pointwise membership: `J.Covers S (𝟙 X) ↔ S ∈ J X` (`covers_iff` +
`Sieve.pullback_id`). The indexed transitivity therefore specializes to the
pointwise version of the bind — the arrow analogue of `bind_covering` —
with a hypothesis uniformly expressed in coverings.
-/

/-- The indexed transitivity, specialized on the identity:
    `J.Covers S (𝟙 X) → (∀ g ∈ S, J.Covers (T hg) (𝟙 Z)) →
    J.Covers (Sieve.bind S T) (𝟙 X)` — the arrow analogue of `bind_covering`.
    Proof: instantiation of `covers_bind` at `f := 𝟙 X`. -/
theorem covers_bind_id {C : Type*} [Category C] {X : C} (J : GrothendieckTopology C)
    (S : Sieve X) (hS : J.Covers S (𝟙 X))
    (T : ∀ ⦃Z : C⦄ ⦃g : Z ⟶ X⦄, S g → Sieve Z)
    (hT : ∀ ⦃Z : C⦄ ⦃g : Z ⟶ X⦄ (hg : S g), J.Covers (T hg) (𝟙 Z)) :
    J.Covers (Sieve.bind S T) (𝟙 X) := by
  exact covers_bind J S (𝟙 X) hS T hT

/-!
## Section 4 : the bind by the top sieve

When each `T hg` is the top sieve, the bind recovers exactly `S`: every
arrow `g ∈ S` is precomposed by the identity (`g = 𝟙 ≫ g`), and conversely
the bind is contained in `S` (`bind_le`). This sieve identity, absent from
Mathlib, gives the arrow form: covering by
`Sieve.bind S (fun ⦃Z⦄ ⦃g : Z ⟶ X⦄ _ => ⊤)` is equivalent to covering by `S`.
-/

/-- The bind by the top sieve is the identity:
    `Sieve.bind S (fun ⦃Y⦄ ⦃f : Y ⟶ X⦄ _ => ⊤) = S`.
    Proof: antisymmetry between `bind_le` and the reverse inclusion — every
    `g ∈ S` is precomposed by the identity, `g = 𝟙 ≫ g`, and the top sieve
    accepts every arrow. -/
theorem bind_top {C : Type*} [Category C] {X : C} (S : Sieve X) :
    Sieve.bind S (fun ⦃Y : C⦄ ⦃_ : Y ⟶ X⦄ _ => (⊤ : Sieve Y)) = S := by
  apply le_antisymm
  · exact bind_le S (fun ⦃Y : C⦄ ⦃_ : Y ⟶ X⦄ _ => (⊤ : Sieve Y))
  · intro Y f hS
    exact ⟨Y, 𝟙 Y, f, hS, by simp, by simp⟩

/-- The arrow form of the bind by the top sieve:
    `J.Covers (Sieve.bind S (fun ⦃Z⦄ ⦃g : Z ⟶ X⦄ _ => ⊤)) f ↔ J.Covers S f`.
    Proof: rewrite of the identity `bind_top`. -/
theorem covers_bind_top {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (S : Sieve X) (f : Y ⟶ X) :
    J.Covers (Sieve.bind S (fun ⦃Z : C⦄ ⦃_ : Z ⟶ X⦄ _ => (⊤ : Sieve Z))) f ↔
      J.Covers S f := by
  rw [bind_top S]

end Grothendieck.CoversBind_en
