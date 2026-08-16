/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Part 45 : arrow form of the pushforward-pullback adjunction

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Parts 1-44 established the foundations: categories, sieves, topologies,
lattice laws, pullback identities, sheaf bases, covering closure,
calibration, subcanonicity, dense topologies, sheaves, internal hom,
Čech cohomology, Mayer-Vietoris limit, Kan extensions, adjunctions, monads,
equivalences, monoidal categories, the Grothendieck construction, the
direct/exceptional image, the arrow form of the covering, the coherence
laws of the pullback pseudo-functor, the indexed lattice laws and the arrow
form of the extremal topologies.

This part applies the guiding thread "arrow form" to the pushforward-pullback
adjunction of sieves. Mathlib provides the adjunction
`Sieve.galoisConnection (Sieve.pushforward f) (Sieve.pullback f)` with its
unit/counit (`Sieve.le_pushforward_pullback`, `Sieve.pullback_pushforward_le`),
its monotonicity and its equalities (`Sieve.pushforward_comp`,
`Sieve.pushforward_union`), but no law of the arrow form `J.Covers` is
attached to it. Here we provide: the covering of the pushforward of a
covering (`covers_pushforward_of_mem`), the arrow form of the monotonicity,
of the composition and of the union, the behaviour at the identity, and the
fixed points of the adjunction — for `f` mono, `(S.pushforward f).pullback f = S`
(coinsertion) ; for `f` split epi, `(R.pullback f).pushforward f = R`
(insertion) — proved by antisymmetry, and their arrow forms.
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck.CoversPushforward_en

open CategoryTheory

/-!
## Section 1 : the unit of the adjunction in arrow form

The unit `Sieve.le_pushforward_pullback` says `S ≤ (S.pushforward f).pullback f`.
With the topology property `superset_covering`, a membership
`S ∈ J Y` therefore transports to the covering `J.Covers (S.pushforward f) f`:
the pushforward of a covering along `f` covers `f` itself.
-/

/-- The pushforward of a covering covers the arrow along which we push:
    `S ∈ J Y → J.Covers (S.pushforward f) f`.
    Proof: `covers_iff` reduces to `(S.pushforward f).pullback f ∈ J Y`, then
    `superset_covering` with the unit `Sieve.le_pushforward_pullback`. -/
theorem covers_pushforward_of_mem {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (f : Y ⟶ X) (S : Sieve Y) (hS : S ∈ J Y) :
    J.Covers (S.pushforward f) f := by
  rw [GrothendieckTopology.covers_iff]
  exact J.superset_covering (Sieve.le_pushforward_pullback f S) hS

/-!
## Section 2 : monotonicity, composition and union in arrow form

`Sieve.pushforward_monotone` and the equalities `Sieve.pushforward_comp` /
`Sieve.pushforward_union` translate directly into laws of the arrow form:
the covering by a pushforward is monotone in the sieve, and invariant under
the structural rewrites of composition and union.
-/

/-- The arrow form is monotone in the sieve: if `A ≤ B` and `A.pushforward f`
    covers `g`, then `B.pushforward f` covers `g`.
    Proof: monotonicity of the pushforward (`Sieve.pushforward_monotone`), then
    monotonicity of the pullback (`Sieve.pullback_monotone`) and `superset_covering`. -/
theorem covers_pushforward_monotone {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (f : Y ⟶ X) {A B : Sieve Y} (hAB : A ≤ B) {Z : C} (g : Z ⟶ X)
    (h : J.Covers (A.pushforward f) g) :
    J.Covers (B.pushforward f) g := by
  rw [GrothendieckTopology.covers_iff] at h ⊢
  exact J.superset_covering (Sieve.pullback_monotone g (Sieve.pushforward_monotone f hAB)) h

/-- The arrow form commutes with the composition of pushforwards:
    `J.Covers (S.pushforward (g ≫ f)) t ↔ J.Covers ((S.pushforward g).pushforward f) t`.
    Proof: rewrite of the equality `Sieve.pushforward_comp`. -/
theorem covers_pushforward_comp {C : Type*} [Category C] {X Y Z : C} (J : GrothendieckTopology C)
    (S : Sieve Z) (f : Y ⟶ X) (g : Z ⟶ Y) {W : C} (t : W ⟶ X) :
    J.Covers (S.pushforward (g ≫ f)) t ↔ J.Covers ((S.pushforward g).pushforward f) t := by
  rw [Sieve.pushforward_comp]

/-- The arrow form distributes over the union of sieves:
    `J.Covers ((S ⊔ R).pushforward f) t ↔ J.Covers (S.pushforward f ⊔ R.pushforward f) t`.
    Proof: rewrite of the equality `Sieve.pushforward_union`. -/
theorem covers_pushforward_union {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (f : Y ⟶ X) (S R : Sieve Y) {Z : C} (t : Z ⟶ X) :
    J.Covers ((S ⊔ R).pushforward f) t ↔ J.Covers (S.pushforward f ⊔ R.pushforward f) t := by
  rw [Sieve.pushforward_union]

/-!
## Section 3 : the pushforward along the identity

The pushforward along `𝟙 X` is the identity on sieves. Mathlib does not
provide this identity; we prove it by extensionality (a sieve contains `f`
if and only if `f ≫ 𝟙 X` belongs to it). The arrow form of this identity then
falls back exactly on the pointwise membership.
-/

/-- The pushforward along the identity is the identity: `S.pushforward (𝟙 X) = S`.
    Proof: `Sieve.ext` — the left member contains `f` iff
    `∃ g, g ≫ 𝟙 X = f ∧ S g`, which is equivalent to `S f`
    (`Category.comp_id`). -/
theorem pushforward_id {C : Type*} [Category C] {X : C} (S : Sieve X) :
    S.pushforward (𝟙 X) = S := by
  ext Y f
  constructor
  · rintro ⟨g, hg, hS⟩
    rwa [← hg, Category.comp_id]
  · intro hS
    exact ⟨f, by simp, hS⟩

/-- The arrow form of the pushforward of the identity above the identity
    coincides with the pointwise membership:
    `J.Covers (S.pushforward (𝟙 X)) (𝟙 X) ↔ S ∈ J X`.
    Proof: `pushforward_id`, then `covers_iff` and `Sieve.pullback_id`. -/
theorem covers_pushforward_id {C : Type*} [Category C] {X : C} (J : GrothendieckTopology C)
    (S : Sieve X) :
    J.Covers (S.pushforward (𝟙 X)) (𝟙 X) ↔ S ∈ J X := by
  rw [pushforward_id]
  rw [GrothendieckTopology.covers_iff, Sieve.pullback_id]

/-!
## Section 4 : the fixed points of the adjunction

Mathlib provides the two faces of the adjunction: for `f` mono,
`Sieve.galoisCoinsertionOfMono` (coreflective); for `f` split epi,
`Sieve.galoisInsertionOfIsSplitEpi` (reflective). The properties `u_l_le` and
`le_l_u` each give an inequality; combined with the opposite unit/counit,
antisymmetry provides the exact fixed points, which Mathlib does not give.
We prove them here, then derive their arrow forms.
-/

/-- Fixed point of the coinsertion: for `f` mono, `(S.pushforward f).pullback f = S`.
    Proof: antisymmetry between the unit `Sieve.le_pushforward_pullback` and
    the property `u_l_le` of `Sieve.galoisCoinsertionOfMono`. -/
theorem pushforward_pullback_fixed {C : Type*} [Category C] {X Y : C} {f : Y ⟶ X} [Mono f]
    (S : Sieve Y) :
    (S.pushforward f).pullback f = S := by
  exact le_antisymm ((Sieve.galoisCoinsertionOfMono f).u_l_le S)
    (Sieve.le_pushforward_pullback f S)

/-- Arrow form of the fixed point of the coinsertion: for `f` mono,
    `J.Covers (S.pushforward f) f ↔ J.Covers S (𝟙 Y)`.
    Proof: `covers_iff` on both sides, `Sieve.pullback_id`, then the fixed
    point `pushforward_pullback_fixed`. -/
theorem covers_pushforward_fixed_mono {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    {f : Y ⟶ X} [Mono f] (S : Sieve Y) :
    J.Covers (S.pushforward f) f ↔ J.Covers S (𝟙 Y) := by
  rw [GrothendieckTopology.covers_iff, GrothendieckTopology.covers_iff, Sieve.pullback_id]
  rw [pushforward_pullback_fixed S]

/-- Fixed point of the insertion: for `f` split epi, `(R.pullback f).pushforward f = R`.
    Proof: antisymmetry between the counit `Sieve.pullback_pushforward_le` and
    the property `le_l_u` of `Sieve.galoisInsertionOfIsSplitEpi`. -/
theorem pullback_pushforward_fixed {C : Type*} [Category C] {X Y : C} {f : Y ⟶ X} [IsSplitEpi f]
    (R : Sieve X) :
    (R.pullback f).pushforward f = R := by
  exact le_antisymm (Sieve.pullback_pushforward_le f R)
    ((Sieve.galoisInsertionOfIsSplitEpi f).le_l_u R)

end Grothendieck.CoversPushforward_en
