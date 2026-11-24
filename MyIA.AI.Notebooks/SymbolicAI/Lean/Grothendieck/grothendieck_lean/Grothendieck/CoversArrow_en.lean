/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Part 35 : the arrow form of covering

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Parts 1-29 established the fundamentals: categories, sieves, topologies,
lattice laws, pullback identities, sheaf bases, covering closure,
calibration, subcanonicity, dense topologies, sheaves, internal hom,
Cech cohomology, Mayer-Vietoris limits, Kan extensions, adjunctions,
monads, equivalences, monoidal categories, limits and colimits, comma
pairs, direct images.

This module records **proper theorems** on the **arrow form of covering**:
for a Grothendieck topology `J` on a category `C`, a sieve `S` on `X` and a
morphism `f : Y ⟶ X`, the notation `J.Covers S f` means that the pullback
`S.pullback f` belongs to the family `J Y` (`GrothendieckTopology.Covers`).
This is the "arrow after arrow" reading of the pullback-stability axiom: a
sieve is covering for a morphism when "its pullback along that morphism is
covering".

The theorems stated here carry **genuine tactical proofs** (DEEP vein, by
contrast with the re-export bridges of the previous parts):

  - `covers_iff_covers_id` : covering along `f` is equivalent to covering
    the pullback of `S` along the identity (covering reduces to the target).
  - `covers_monotone` : covering is monotone in the sieve.
  - `covers_inf` : covering the intersection of two sieves is equivalent to
    covering each of them (the topology is a filter).
  - `covers_union` : covering each of two sieves implies covering their
    union — one-way implication only: the topology is not descending, so
    the converse is false in general.
  - `covers_comp_iff` : covering the pullback of `S` along `g` is equivalent
    to covering `S` along `g ≫ f` (contravariance in the arrow, via
    `Sieve.pullback_comp`).
  - `inf_mem` : a sieve belongs to `J₁ ⊓ J₂` iff it belongs to `J₁` and to
    `J₂` (the infimum of two topologies is the intersection of the families).
  - `inf_covers` : the arrow form behaves likewise for the infimum.

Each proof mobilizes a distinct Mathlib lemma (`Sieve.pullback_comp`,
`Sieve.pullback_monotone`, `GrothendieckTopology.arrow_intersect`,
`GrothendieckTopology.superset_covering`, `sInf_pair`, `mem_sInf`) — no
proof is a mere re-export.

EPIC #1646, Phase 5 (#2159). All `sorry`s eliminated at creation.

### i18n convention (EPIC #4980 ratified by user 2026-07-04)

This module is paired with its French canonical version in the sibling file
`CoversArrow.lean` (sibling pair model, see PR #6154 for the pilot on
`Utility.lean`). The `_en` namespace suffix is applied to this English file
(anti-collision, per code-style.md #4980). Theorem statements, lemma names,
Lean tactics and Mathlib references stay in English; only the docstrings
`/-- ... -/` and the comments `-- ...` differ between the two files
(byte-identity preservation).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck.CoversArrow_en

open CategoryTheory

/-!
## Section 1 : first equivalences of the arrow form

Recall: `GrothendieckTopology.Covers S f` is definitionally
`S.pullback f ∈ J Y`, and `covers_iff` is the rewriting lemma
`J.Covers S f ↔ S.pullback f ∈ J Y`. The first theorem reduces covering
along an arrow to covering along the identity; the second expresses
monotonicity in the sieve.
-/

/-- Covering along `f` is equivalent to covering the pullback of `S` along
    the identity: `J.Covers S f ↔ J.Covers (S.pullback f) (𝟙 Y)`.
    Proof: unfold both arrow forms with `covers_iff`, then rewrite
    `(S.pullback f).pullback (𝟙 Y)` as `S.pullback (𝟙 Y ≫ f)` via
    `Sieve.pullback_comp` (reverse orientation) and `𝟙 Y ≫ f` as `f` via
    `Category.id_comp`. Both sides become definitionally equal and `rw`
    concludes by reflexivity. -/
theorem covers_iff_covers_id {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (S : Sieve X) (f : Y ⟶ X) :
    J.Covers S f ↔ J.Covers (S.pullback f) (𝟙 Y) := by
  rw [J.covers_iff S f, J.covers_iff (S.pullback f) (𝟙 Y),
    ← Sieve.pullback_comp, Category.id_comp]

/-- Covering is monotone in the sieve: if `S ≤ R` and `S` covers `f`, then
    `R` covers `f`.
    Proof: unfold both arrow forms with `covers_iff`, then the pullback is
    monotone (`Sieve.pullback_monotone f h : S.pullback f ≤ R.pullback f`)
    and the topology is closed under supersets
    (`GrothendieckTopology.superset_covering`). -/
theorem covers_monotone {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) {S R : Sieve X} (f : Y ⟶ X)
    (h : S ≤ R) (hS : J.Covers S f) :
    J.Covers R f := by
  rw [J.covers_iff S f] at hS
  rw [J.covers_iff R f]
  exact J.superset_covering (Sieve.pullback_monotone f h) hS

/-!
## Section 2 : intersections, unions and composition

The following two theorems exploit the lattice structure of sieves.
`covers_inf` is an equivalence (the topology is a filter: the covering
family is closed under finite intersections, `arrow_intersect`).
`covers_union` is only an implication: the topology is not descending,
the converse would be false in general.
-/

/-- Covering the intersection of two sieves is equivalent to covering each
    of them: `J.Covers (S ⊓ R) f ↔ J.Covers S f ∧ J.Covers R f`.
    Proof: the forward direction applies `covers_monotone` with
    `inf_le_left` and `inf_le_right`; the reverse direction is exactly the
    intersection axiom of the topology, `GrothendieckTopology.arrow_intersect`. -/
theorem covers_inf {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (S R : Sieve X) (f : Y ⟶ X) :
    J.Covers (S ⊓ R) f ↔ J.Covers S f ∧ J.Covers R f := by
  constructor
  · intro h
    exact ⟨covers_monotone J f inf_le_left h, covers_monotone J f inf_le_right h⟩
  · intro h
    exact J.arrow_intersect f S R h.1 h.2

/-- Covering each of two sieves implies covering their union:
    `J.Covers S f → J.Covers R f → J.Covers (S ⊔ R) f`.
    Proof: `S ≤ S ⊔ R` (`le_sup_left`), so the pullback of `S` is below the
    pullback of `S ⊔ R` (`Sieve.pullback_monotone`), and the topology is
    closed under supersets (`superset_covering`).
    The implication is one-way: since the covering family has no downward
    closure, `J.Covers (S ⊔ R) f` does not imply `J.Covers S f` in general. -/
theorem covers_union {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (S R : Sieve X) (f : Y ⟶ X)
    (hS : J.Covers S f) (_hR : J.Covers R f) :
    J.Covers (S ⊔ R) f := by
  rw [J.covers_iff S f] at hS
  rw [J.covers_iff (S ⊔ R) f]
  exact J.superset_covering (Sieve.pullback_monotone f le_sup_left) hS

/-- Covering the pullback of `S` along `g` is equivalent to covering `S`
    along `g ≫ f`: `J.Covers (S.pullback f) g ↔ J.Covers S (g ≫ f)`.
    Proof: unfold both arrow forms with `covers_iff`, then
    `Sieve.pullback_comp` (reverse orientation) identifies `(S.pullback f)
    .pullback g` with `S.pullback (g ≫ f)`. The arrow form is contravariant
    in the arrow. -/
theorem covers_comp_iff {C : Type*} [Category C] {X Y Z : C}
    (J : GrothendieckTopology C) (S : Sieve X) (f : Y ⟶ X) (g : Z ⟶ Y) :
    J.Covers (S.pullback f) g ↔ J.Covers S (g ≫ f) := by
  rw [J.covers_iff (S.pullback f) g, J.covers_iff S (g ≫ f),
    ← Sieve.pullback_comp]

/-!
## Section 3 : the infimum of two topologies

The last two theorems concern the order structure of topologies themselves.
`sInf_pair` (dual generator `to_dual` of `sSup_pair`) identifies `J₁ ⊓ J₂`
with `sInf {J₁, J₂}`, and `GrothendieckTopology.mem_sInf` expresses
membership in an intersection of families.
-/

/-- A sieve belongs to `J₁ ⊓ J₂` iff it belongs to `J₁` and to `J₂`:
    `S ∈ (J₁ ⊓ J₂) X ↔ S ∈ J₁ X ∧ S ∈ J₂ X`.
    Proof: `sInf_pair` brings `J₁ ⊓ J₂` back to `sInf {J₁, J₂}`, then
    `GrothendieckTopology.mem_sInf` restates membership as a universal
    quantification over the pair. The forward direction instantiates each
    element of the pair (membership proved by `simp`); the reverse
    direction case-splits on `t = J₁ ∨ t = J₂` (`Set.mem_insert_iff` +
    `Set.mem_singleton_iff`). -/
theorem inf_mem {C : Type*} [Category C] {X : C} (J₁ J₂ : GrothendieckTopology C)
    (S : Sieve X) :
    S ∈ (J₁ ⊓ J₂) X ↔ S ∈ J₁ X ∧ S ∈ J₂ X := by
  rw [← sInf_pair]
  rw [GrothendieckTopology.mem_sInf ({J₁, J₂} : Set (GrothendieckTopology C)) S]
  constructor
  · intro h
    exact ⟨h J₁ (by simp), h J₂ (by simp)⟩
  · rintro ⟨h₁, h₂⟩ t ht
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact h₁
    · exact h₂

/-- The arrow form behaves likewise for the infimum:
    `(J₁ ⊓ J₂).Covers S f ↔ J₁.Covers S f ∧ J₂.Covers S f`.
    Proof: unfold the three arrow forms with `covers_iff` (the pullback of
    `S` along `f` is common to the three sides), then apply `inf_mem` to
    the sieve `S.pullback f`. -/
theorem inf_covers {C : Type*} [Category C] {X Y : C}
    (J₁ J₂ : GrothendieckTopology C) (S : Sieve X) (f : Y ⟶ X) :
    (J₁ ⊓ J₂).Covers S f ↔ J₁.Covers S f ∧ J₂.Covers S f := by
  rw [(J₁ ⊓ J₂).covers_iff S f, J₁.covers_iff S f, J₂.covers_iff S f]
  exact inf_mem J₁ J₂ (S.pullback f)

end Grothendieck.CoversArrow_en
