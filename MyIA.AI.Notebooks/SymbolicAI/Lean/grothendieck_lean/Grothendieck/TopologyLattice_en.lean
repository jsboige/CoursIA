/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Grothendieck Homage — Part 39 : lattice laws of the topologies

Alexandre Grothendieck (1928-2014).

Phase 5 extension (#2159, EPIC #1646).

Parts 1-38 established the fundamentals : categories, sieves, topologies,
lattice laws, pullback identities, sheaf bases, covering closure,
calibration, subcanonicity, dense topologies, sheaves, internal hom, Cech
cohomology, Mayer-Vietoris limit, Kan extensions, adjunctions, monads,
equivalences, monoidal categories, limits and colimits, comma couples,
direct images, proper theorems on the arrow form (`J.Covers S f`), on the
bundled cover (`J.Cover X`), the pullback pseudofunctor coherence laws
(Part 37) and the pullback functor laws (Part 38).

Part 39 establishes the **lattice laws of the Grothendieck topologies** :
Mathlib provides the complete lattice structure on `GrothendieckTopology C`
(`CompleteLattice` instance, built from the pointwise-intersection `sInf`),
but does **not** provide the covering characterizations of the lattice
operations. This module states and proves them :

  - `le_covering` : the order is pointwise — `J₁ ≤ J₂` if and only if every
    sieve `S ∈ J₁ X` also belongs to `J₂ X`.
  - `le_covers` : the order is compatible with the arrow form —
    `J₁ ≤ J₂ → J₁.Covers S f → J₂.Covers S f`.
  - `inf_covering` / `inf_covers` : `S ∈ (J₁ ⊓ J₂) X` if and only if
    `S ∈ J₁ X` **and** `S ∈ J₂ X` — the intersection of topologies is the
    pointwise intersection of the covering sieves.
  - `sup_covering` / `sup_covers` : the join is the **generated topology** —
    `S ∈ (J₁ ⊔ J₂) X` if and only if `S` is covered by every topology `K`
    above both `J₁` and `J₂` (upper-bound characterization ; the pointwise
    union is not enough, it is not pullback-stable).
  - `sSup_covering` : the infinite version — `S ∈ sSup s X` if and only if
    `S` is covered by every upper bound of the family `s`.

Each proof is a **real tactic proof** (DEEP vein) : the lattice axioms
(`le_sInf`, `sInf_le`, `le_sSup`, `sSup_le`, `le_inf`, `inf_le_left` /
`inf_le_right`, `sup_le`, `le_sup_left` / `le_sup_right`) plus `le_covering`
reducing the order/covering compatibility. No proof is a re-export.

EPIC #1646, Phase 5 (#2159). All `sorry`s eliminated at creation.

### i18n convention (EPIC #4980 ratified by user 2026-07-04)

This module is paired with its French twin in the sibling file
`TopologyLattice.lean` (sibling pair model, see PR #6154 for the pilot on
`Utility.lean`). The `_en` suffix is applied to this English file's namespace
(anti-collision, per code-style.md #4980). Theorem statements, lemma names,
Lean tactics and Mathlib references remain in English ; only the docstrings
`/-- ... -/` and comments `-- ...` differ between the two files
(byte-identity preservation).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck.TopologyLattice_en

open CategoryTheory

/-!
## Section 1 : order and arrow form

The order on `GrothendieckTopology C` is the pointwise order on the families
of sieves (`le_def` of Mathlib). The arrow form `J.Covers S f` is defined by
`S.pullback f ∈ J Y` (Mathlib, `covers_iff`). This section relates the two.
-/

/-- The order of topologies is pointwise : `J₁ ≤ J₂` if and only if every
    sieve covered by `J₁` is covered by `J₂`.
    Proof : `le_def` then the pointwise order of functions (definitional),
    decomposed into pointwise memberships. -/
theorem le_covering {C : Type*} [Category C] {J₁ J₂ : GrothendieckTopology C} :
    J₁ ≤ J₂ ↔ ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J₁ X → S ∈ J₂ X := by
  rw [GrothendieckTopology.le_def]
  constructor
  · intro h X S hS
    exact h X hS
  · intro h X S hS
    exact h S hS

/-- The order is compatible with the arrow form : if `J₁ ≤ J₂`, any sieve
    covered by `J₁` along `f` is also covered by `J₂`.
    Proof : `covers_iff` on both sides (both members are `∈ J₁ Y` / `∈ J₂ Y`)
    then `le_covering`. -/
theorem le_covers {C : Type*} [Category C] {X Y : C} {J₁ J₂ : GrothendieckTopology C}
    (S : Sieve X) (f : Y ⟶ X) :
    J₁ ≤ J₂ → J₁.Covers S f → J₂.Covers S f := by
  intro h₁₂ hc
  rw [GrothendieckTopology.covers_iff] at hc ⊢
  exact le_covering.mp h₁₂ (S.pullback f) hc

/-!
## Section 2 : infimum (inf)

The infimum `J₁ ⊓ J₂` of two topologies is the `sInf` of the pair (the
infimum of the complete lattice), and by `mem_sInf` of Mathlib its pointwise
characterization is the intersection of the covering sieves. This section
proves these characterizations and their translation to the arrow form.
-/

/-- The infimum of a pair is the `sInf` of the pair : `J₁ ⊓ J₂ = sInf {J₁, J₂}`.
    Proof : `le_antisymm` — on one side `le_sInf` with `inf_le_left` /
    `inf_le_right`, on the other `le_inf` with `sInf_le` twice. -/
lemma inf_eq_sInf {C : Type*} [Category C] {J₁ J₂ : GrothendieckTopology C} :
    J₁ ⊓ J₂ = sInf {J₁, J₂} := by
  apply le_antisymm
  · apply le_sInf
    intro J hJ
    simp at hJ
    rcases hJ with rfl | rfl
    · exact inf_le_left
    · exact inf_le_right
  · apply le_inf
    · apply sInf_le
      simp
    · apply sInf_le
      simp

/-- The intersection of two topologies is the pointwise intersection :
    `S ∈ (J₁ ⊓ J₂) X` if and only if `S ∈ J₁ X` and `S ∈ J₂ X`.
    Proof : `inf_eq_sInf` then `mem_sInf` of Mathlib, and decomposing the
    membership in the pair `{J₁, J₂}`. -/
theorem inf_covering {C : Type*} [Category C] {X : C} {J₁ J₂ : GrothendieckTopology C}
    (S : Sieve X) :
    S ∈ (J₁ ⊓ J₂) X ↔ S ∈ J₁ X ∧ S ∈ J₂ X := by
  rw [inf_eq_sInf]
  rw [GrothendieckTopology.mem_sInf]
  constructor
  · intro h
    exact ⟨h J₁ (by simp), h J₂ (by simp)⟩
  · intro h K hK
    simp at hK
    rcases hK with rfl | rfl
    · exact h.1
    · exact h.2

/-- Translation of `inf_covering` to the arrow form : covering by `J₁ ⊓ J₂`
    is equivalent to covering by `J₁` and by `J₂`.
    Proof : `covers_iff` three times (the three members are memberships
    `∈ (J₁ ⊓ J₂) Y` / `∈ J₁ Y` / `∈ J₂ Y`) then `inf_covering`. -/
theorem inf_covers {C : Type*} [Category C] {X Y : C} {J₁ J₂ : GrothendieckTopology C}
    (S : Sieve X) (f : Y ⟶ X) :
    (J₁ ⊓ J₂).Covers S f ↔ J₁.Covers S f ∧ J₂.Covers S f := by
  rw [GrothendieckTopology.covers_iff, GrothendieckTopology.covers_iff,
    GrothendieckTopology.covers_iff]
  exact inf_covering (S.pullback f)

/-!
## Section 3 : supremum (sup, sSup)

The join `J₁ ⊔ J₂` of two topologies is the **generated topology** by the
union of the sieves : the smallest topology above both. The correct
characterization is therefore not the pointwise union (which is not
pullback-stable) but the upper-bound characterization : `S ∈ (J₁ ⊔ J₂) X`
if and only if `S` is covered by **every** topology above both `J₁` and
`J₂`. This section proves these characterizations together with their
infinite `sSup` version.
-/

/-- Join of a pair, covering characterization : `S ∈ (J₁ ⊔ J₂) X` if and only
    if `S ∈ K X` for every topology `K` above both `J₁` and `J₂` (the
    generated topology).
    Proof : one direction `sup_le` then `le_covering` ; the other, take
    `K = J₁ ⊔ J₂`, an upper bound of both by `le_sup_left`/`le_sup_right`. -/
theorem sup_covering {C : Type*} [Category C] {X : C} {J₁ J₂ : GrothendieckTopology C}
    (S : Sieve X) :
    S ∈ (J₁ ⊔ J₂) X ↔
      ∀ K : GrothendieckTopology C, J₁ ≤ K → J₂ ≤ K → S ∈ K X := by
  constructor
  · intro hS K h₁K h₂K
    exact le_covering.mp (sup_le h₁K h₂K) S hS
  · intro h
    exact h (J₁ ⊔ J₂) le_sup_left le_sup_right

/-- Translation of `sup_covering` to the arrow form.
    Proof : `covers_iff` twice then `sup_covering`. -/
theorem sup_covers {C : Type*} [Category C] {X Y : C} {J₁ J₂ : GrothendieckTopology C}
    (S : Sieve X) (f : Y ⟶ X) :
    (J₁ ⊔ J₂).Covers S f ↔
      ∀ K : GrothendieckTopology C, J₁ ≤ K → J₂ ≤ K → K.Covers S f := by
  rw [GrothendieckTopology.covers_iff]
  constructor
  · intro hS K h₁K h₂K
    rw [GrothendieckTopology.covers_iff]
    exact le_covering.mp (sup_le h₁K h₂K) (S.pullback f) hS
  · intro h
    rw [← GrothendieckTopology.covers_iff]
    exact h (J₁ ⊔ J₂) le_sup_left le_sup_right

/-- Supremum of a family, covering characterization : `S ∈ sSup s X` if and
    only if `S ∈ K X` for every upper bound `K` of the family `s`.
    Proof : one direction `sSup_le` then `le_covering` ; the other, take
    `K = sSup s`, an upper bound of the family by `le_sSup`. -/
theorem sSup_covering {C : Type*} [Category C] {X : C} (s : Set (GrothendieckTopology C))
    (S : Sieve X) :
    S ∈ sSup s X ↔ ∀ K : GrothendieckTopology C, (∀ J ∈ s, J ≤ K) → S ∈ K X := by
  constructor
  · intro hS K hK
    exact le_covering.mp (sSup_le hK) S hS
  · intro h
    exact h (sSup s) fun J hJ => le_sSup hJ

end Grothendieck.TopologyLattice_en
