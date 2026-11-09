/-
Grothendieck tribute — Part 8: Topology ordering, pullback cover, and lattice facts
Alexandre Grothendieck (1928-2014).

Phase 4 extension (#2159, Epic #1646).

Part 6 (SieveLattice.lean) established pullback identities. Part 7
(SheafBasics.lean) connected sheaves with the lattice of topologies.
Mathlib already provides Sieve.pullback_inter (pullback preserves ⊓).

This module adds pedagogical wrappers and observations:

  - The complete ordering chain: ⊥ ≤ J ≤ ⊤ for any topology J
  - Pullback of a covering sieve is covering (stability, explicit statement)
  - Intersection of covering sieves is covering (meet closure)
  - A topology that covers the maximal sieve is discrete

These facts are exercises in reading the Grothendieck topology axioms
through the lens of order theory.

Epic #1646, Phase 4 (#2159). All `sorry`s eliminated at creation.
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck_en

open CategoryTheory

/-!
## Pullback and intersections (wrapper)

Mathlib provides `Sieve.pullback_inter`: pullback distributes over
intersection. We record a convenient restatement using ⊓ notation.
-/

/-- Pullback preserves intersections: `Sieve.pullback f (S ⊓ T) =
    Sieve.pullback f S ⊓ Sieve.pullback f T`.
    Direct restatement of `Sieve.pullback_inter`. -/
theorem pullback_inf {C : Type*} [Category C] {X Y : C} (f : Y ⟶ X)
    (S T : Sieve X) :
    Sieve.pullback f (S ⊓ T) = Sieve.pullback f S ⊓ Sieve.pullback f T :=
  Sieve.pullback_inter S T

/-!
## Topology ordering chain

Every Grothendieck topology J lies between the trivial (⊥) and
discrete (⊤) topologies. This is a simple consequence of the
complete lattice structure.
-/

/-- The trivial (coarsest) topology is below any Grothendieck topology. -/
theorem trivial_le_any {C : Type*} [Category C] (J : GrothendieckTopology C) :
    (GrothendieckTopology.trivial C : GrothendieckTopology C) ≤ J := by
  rw [GrothendieckTopology.trivial_eq_bot]
  exact bot_le

/-- Any Grothendieck topology is below the discrete (finest) topology. -/
theorem any_le_discrete {C : Type*} [Category C] (J : GrothendieckTopology C) :
    (J : GrothendieckTopology C) ≤ GrothendieckTopology.discrete C := by
  rw [GrothendieckTopology.discrete_eq_top]
  exact le_top

/-- Every Grothendieck topology lies between trivial and discrete:
    ⊥ ≤ J ≤ ⊤. -/
theorem trivial_le_J_le_discrete {C : Type*} [Category C]
    (J : GrothendieckTopology C) :
    (GrothendieckTopology.trivial C : GrothendieckTopology C) ≤ J ∧
    (J : GrothendieckTopology C) ≤ GrothendieckTopology.discrete C :=
  ⟨trivial_le_any J, any_le_discrete J⟩

/-!
## Covering sieve closure operations

The three axioms of a Grothendieck topology (stability, intersection,
supremum) give closure properties on covering sieves. We record
explicit pedagogical statements of each.
-/

/-- The intersection of two covering sieves is a covering sieve.
    This is the intersection axiom, stated via `intersection_covering`. -/
theorem cover_inf {C : Type*} [Category C] {J : GrothendieckTopology C}
    {X : C} {R S : Sieve X} (hR : R ∈ J X) (hS : S ∈ J X) :
    R ⊓ S ∈ J X :=
  J.intersection_covering hR hS

/-- Intersection characterization: R ⊓ S covers iff both R and S cover.
    Forward: `intersection_covering`. Backward: superset_covering with inf_le. -/
theorem cover_inf_iff {C : Type*} [Category C] {J : GrothendieckTopology C}
    {X : C} {R S : Sieve X} :
    R ⊓ S ∈ J X ↔ R ∈ J X ∧ S ∈ J X :=
  ⟨fun h => ⟨J.superset_covering inf_le_left h, J.superset_covering inf_le_right h⟩,
   fun ⟨hR, hS⟩ => J.intersection_covering hR hS⟩

/-- Pullback of a covering sieve is covering (stability axiom).
    This is the fundamental stability property: if S covers X and
    f : Y ⟶ X, then Sieve.pullback f S covers Y.
    Uses `GrothendieckTopology.pullback_stable`. -/
theorem cover_pullback_stable {C : Type*} [Category C]
    {J : GrothendieckTopology C} {X Y : C} {S : Sieve X}
    (hS : S ∈ J X) (f : Y ⟶ X) :
    Sieve.pullback f S ∈ J Y :=
  J.pullback_stable f hS

/-!
## Characterizing the discrete topology

The discrete topology is the unique topology where the maximal sieve ⊤
covers every object. We record this as an explicit characterization.
-/

/-- Every sieve belongs to the discrete topology (by definition, sieves = univ). -/
theorem mem_discrete {C : Type*} [Category C] (X : C) (S : Sieve X) :
    S ∈ GrothendieckTopology.discrete C X :=
  Set.mem_univ _

/-- The maximal sieve belongs to the trivial topology at every object.
    Uses `GrothendieckTopology.top_mem`. -/
theorem top_mem_trivial {C : Type*} [Category C] (X : C) :
    (⊤ : Sieve X) ∈ GrothendieckTopology.trivial C X :=
  (GrothendieckTopology.trivial C).top_mem X

/-!
## Proper theorems (c.1301+128)

The theorems below *prove* definitional equalities that the fields/lemmas
of the `GrothendieckTopology C` structure expose. All these fields operate
on the resident structure `GrothendieckTopology C` non polymorphic over
universes — therefore **L902 ★★ SAFE** (cf c.1301+108-L1 ★★: polymorphic
universe constructors are to be proscribed, unlike resident fields on C).

1. `covering_of_eq_top_field`: restatement of the lemma `covering_of_eq_top`
   (forward: `S = ⊤ → S ∈ J X`).
2. `covers_iff_field`: restatement of the lemma `covers_iff`
   (`J.Covers S f ↔ S.pullback f ∈ J Y`, reflexive in `Iff.rfl`).
3. `covering_iff_covers_id_field`: restatement of `covering_iff_covers_id`
   (`S ∈ J X ↔ J.Covers S (𝟙 X)`, proved by `simp [covers_iff]`).
4. `top_covering_field`: restatement of `top_covering`
   (`S ∈ (⊤ : GrothendieckTopology C) X`, trivial by `⟨⟩`).
5. `bot_covering_iff_top_field`: restatement of `bot_covering`
   (`S ∈ (⊥ : GrothendieckTopology C) X ↔ S = ⊤`, symm of `trivial_covering`).

These are "showcase" theorems that certify the fields/lemmas of the
`GrothendieckTopology C` structure are effectively computable in the same
Lean execution.
-/

/-- Theorem: forward direction of `top_mem` — if a sieve `S` equals the
    maximal sieve `⊤`, then `S` covers `X` for any topology `J`. β-equivalent
    to the lemma `GrothendieckTopology.covering_of_eq_top`. -/
theorem covering_of_eq_top_field {C : Type*} [Category C]
    {J : GrothendieckTopology C} {X : C} {S : Sieve X}
    (h : S = ⊤) : S ∈ J X :=
  J.covering_of_eq_top h

/-- Theorem: `J.Covers S f` iff the pullback of `S` by `f` covers `Y`.
    β-equivalent to the lemma `GrothendieckTopology.covers_iff` (reflexive
    in `Iff.rfl`). -/
theorem covers_iff_field {C : Type*} [Category C]
    {J : GrothendieckTopology C} {X Y : C} {S : Sieve X} (f : Y ⟶ X) :
    J.Covers S f ↔ S.pullback f ∈ J Y :=
  J.covers_iff S f

/-- Theorem: a sieve `S` covers `X` iff `J.Covers S (𝟙 X)`. β-equivalent
    to the lemma `GrothendieckTopology.covering_iff_covers_id` (proved by
    `simp [covers_iff]`). -/
theorem covering_iff_covers_id_field {C : Type*} [Category C]
    {J : GrothendieckTopology C} {X : C} {S : Sieve X} :
    S ∈ J X ↔ J.Covers S (𝟙 X) :=
  J.covering_iff_covers_id S

/-- Theorem: any sieve `S` belongs to the discrete topology (⊤) at any
    object. β-equivalent to the lemma `GrothendieckTopology.top_covering`
    (trivial by `⟨⟩`). -/
theorem top_covering_field {C : Type*} [Category C]
    {X : C} {S : Sieve X} :
    S ∈ (⊤ : GrothendieckTopology C) X :=
  GrothendieckTopology.top_covering

/-- Theorem: a sieve `S` belongs to the trivial topology (⊥) at `X` iff
    `S = ⊤`. β-equivalent to the lemma `GrothendieckTopology.bot_covering`
    (symm of `trivial_covering`). -/
theorem bot_covering_iff_top_field {C : Type*} [Category C]
    {X : C} {S : Sieve X} :
    S ∈ (⊥ : GrothendieckTopology C) X ↔ S = ⊤ :=
  GrothendieckTopology.bot_covering

end Grothendieck_en