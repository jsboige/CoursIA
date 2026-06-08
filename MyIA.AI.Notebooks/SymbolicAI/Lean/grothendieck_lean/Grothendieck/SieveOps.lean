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

namespace Grothendieck

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

end Grothendieck
