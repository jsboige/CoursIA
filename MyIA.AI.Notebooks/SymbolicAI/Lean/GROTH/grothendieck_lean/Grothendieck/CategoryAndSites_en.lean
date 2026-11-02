/-
Grothendieck tribute — Part 1: Categories, Sieves, and Grothendieck Topologies
Alexandre Grothendieck (1928-2014).

Grothendieck revolutionized algebraic geometry by replacing topological spaces
with categories equipped with a "topology" defined by covering sieves. This file
tours the Mathlib 4 formalization of these concepts.

The key insight: a Grothendieck topology on a category C assigns to each object X
a collection of "covering sieves" satisfying three axioms:
  1. The maximal sieve always covers (stability under identity)
  2. Covering sieves are stable under pullback (locality)
  3. If S covers X and R pulls back to a covering sieve along every arrow in S,
     then R covers X (transitivity)

Epic #1646. All `sorry`s eliminated at creation.
-/
import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck_en

open CategoryTheory

/-!
## Sieves

A sieve on X is a collection of morphisms with codomain X that is downward-closed:
if f ∈ S and g compose with f, then g ≫ f ∈ S. In Mathlib, a `Sieve X` is a
subfunctor of the Yoneda embedding at X.
-/

/-- Sieves form a complete lattice: we can take intersections, unions, etc.
    Note: `Sieve X` (not `Sieve C X`) — the category is inferred. -/
example {C : Type*} [Category C] (X : C) : CompleteLattice (Sieve X) :=
  inferInstance

/-!
## Grothendieck topologies

A `GrothendieckTopology` on C is a function assigning to each X a set of covering
sieves, satisfying the three axioms: top_mem, pullback_stable, transitive.
-/

/-- The trivial topology: only the maximal sieve covers.
    This is the coarsest (bottom) topology. -/
example {C : Type*} [Category C] : GrothendieckTopology C :=
  GrothendieckTopology.trivial C

/-- The discrete topology: every sieve covers.
    This is the finest (top) topology. -/
example {C : Type*} [Category C] : GrothendieckTopology C :=
  GrothendieckTopology.discrete C

/-- The dense topology: a sieve S covers X iff for every f : Y → X,
    there exists some arrow in S that factors through f. -/
example {C : Type*} [Category C] : GrothendieckTopology C :=
  GrothendieckTopology.dense

/-!
## The three axioms

Every `J : GrothendieckTopology C` satisfies the three axioms explicitly.
-/

/-- Axiom 1: the maximal sieve is always covering. -/
theorem top_covers {C : Type*} [Category C] (J : GrothendieckTopology C) (X : C) :
    (⊤ : Sieve X) ∈ J.sieves X :=
  J.top_mem X

/-- Axiom 2: covering sieves are stable under pullback. -/
theorem pullback_cover {C : Type*} [Category C] (J : GrothendieckTopology C)
    {X Y : C} {S : Sieve X} (f : Y ⟶ X) (hS : S ∈ J.sieves X) :
    S.pullback f ∈ J.sieves Y :=
  J.pullback_stable f hS

/-- Axiom 3: the transitivity (local character) axiom.
    If S covers X and every arrow in S pulls back to a cover of R, then R covers X. -/
theorem transitivity {C : Type*} [Category C] (J : GrothendieckTopology C)
    {X : C} {S R : Sieve X} (hS : S ∈ J.sieves X)
    (hR : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S.arrows f → R.pullback f ∈ J.sieves Y) :
    R ∈ J.sieves X :=
  J.transitive hS R hR

/-!
## Grothendieck topologies form a lattice

The set of Grothendieck topologies on a category is a complete lattice,
ordered by inclusion of covering sieves.
-/

/-- Grothendieck topologies on C form a complete lattice. -/
example {C : Type*} [Category C] : CompleteLattice (GrothendieckTopology C) :=
  inferInstance

/-- The trivial topology is the bottom element. -/
theorem trivial_eq_bot {C : Type*} [Category C] :
    GrothendieckTopology.trivial C = ⊥ :=
  GrothendieckTopology.trivial_eq_bot

/-- The discrete topology is the top element. -/
theorem discrete_eq_top {C : Type*} [Category C] :
    GrothendieckTopology.discrete C = ⊤ :=
  GrothendieckTopology.discrete_eq_top

end Grothendieck_en
