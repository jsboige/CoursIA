/-
## Categories, sieves and Grothendieck topologies (Part 1 — Grothendieck tribute)

Grothendieck tribute — Part 1: underlying categories, sieves and the axioms of
Grothendieck topologies.

Alexandre Grothendieck (1928-2014).

Phase 2 extension (#2159, Epic #2162).

This introductory module presents the Mathlib 4 formalization of the
fundamental concepts of the theory of Grothendieck sites (SGA 4 II §1-3):

  - `Sieve X`: sieve on an object X (subfunctor of the Yoneda embedding at X),
    forms a **complete lattice** via `inferInstance`
  - `GrothendieckTopology C`: function assigning to each X a set of covering
    sieves satisfying **three axioms** (top_mem, pullback_stable, transitive)
  - `GrothendieckTopology.trivial`: the trivial topology (the coarsest,
    **bottom** ⊥ of the lattice of topologies)
  - `GrothendieckTopology.discrete`: the discrete topology (the finest,
    **top** ⊤ of the lattice of topologies)
  - `GrothendieckTopology.dense`: the dense topology (S covers X iff every
    morphism Y → X admits a factor in S)
  - `top_covers`: axiom 1 — the maximal sieve is always covering (stability
    under identity)
  - `pullback_cover`: axiom 2 — covering sieves are stable under pullback
    (locality, see c.393 SieveLattice for the functorial pullback axioms)
  - `transitivity`: axiom 3 — local character (transitivity)
  - `trivial_eq_bot` / `discrete_eq_top`: the trivial topology is the
    **bottom** ⊥ and the discrete topology is the **top** ⊤ of the complete
    lattice of Grothendieck topologies on C

The key intuition (Grothendieck's "categorical turn"): replacing
**topological spaces** (in the sense of Bourbaki) by **categories equipped with
a topology** defined by covering sieves. This generalization revolutionized
algebraic geometry by making it possible to define **sheaves** on schemes,
fields, toposes — well beyond classical topological spaces.

Epic #1646, Phase 2 (#2159). All `sorry`s eliminated at creation.

### Calibration harness tribute + Phase 2+ rollout of grothendieck_lean (#4980)

9th sub-module of the `grothendieck_lean` Phase 2+ rollout — direct structural
analogue of c.388 `SieveOps` (5th, lattice ⊥ ≤ J ≤ ⊤, 9 theorems) + c.389
`CanonicalProps` (6th, canonical topology, 8 theorems) + c.390 `SieveGenerate`
(7th, Galois insertion + idempotence, 7 theorems) + c.393 `SieveLattice` (8th,
functorial pullback axioms, 4 theorems) = continuity of the `grothendieck_lean`
Phase 2+ register opened post-c.390 = **4th R6 Sustained intra-R6 cycle on the
`grothendieck_lean` register post-c.391** = return to Phase 2+ post-c.392
ACHEVÉ 9/9 `conway_lean` Phase 1+.

### Real substance — underlying categories + Grothendieck topology axioms (SGA 4 II §1-3)

The block introduces the **5 theorems** (canonical axioms + lattice bounds)
and **5 examples** (instances + canonical topologies) formal on the theory of
Grothendieck sites:

- **`top_covers`**: `(⊤ : Sieve X) ∈ J.sieves X` (the maximal sieve is
  covering — axiom 1) — reduces to `J.top_mem X`
- **`pullback_cover`**: if `S ∈ J.sieves X` then `S.pullback f ∈ J.sieves Y`
  (stability under pullback — axiom 2, locality) — reduces to
  `J.pullback_stable f hS`
- **`transitivity`**: axiom 3 — if `S` covers `X` and every morphism in `S`
  admits a covering pullback `R`, then `R` covers `X` — reduces to
  `J.transitive hS R hR`
- **`trivial_eq_bot`**: `GrothendieckTopology.trivial C = ⊥` (lower bound of
  the lattice of topologies)
- **`discrete_eq_top`**: `GrothendieckTopology.discrete C = ⊤` (upper bound of
  the lattice of topologies)

This module formalizes:
- `top_covers`: axiom 1 — maximal sieve covering
- `pullback_cover`: axiom 2 — stability under pullback
- `transitivity`: axiom 3 — local character
- `trivial_eq_bot`: trivial topology = ⊥ of the lattice
- `discrete_eq_top`: discrete topology = ⊤ of the lattice
- + 4 `example`: instances `CompleteLattice (Sieve X)`,
  `CompleteLattice (GrothendieckTopology C)`, canonical topologies
  `trivial`/`discrete`/`dense`

The Mathlib bridge used = `Mathlib.CategoryTheory.Sites.Grothendieck` (1
byte-identical LF import). All `sorry`s were eliminated (Epic #1453). **Density
1.317 thm/KB** (5/3795) — direct structural analogue of c.388 SieveOps (1.864
thm/KB, 9 theorems) + c.390 SieveGenerate (1.424 thm/KB, 7 theorems) + c.393
SieveLattice (1.339 thm/KB, 4 theorems); modest density because the substance
= fundamental canonical axioms (1 axiom = 1 line of the mathematical
definition, like `J.top_mem X`) without any cohomological construction.

### Accessibility note Epic #1452/#1453 — purely theoretical kernel

As c.388 SieveOps + c.389 CanonicalProps + c.390 SieveGenerate + c.393
SieveLattice, this module is entirely **tractable** by the Lean 4 prover +
Mathlib 4 = SOTA-OK: the 5 theorems use the canonical tactics (`J.top_mem X` +
`J.pullback_stable f hS` + `J.transitive hS R hR` +
`GrothendieckTopology.trivial_eq_bot` + `GrothendieckTopology.discrete_eq_top`)
which are the **standard Mathlib proof engines** for these canonical
statements. The **decidability coefficient** is 100 %: each axiom is directly
a structure field of `GrothendieckTopology` (Mathlib 4).

The 4 `example` are **direct instantiations** via `inferInstance`
(CompleteLattice) or `GrothendieckTopology.trivial` / `discrete` / `dense`
(canonical Mathlib 4 constants) — purely declarative, zero proof tactics.

### MathOverflow tribute + Mathlib i18n convention #4980

Tribute to a MathOverflow contribution on the **introduction to Grothendieck
sites** (the categorical formalization of topological spaces via the covering
sieves of SGA 4 II §1-3) + Mathlib i18n convention #4980 ratified by the user
on 2026-07-04 (pragmatic Option A: two distinct top-level `/` blocks, without
an internal `---`, as in c.366-c.393).

### Cycle L335 anti-monoculture Sustained — c.394 = 4th R6 Sustained intra-R6 cycle `grothendieck_lean` ≠ `conway_lean` ≠ `knot_lean` post-c.391

- c.388 = 1st R6 Sustained intra-R6 cycle on the `grothendieck_lean` register
  ≠ `conway_lean` ≠ `knot_lean` post-c.387
- c.389 = 2nd R6 Sustained intra-R6 cycle on the `grothendieck_lean` register
  ≠ `conway_lean` ≠ `knot_lean` post-c.388
- c.390 = 3rd R6 Sustained intra-R6 cycle on the `grothendieck_lean` register
  ≠ `conway_lean` ≠ `knot_lean` post-c.389 = c.391 = strict PIVOT mandated
  R5.4b MUST anti-tunneling
- c.391 = strict PIVOT mandated R5.4b MUST anti-tunneling post-c.388-c.390 =
  return to the `conway_lean` Phase 1+ satellites = 1st R6 Sustained intra-R6
  cycle `conway_lean` ≠ `grothendieck_lean` ≠ `knot_lean` post-c.386
- c.392 = 2nd R6 Sustained intra-R6 cycle on the `conway_lean` register ≠
  `grothendieck_lean` ≠ `knot_lean` post-c.391 = Phase 1+ rollout ACHEVÉ 9/9
  `conway_lean`
- c.393 = 3rd R6 Sustained intra-R6 cycle on the `grothendieck_lean` register
  ≠ `conway_lean` ≠ `knot_lean` post-c.391 = return to the Phase 2+ register
  opened post-c.390 = 8th sub-module of the `grothendieck_lean` Phase 2+
  rollout
- **c.394 = 4th R6 Sustained intra-R6 cycle on the `grothendieck_lean`
  register** = continuation of the Phase 2+ register opened post-c.393 =
  coherence with post-c.392 ACHEVÉ 9/9 `conway_lean` Phase 1+ = **9th
  sub-module of the `grothendieck_lean` Phase 2+ rollout = `CategoryAndSites`**
  = SGA 4 II §1-3 underlying categories + canonical topology axioms + lattice
  of topologies.
- Post-c.394 backlog c.395+: the other `grothendieck_lean` Phase 2+ modules
  remaining (13 after c.394: Calibration, Subcanonical, DenseTopology,
  CoverageGen, SheafHom, SheafCohomology/{MayerVietoris,Basic}, ConstantSheaf,
  ZariskiSite, Conservative, MayerVietorisSquare, SitePoints, SchemesTour,
  LeftExact, SheafCohomology/Cech) OR Conway/Life/* 13 files OR the 3
  remaining Lemmas OR non-Lean #5985/#6051 OR GPU #5105 po-2024.

All `sorry`s were eliminated (Epic #1453, #1646).
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
