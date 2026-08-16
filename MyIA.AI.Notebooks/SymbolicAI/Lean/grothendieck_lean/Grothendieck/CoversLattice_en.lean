/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 43 : indexed lattice laws of the arrow form

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Parts 1-42 established the foundations: categories, sieves, topologies,
lattice laws, pullback identities, sheaf bases, covering closure,
calibration, subcanonicity, dense topologies, sheaves, internal hom,
Čech cohomology, Mayer-Vietoris limit, Kan extensions, adjunctions, monads,
equivalences, monoidal categories, the Grothendieck construction, the
direct/exceptional image, the arrow form of the covering and the coherence
laws of the pullback pseudo-functor.
Part 39 (`TopologyLattice.lean`) established the pointwise lattice laws of
topologies — greatest lower bound, least upper bound — and their arrow-form
translations for the **binary** operations. This part completes the picture
with the **indexed** operations: the `sInf` of a family (`mem_sInf` from
Mathlib) and the `sSup` of a family (`sSup_covering`), whose arrow-form
translations `J.Covers` we provide.

The guiding thread: every pointwise statement `S ∈ J X` admits an arrow-form
twin `J.Covers S f` (via `covers_iff`, `S.pullback f ∈ J Y`). Part 39
showed the pattern for `⊓` and `⊔`; here we generalize it to indexed bounds.

The statements below complete exactly what `TopologyLattice.lean` was
missing: `sInf_covering` and `sInf_covers` (the indexed dual of the pair)
and `sSup_covers` (the arrow form of the `sSup`, absent even though
`sSup_covering` was present).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck
import Grothendieck.TopologyLattice

namespace Grothendieck.CoversLattice_en

open CategoryTheory

/-!
## Section 1 : indexed greatest lower bound (sInf)

The `CompleteLattice` instance from Mathlib defines the `sInf` of a family
of topologies as the pointwise `sInf` of the sieve families, and provides
the characterization `mem_sInf` : `S ∈ sInf s X ↔ ∀ J ∈ s, S ∈ J X`. We give
its arrow-form translation `J.Covers`.
-/

/-- The greatest lower bound of a family is pointwise: `S ∈ sInf s X` if and
    only if `S` is covered by every topology of the family.
    Proof: this is exactly `mem_sInf` from Mathlib. -/
theorem sInf_covering {C : Type*} [Category C] {s : Set (GrothendieckTopology C)}
    {X : C} (S : Sieve X) :
    S ∈ sInf s X ↔ ∀ J ∈ s, S ∈ J X := by
  exact GrothendieckTopology.mem_sInf s S

/-- Arrow-form translation of `sInf_covering`: covering by the `sInf` of a
    family is equivalent to covering by every topology of the family.
    Proof: `covers_iff` on both sides — the left member is
    `S.pullback f ∈ sInf s Y`, the right member is the quantification
    `∀ J ∈ s, S.pullback f ∈ J Y` — then `sInf_covering`. -/
theorem sInf_covers {C : Type*} [Category C] {s : Set (GrothendieckTopology C)}
    {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
    (sInf s).Covers S f ↔ ∀ J ∈ s, J.Covers S f := by
  rw [GrothendieckTopology.covers_iff]
  constructor
  · intro hS J hJ
    rw [GrothendieckTopology.covers_iff]
    exact (sInf_covering (S.pullback f)).mp hS J hJ
  · intro h
    rw [← GrothendieckTopology.covers_iff]
    exact (sInf_covering (S.pullback f)).mpr h

/-!
## Section 2 : indexed least upper bound (sSup)

The least upper bound `sSup s` of a family is the generated topology: a
sieve is covered there if and only if it is covered by **every** topology
`K` above all the members of `s`. This is the characterization of part 39
(`sSup_covering`) — the converse of the pointwise union, which is not
stable under pullback. Here we provide its arrow-form translation, which
was the missing piece.
-/

/-- Arrow-form translation of `sSup_covering`: `(sSup s).Covers S f` if and
    only if `K.Covers S f` for every topology `K` above all the members of
    `s`.
    Proof: `covers_iff` on both sides (both members are memberships
    `∈ sSup s Y` / `∈ K Y` on `S.pullback f`) then `sSup_covering`. -/
theorem sSup_covers {C : Type*} [Category C] {s : Set (GrothendieckTopology C)}
    {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
    (sSup s).Covers S f ↔
      ∀ K : GrothendieckTopology C, (∀ J ∈ s, J ≤ K) → K.Covers S f := by
  rw [GrothendieckTopology.covers_iff]
  constructor
  · intro hS K hK
    rw [GrothendieckTopology.covers_iff]
    exact (Grothendieck.TopologyLattice.sSup_covering (s := s) (S.pullback f)).mp hS K hK
  · intro h
    rw [← GrothendieckTopology.covers_iff]
    exact (Grothendieck.TopologyLattice.sSup_covering (s := s) (S.pullback f)).mpr h

end Grothendieck.CoversLattice_en
