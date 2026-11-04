/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Part 60: The Grothendieck ↔ Lawvere–Tierney dictionary

Alexandre Grothendieck (1928-2014).

Extension of #2159 (EPIC #1646).

Part 58 established the **subobject classifier** Ω = the presheaf of sieves;
Part 59 introduced the **Lawvere–Tierney topology** as a closure operator `j`
on Ω. Part 59 ended on an explicit frontier: "the correspondence
Grothendieck topology ↔ Lawvere–Tierney topology requires an operator
`GrothendieckTopology.closure` absent from Mathlib v4.32.1; it remains out of
reach for that part".

This part closes that frontier: the dictionary is **complete and
bidirectional**. The missing operator does not need to exist in Mathlib —
it is built from the raw axioms:

  - **Direction J → j**: for any Grothendieck topology `J`, the **closure**
    `jClosure J S := {f | S.pullback f ∈ J}` is a Lawvere–Tierney topology
    (`grothendieckToLawvereTierney`). The three laws follow from the three
    axioms: extensivity via `mem_iff_pullback_eq_top` + `top_mem`;
    idempotence via the **transitivity** axiom (which is literally the
    mirror of the closure definition); meet preservation via
    `pullback_inter` + `cover_inf_iff`.
  - **Direction j → J**: for any Lawvere–Tierney topology `j`, the **dense**
    sieves `S` such that `j S = ⊤` form a Grothendieck topology
    (`lawvereTierneyToGrothendieck`). Transitivity — the only non-trivial
    axiom — follows from the monotonicity and idempotence of Part 59:
    `S ≤ j R` then `⊤ = j S ≤ j (j R) = j R`.
  - **Round trips**: the two constructions are inverse to each other — `J`
    is recovered identically (membership of covering sieves), and `j` is
    recovered identically (closure point by point).

The bridge theorem: on a category `C`, **Grothendieck topologies and
Lawvere–Tierney topologies are the same thing** — the "site" view (SGA 4)
and the "elementary topos" view (Lawvere–Tierney) coincide at the presheaf
level. This is the bridge that Mac Lane–Moerdijk call the correspondence
between topologies on a site and topologies on its presheaf topos.

All `sorry`s eliminated at creation.

### Accessibility note (Epics #1452/#1453)

This module exposes **7 `#check` verifications**, **3 constructions** (the
closure `jClosure` and the two transports of the dictionary) and **10 own
theorems**, including the two round trips. Every proof is computational:
sieve extensionality + rewriting by the identities of Part 6 and the laws of
Part 59 — no high-level tactic.

### i18n convention (EPIC #4980 ratified by user 2026-07-04)

This module is paired with its canonical French version in the sibling file
`TopologyDictionary.lean` (sibling pair model, self-contained mirror).
Namespace suffixed `_en` (collision avoidance). The `#check`s, signatures,
variables and universes are byte-identical between the two files; only the
docstrings and comments differ.
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

import Grothendieck.LawvereTierney
import Grothendieck.SieveLattice
import Grothendieck.SieveOps

universe u v

namespace Grothendieck.TopologyDictionary_en

open CategoryTheory
open Grothendieck.LawvereTierney

variable {C : Type u} [Category.{v} C]

/-!
## Section 0: Calibration

The required Mathlib material: the three axioms of `GrothendieckTopology`
(`top_mem`, `pullback_stable`, `transitive`), its two closure lemmas
(`superset_covering`, `intersection_covering`), the lattice of sieves and
the pullback. Nothing beyond what Parts 1, 6 and 8 already covered.
-/

-- CALIBRATION: the three axioms of a Grothendieck topology.
#check @GrothendieckTopology.top_mem           -- ⊤ ∈ J.sieves X (axiom 1)
#check @GrothendieckTopology.pullback_stable   -- pullback stability (axiom 2)
#check @GrothendieckTopology.transitive        -- local character (axiom 3)
-- CALIBRATION: the closure lemmas for covering sieves.
#check @GrothendieckTopology.superset_covering     -- supsieve of a covering one
#check @GrothendieckTopology.intersection_covering -- intersection of coverings
-- CALIBRATION: the lattice of sieves and the pullback (Parts 1 and 6).
#check @Sieve.pullback_top                     -- (⊤ : Sieve X).pullback f = ⊤
#check @Sieve.pullback_inter                   -- pullback distributes over ⊓

/-!
## Section 1: The membership bridge

An arrow `g` belongs to the pullback `R.pullback f` exactly when the
composite `g ≫ f` belongs to `R`; and an arrow `f` belongs to `R` exactly
when the identity belongs to the pullback `R.pullback f`. This second
bridge is the key of the dictionary: it translates "being covering"
(membership in `J`) into "being closed at the top" (equality to `⊤` in `j`).
-/

/-- `g` lives in the pullback of `R` along `f` iff the composite
    `g ≫ f` lives in `R` — a direct reading of the Mathlib definition. -/
theorem mem_pullback_iff {X Y Z : C} (R : Sieve X) (f : Y ⟶ X) (g : Z ⟶ Y) :
    (R.pullback f) g ↔ R (g ≫ f) := by
  simp [Sieve.pullback]

/-- `f` belongs to a sieve iff the identity belongs to the pullback of
    that sieve along `f`. This is the "membership ↔ pullback at the top"
    bridge carrying density of `j` over to coverage of `J`. -/
theorem mem_iff_id_mem_pullback {X Y : C} (R : Sieve X) (f : Y ⟶ X) :
    R f ↔ (R.pullback f) (𝟙 Y) := by
  rw [mem_pullback_iff, Category.id_comp]

/-!
## Section 2: Direction J → j — the closure of a Grothendieck topology

The **closure** of a sieve `S` for a topology `J`: the set of arrows `f`
such that the pullback of `S` along `f` is covering. This is the operator
Mathlib v4.32.1 does not provide — it is built from the raw axioms, and its
descent under composition is exactly axiom 2.
-/

/-- The **J-closure** of a sieve `S`: the arrows `f : Y ⟶ X` such that
    `S.pullback f` covers `Y`. Downward closure is the pullback stability
    axiom; sieve extensionality does the rest. -/
def jClosure (J : GrothendieckTopology C) {X : C} (S : Sieve X) : Sieve X where
  arrows := fun Y f => S.pullback f ∈ J Y
  downward_closed := by
    intro Y Z f hf g
    show S.pullback (g ≫ f) ∈ J Z
    rw [← pullback_pullback]
    exact J.pullback_stable g hf

/-- Belonging to the J-closure is covering after pullback — the
    definitional equality, stated as a reusable bridge. -/
theorem mem_jClosure_iff (J : GrothendieckTopology C) {X Y : C}
    (S : Sieve X) (f : Y ⟶ X) :
    (jClosure J S) f ↔ S.pullback f ∈ J Y :=
  Iff.rfl

/-- The J-closure is **natural** — the pullback diagram commutes up to
    closure. Proof: extensionality + the associativity identity
    `pullback_pullback` of Part 6. -/
theorem jClosure_pullback (J : GrothendieckTopology C) {X Y : C}
    (f : Y ⟶ X) (S : Sieve X) :
    jClosure J (S.pullback f) = (jClosure J S).pullback f := by
  ext Z g
  rw [mem_jClosure_iff, mem_pullback_iff, mem_jClosure_iff, pullback_pullback]

/-- The J-closure of a covering sieve is covering. This is the easy
    direction of transitivity: the sieve `S.pullback f` covers for every
    arrow of the closure, so the closure "contains enough" arrows. -/
theorem jClosure_mem (J : GrothendieckTopology C) {X : C} {S : Sieve X}
    (h : S ∈ J X) : jClosure J S ∈ J X := by
  have htop : jClosure J S = ⊤ := by
    ext Y f
    exact ⟨fun _ => trivial, fun _ => J.pullback_stable f h⟩
  rw [htop]
  exact J.top_mem X

/-- A sieve whose closure covers is covering — the non-trivial
    direction, which IS the transitivity axiom: the closure of `S` covers
    and each of its arrows pulls `S` back to a covering sieve, so `S`
    covers. The proof is the exact mirror of the definition of `jClosure`. -/
theorem mem_of_mem_jClosure (J : GrothendieckTopology C) {X : C} {S : Sieve X}
    (h : jClosure J S ∈ J X) : S ∈ J X :=
  J.transitive h S (fun _ _ hf => hf)

/-- The central bridge of the J → j direction — the closure of a sieve
    is covering if and only if the sieve is. The J-closure creates no new
    coverage: it dilates each sieve to the largest sieve with the same
    local coverage. -/
theorem covering_iff_jClosure (J : GrothendieckTopology C) {X : C}
    {S : Sieve X} :
    jClosure J S ∈ J X ↔ S ∈ J X :=
  ⟨mem_of_mem_jClosure J, jClosure_mem J⟩

/-- **J → j direction of the dictionary**: every Grothendieck topology
    induces a Lawvere–Tierney topology — its closure. Extensivity: an arrow
    of `S` makes its pullback maximal (`mem_iff_pullback_eq_top`, Part 6),
    hence covering (axiom 1). Idempotence: via the central bridge. Meets:
    the pullback distributes over ⊓ (Part 6) and the intersection of
    coverings covers (Part 8). -/
def grothendieckToLawvereTierney (J : GrothendieckTopology C) :
    LawvereTierney C where
  closure := fun X => jClosure J
  maps_pullback := fun _ _ f S => jClosure_pullback J f S
  extensive := by
    intro X S Y f hf
    show S.pullback f ∈ J _
    rw [(mem_iff_pullback_eq_top S f).1 hf]
    exact J.top_mem _
  idempotent := by
    intro X S
    ext Z g
    rw [mem_jClosure_iff, ← jClosure_pullback, covering_iff_jClosure,
      mem_jClosure_iff]
  preserve_meet := by
    intro X S T
    ext Z g
    rw [mem_jClosure_iff, Sieve.inter_apply, mem_jClosure_iff, mem_jClosure_iff,
      Sieve.pullback_inter, cover_inf_iff]

/-!
## Section 3: Direction j → J — the dense sieves of a Lawvere–Tierney topology

The sieves that `j` sends to the maximal sieve are the **dense** ones. The
three axioms of a Grothendieck topology all hold: the top is dense (`j_top`,
Part 59), pullback stability is the naturality of `j`, and transitivity is
the chain `S ≤ j R` then `⊤ = j S ≤ j (j R) = j R` — monotonicity then
idempotence.
-/

/-- **j → J direction of the dictionary**: every Lawvere–Tierney topology
    induces a Grothendieck topology — its dense sieves `j S = ⊤`. The proof
    of transitivity is the central chain of the dictionary: every arrow of
    `S` is in `j R` (the identity lives in a pullback become maximal), then
    the monotonicity and idempotence of Part 59 lift `j R` above `⊤`. -/
def lawvereTierneyToGrothendieck (j : LawvereTierney C) :
    GrothendieckTopology C where
  sieves X := {S | j.closure X S = ⊤}
  top_mem' := by
    intro X
    exact j_top j X
  pullback_stable' := by
    intro X Y S f hS
    have hS' : j.closure X S = ⊤ := hS
    show j.closure Y (S.pullback f) = ⊤
    rw [j.maps_pullback, hS', Sieve.pullback_top]
  transitive' := by
    intro X S hS R hR
    have hS' : j.closure X S = ⊤ := hS
    have hsub : S ≤ j.closure X R := by
      intro Y f hf
      have hd : j.closure Y (R.pullback f) = ⊤ := hR hf
      rw [mem_iff_id_mem_pullback, ← j.maps_pullback, hd]
      trivial
    have hmono : j.closure X S ≤ j.closure X (j.closure X R) :=
      j_monotone j hsub
    rw [j.idempotent, hS'] at hmono
    show j.closure X R = ⊤
    exact le_antisymm le_top hmono

/-!
## Section 4: The round trips — the dictionary is a bijection

The two transports are inverse to each other. The first round trip reads on
covering sieves: `S` is dense for the closure of `J` exactly when `S`
covers for `J`. The second reads on the operators: the closure extracted
from the dense sieves of `j` gives `j` back point by point.
-/

/-- First round trip, in membership — the dense sieves of the closure
    of `J` are exactly the covering sieves of `J`. Forward direction: the
    identity lives in a maximal closure, and the pullback along the
    identity is `S` itself (`pullback_id`, Part 6). Backward direction:
    pullback stability, arrow by arrow. -/
theorem mem_lawvereTierney_toGrothendieck_iff (J : GrothendieckTopology C)
    {X : C} {S : Sieve X} :
    S ∈ lawvereTierneyToGrothendieck
        (grothendieckToLawvereTierney J) X ↔ S ∈ J X := by
  constructor
  · intro h
    rw [← GrothendieckTopology.mem_sieves_iff_coe] at h
    simp only [lawvereTierneyToGrothendieck, grothendieckToLawvereTierney,
      Set.mem_setOf_eq] at h
    have h1 : (jClosure J S) (𝟙 X) := by
      rw [h]
      trivial
    rw [mem_jClosure_iff] at h1
    rwa [pullback_id] at h1
  · intro h
    rw [← GrothendieckTopology.mem_sieves_iff_coe]
    simp only [lawvereTierneyToGrothendieck, grothendieckToLawvereTierney,
      Set.mem_setOf_eq]
    ext Y f
    exact ⟨fun _ => trivial, fun _ => J.pullback_stable f h⟩

/-- First round trip, as an equality of topologies — starting from `J`,
    passing to Lawvere–Tierney and back, gives `J` back identically. -/
theorem lawvereTierneyToGrothendieck_comp_grothendieckToLawvereTierney
    (J : GrothendieckTopology C) :
    lawvereTierneyToGrothendieck (grothendieckToLawvereTierney J) = J := by
  apply le_antisymm
  · rw [GrothendieckTopology.le_def]
    intro X S hS
    exact (mem_lawvereTierney_toGrothendieck_iff J).1 hS
  · rw [GrothendieckTopology.le_def]
    intro X S hS
    exact (mem_lawvereTierney_toGrothendieck_iff J).2 hS

/-- Second round trip — the closure extracted from the dense sieves of
    `j` gives `j` back at every sieve. An arrow `f` is in the extracted
    closure iff the pullback of `S` along `f` is dense, iff `(j S).pullback f`
    is maximal (naturality), iff finally `f` lives in `j S` (Section 1
    bridge). -/
theorem grothendieckToLawvereTierney_comp_lawvereTierneyToGrothendieck_closure
    (j : LawvereTierney C) :
    (grothendieckToLawvereTierney (lawvereTierneyToGrothendieck j)).closure
      = j.closure := by
  funext X S
  simp only [grothendieckToLawvereTierney]
  ext Y f
  rw [mem_jClosure_iff, ← GrothendieckTopology.mem_sieves_iff_coe]
  simp only [lawvereTierneyToGrothendieck, Set.mem_setOf_eq]
  rw [j.maps_pullback, ← mem_iff_pullback_eq_top]

/-!
## Section 5: Dictionary summary

The "site" view of SGA 4 — a Grothendieck topology, three axioms on
covering sieves — and the "elementary topos" view of Lawvere–Tierney — a
closure operator on the classifier Ω — describe **the same data**:

  J ↦ jClosure J          (J → j direction, Section 2)
  j ↦ {S | j S = ⊤}        (j → J direction, Section 3)
  round trips              (Section 4: bijection)

Parts 58 (Ω), 59 (j) and 60 (the dictionary) thus close the elementary
half of the theory: the presheaf of sieves of a site is an elementary topos
whose Lawvere–Tierney topologies are exactly the topologies of the site.
-/

end Grothendieck.TopologyDictionary_en
