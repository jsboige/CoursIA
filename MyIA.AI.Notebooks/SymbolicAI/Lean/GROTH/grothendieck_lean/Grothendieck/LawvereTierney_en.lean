/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A Tribute to Grothendieck — Part 59: The Lawvere–Tierney topology — the closure operator on Ω

Alexandre Grothendieck (1928-2014).

Extension of #2159 (EPIC #1646).

Parts 1-44 established the foundations: categories, sieves, topologies,
lattice laws (`SieveLattice`), sheaves, sheafification. Parts 45-57
systematized the arrow form of the covering. Part 58 crossed a threshold by
exhibiting the **subobject classifier** Ω = `Functor.sieves`, the presheaf of
sieves.

This part sets the other half of the elementary-topos structure: the
**Lawvere–Tierney topology**. A Lawvere–Tierney topology is a closure operator
`j` on Ω — at each object `X`, a map `Sieve X → Sieve X` — satisfying three
laws:

  - **extensivity**: `S ≤ j S` (every sieve is contained in its closure);
  - **idempotence**: `j (j S) = j S` (the closure of a closure is closed);
  - **meet preservation**: `j (S ⊓ T) = j S ⊓ j T` (closure commutes with
    finite intersection).

together with a **naturality** with respect to pullback: `j (S.pullback f) =
(j S).pullback f`. Naturality is what makes `j` a **global** operator on the
presheaf Ω rather than a disconnected family of local operators.

This is also the closure operator that Part 6 walked through for sieves under
another name: `pullback_imap`, `pullback_iinf` are pieces of the lattice
structure of Ω; Part 59 shows that the Lawvere–Tierney closure is the dual
gesture that, on this lattice, cuts out the **closed** sieves.

Two canonical topologies realize it, at the two ends of the spectrum:

  - **discrete** (`j S = S`): the closure is the identity, every sieve is closed;
  - **indiscrete** (`j S = ⊤`): the closure is maximal, only `⊤` is closed.

Both satisfy the three laws — the first trivially, the second through the laws
of `Sieve` (`pullback_top`, `le_top`, `inf_idem`). The **honest frontier** of
this part: the correspondence "Grothendieck topology ↔ Lawvere–Tierney
topology" (the `j` induced by the `J`-closure operator) requires a
`GrothendieckTopology.closure` operator absent from Mathlib v4.32.1; it remains
out of reach of this part, as the `ElementaryTopos` instance was for Part 58.

All `sorry`s eliminated at creation.

### Accessibility note (Epics #1452/#1453)

This module exposes **6 `#check` verifications**, **1 structure**, **2 canonical
topologies** and **4 own theorems**: (1) the `LawvereTierney` structure;
(2) the discrete topology; (3) the indiscrete topology; (4) the top law,
monotonicity and closedness of the closure; (5) the closed sieves of the
indiscrete topology.

### i18n convention (EPIC #4980 ratified by user 2026-07-04)

This module is paired with its canonical French version in the sibling file
`LawvereTierney.lean` (sibling pair model). Namespace suffixed `_en`
(anti-collision). The `#check`s, signatures, variables and universes are
byte-identical between the two files; only docstrings and comments differ.
-/

import Mathlib.CategoryTheory.Topos.Sheaf

universe u v

namespace Grothendieck.LawvereTierney_en

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-!
## Section 1: The structure

A **Lawvere–Tierney topology** on Ω is a closure operator
`closure : ∀ X, Sieve X → Sieve X` natural in `X` (compatible with pullback)
and satisfying the three laws: extensivity, idempotence, meet preservation.
The Mathlib material needed: the complete lattice of sieves (`CompleteLattice
(Sieve X)`, hence `≤`, `⊓`, `⊤`, `le_inf`, `le_top`), the pullback
`Sieve.pullback` and its laws (`pullback_top`, `pullback_inter`,
`pullback_id`, `pullback_comp`).
-/

-- CALIBRATION: the lattice of sieves and its pullback.
#check @Sieve.ext               -- extensionality: R = S iff ∀ Y f, R f ↔ S f
#check @Sieve.top_apply         -- (⊤ : Sieve X) f : the maximal sieve contains f
#check @Sieve.pullback          -- pullback of a sieve along a morphism
#check @Sieve.pullback_top      -- (⊤ : Sieve X).pullback f = ⊤
#check @Sieve.pullback_inter    -- (S ⊓ R).pullback f = S.pullback f ⊓ R.pullback f
#check @Sieve.pullback_id       -- S.pullback (𝟙 _) = S

/-- A **Lawvere–Tierney topology** on the category of presheaves of `C`.

    It is given by a closure operator `closure` on sieves, natural in `X`
    (compatible with pullback), extensive (`S ≤ closure S`), idempotent
    (`closure (closure S) = closure S`) and meet-preserving
    (`closure (S ⊓ T) = closure S ⊓ closure T`). This is exactly the closure
    operator whose fixed points are the **closed** sieves — the dual structure
    of the subobject that Part 58 classified. -/
structure LawvereTierney (C : Type u) [Category.{v} C] where
  /-- The closure operator: an endomorphism of `Sieve X` at each object `X`. -/
  closure : ∀ X : C, Sieve X → Sieve X
  /-- Naturality: the closure commutes with pullback — `j` is a global operator
      on Ω, not a disconnected local family. -/
  maps_pullback : ∀ ⦃X Y : C⦄ (f : Y ⟶ X) (S : Sieve X),
    closure Y (S.pullback f) = (closure X S).pullback f
  /-- Extensivity: every sieve is contained in its closure. -/
  extensive : ∀ X (S : Sieve X), S ≤ closure X S
  /-- Idempotence: the closure of a sieve is closed. -/
  idempotent : ∀ X (S : Sieve X), closure X (closure X S) = closure X S
  /-- Meet preservation: the closure commutes with finite intersection. -/
  preserve_meet : ∀ X (S T : Sieve X), closure X (S ⊓ T) = closure X S ⊓ closure X T

/-- A sieve `S` is **closed** for the topology `j` if it is a fixed point of the
    closure: `closure S = S`. The closed sieves are precisely those stable under
    `j` — the subobject that Part 58 calls closed. -/
def IsClosed (j : LawvereTierney C) {X : C} (S : Sieve X) : Prop :=
  j.closure X S = S

/-!
## Section 2: The discrete topology

The identity closure `j S = S` is a Lawvere–Tierney topology: the **discrete
topology**. Every sieve is closed — the closure separates nothing. The three
laws are trivial (`S ≤ S`, `S = S`, `S ⊓ T = S ⊓ T`).
-/

/-- The **discrete** topology: `j S = S`. The closure is the identity; every
    sieve is closed. Extensivity by `le_refl`, idempotence and meet preservation
    by reflexivity. -/
def lawvereTierneyDiscrete : LawvereTierney C where
  closure := fun X S => S
  maps_pullback := by
    intro X Y f S
    rfl
  extensive := by
    intro X S
    exact le_refl S
  idempotent := by
    intro X S
    rfl
  preserve_meet := by
    intro X S T
    rfl

/-!
## Section 3: The indiscrete topology

The constant closure `j S = ⊤` is a Lawvere–Tierney topology: the **indiscrete
topology** (coarse). Only the maximal sieve `⊤` is closed; every other sieve is
forced into `⊤`. The laws hold by the laws of `Sieve`: pullback of the top
(`pullback_top`), top bound (`le_top`), idempotence and `inf_idem` for the meet.
-/

/-- The **indiscrete** topology: `j S = ⊤`. The closure is constant maximal;
    only the maximal sieve is closed. Extensivity by `le_top`, naturality by
    `Sieve.pullback_top`, meet by `inf_idem`. -/
def lawvereTierneyIndiscrete : LawvereTierney C where
  closure := fun X S => ⊤
  maps_pullback := by
    intro X Y f S
    simp
  extensive := by
    intro X S
    exact le_top
  idempotent := by
    intro X S
    rfl
  preserve_meet := by
    intro X S T
    simp

/-!
## Section 4: The proper laws of a Lawvere–Tierney topology

The theorems that make `closure` a closure operator worthy of the name: the
closure of the maximal sieve is maximal, the closure is **monotone** (preserves
order — derived from meet preservation), and the closure of any sieve is
**closed**.
-/

/-- THE TOP LAW: the closure of the maximal sieve is the maximal sieve.
    Derived from extensivity (`⊤ ≤ j ⊤`) and the fact that `j ⊤ ≤ ⊤` since
    `⊤` is the top element. -/
theorem j_top (j : LawvereTierney C) (X : C) :
    j.closure X (⊤ : Sieve X) = ⊤ :=
  le_antisymm le_top (j.extensive X (⊤ : Sieve X))

/-- PROPER: the closure is **monotone** — `S ≤ T` implies `j S ≤ j T`.
    The proof is a consequence of meet preservation: `S ≤ T` gives
    `S ⊓ T = S`, hence `j S = j (S ⊓ T) = j S ⊓ j T`, and the intersection is
    bounded above by each factor. This is what makes `closure` a closure
    operator (a closure preserves order), not a mere involution. -/
theorem j_monotone (j : LawvereTierney C) {X : C} {S T : Sieve X} (h : S ≤ T) :
    j.closure X S ≤ j.closure X T := by
  have h_eq_inf : S ⊓ T = S := le_antisymm inf_le_left (le_inf le_rfl h)
  have h_meet : j.closure X (S ⊓ T) = j.closure X S ⊓ j.closure X T :=
    j.preserve_meet X S T
  rw [h_eq_inf] at h_meet
  calc
    j.closure X S = j.closure X S ⊓ j.closure X T := h_meet
    _ ≤ j.closure X T := inf_le_right

/-- PROPER: the closure of any sieve is **closed** — this is idempotence, read
    as a property of `IsClosed`. The closure of a closure no longer moves: the
    closures are exactly the fixed points. -/
theorem closure_isClosed (j : LawvereTierney C) {X : C} (S : Sieve X) :
    IsClosed j (j.closure X S) := j.idempotent X S

/-!
## Section 5: The closed sieves of the indiscrete topology

For the discrete topology, `IsClosed` is trivially true for every sieve.
For the indiscrete topology, the characterization is informative: a sieve is
closed exactly when it is the maximal sieve — the closure leaves a single fixed
point, the top of the lattice.
-/

/-- PROPER: for the indiscrete topology, a sieve is closed iff it is the maximal
    sieve `⊤`. The constant-top closure has a single fixed point. -/
theorem indiscrete_closed_iff_top {X : C} (S : Sieve X) :
    IsClosed lawvereTierneyIndiscrete S ↔ S = ⊤ :=
  Iff.intro (fun h => h.symm) (fun h => h.symm)

/-!
## Section 6: Summary of the structure

Part 58 exhibited the subobject classifier `Ω`; this part installs the closure
operator that cuts it. The `LawvereTierney` structure is what `Ω` was missing
to be an elementary topos: classifier (58) + Lawvere–Tierney closures (59). The
two canonical realizations (discrete and indiscrete) are the ends of the
spectrum; monotonicity links the closure to the order of the lattice of sieves.
-/

end Grothendieck.LawvereTierney_en
