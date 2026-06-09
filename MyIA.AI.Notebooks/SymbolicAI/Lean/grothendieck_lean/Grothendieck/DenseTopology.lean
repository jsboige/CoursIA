/-
Grothendieck tribute — Part 12: The dense topology
Alexandre Grothendieck (1928-2014).

Phase 7 extension (#2159, Epic #1646).

Part 11 (SieveGenerate.lean) recorded the identities of `Sieve.generate`.
This module studies the **dense topology** (a.k.a. `¬∀`-topology, or the
"double-negation" topology), one of the standard examples of a Grothendieck
topology that is neither trivial nor discrete.

A sieve S on X is dense-covering when every arrow `f : Y ⟶ X` into X can be
*refined* by an arrow landing in S: there exist `Z` and `g : Z ⟶ Y` with
`S (g ≫ f)`. Equivalently, S is "eventually covering" along any incoming
arrow — the order-theoretic shadow of a double-negation sheaf.

We record the basic identities:

  - The maximal sieve is dense-covering at every object.
  - The dense topology lies between the trivial and discrete topologies.
  - The explicit membership characterization (`dense_covering`).
  - Pullback stability: dense-covering is stable under base change.

A naming subtlety worth flagging for learners: in Mathlib, `C` is an
*explicit* parameter of `GrothendieckTopology.trivial` and `.discrete` but
an *implicit* one of `.dense` (they live in different `variable` blocks of
the Mathlib source). Hence we write `trivial C` and `discrete C` but bare
`dense` (letting Lean infer `C`); writing `dense C` would instead apply the
topology to `C` as an object via the `DFunLike` coercion.

Epic #1646, Phase 7 (#2159). All `sorry`s eliminated at creation.
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck

open CategoryTheory

/-!
## The maximal sieve is dense-covering

Every arrow `f : Y ⟶ X` is refined by itself via the identity: `g := 𝟙 Y`
gives `⊤ (𝟙 Y ≫ f)`. So the maximal sieve covers for the dense topology at
every object — this is the identity axiom of a Grothendieck topology,
specialized to the dense topology.
-/

/-- The maximal sieve is dense-covering at every object.
    Unfolds `dense_covering` and witnesses the refinement via `𝟙`. -/
theorem dense_top_mem {C : Type*} [Category C] (X : C) :
    (⊤ : Sieve X) ∈ GrothendieckTopology.dense X := by
  rw [GrothendieckTopology.dense_covering]
  intro Y _f
  exact ⟨Y, 𝟙 Y, trivial⟩

/-!
## The dense topology lies between trivial and discrete

The trivial (coarsest) topology is below the dense topology, and the dense
topology is below the discrete (finest) topology. These follow directly from
the complete lattice structure on `GrothendieckTopology C`.

Note that `dense` carries `C` implicitly (unlike `trivial`/`discrete`), so
it is written without an explicit argument here — Lean infers it from the
expected type.
-/

/-- The trivial topology is below the dense topology. -/
theorem trivial_le_dense {C : Type*} [Category C] :
    (GrothendieckTopology.trivial C : GrothendieckTopology C) ≤
      GrothendieckTopology.dense := by
  rw [GrothendieckTopology.trivial_eq_bot]
  exact bot_le

/-- The dense topology is below the discrete topology. -/
theorem dense_le_discrete {C : Type*} [Category C] :
    (GrothendieckTopology.dense : GrothendieckTopology C) ≤
      GrothendieckTopology.discrete C := by
  rw [GrothendieckTopology.discrete_eq_top]
  exact le_top

/-- Every dense topology lies between trivial and discrete:
    ⊥ ≤ dense ≤ ⊤. -/
theorem trivial_le_dense_le_discrete {C : Type*} [Category C] :
    (GrothendieckTopology.trivial C : GrothendieckTopology C) ≤
      GrothendieckTopology.dense ∧
    (GrothendieckTopology.dense : GrothendieckTopology C) ≤
      GrothendieckTopology.discrete C :=
  ⟨trivial_le_dense, dense_le_discrete⟩

/-!
## Explicit membership characterization

A sieve `S` is dense-covering exactly when every incoming arrow can be
refined into `S`. This is the definitional `dense_covering` iff,
repackaged as forward and backward directions for readability.
-/

/-- If every incoming arrow `f : Y ⟶ X` can be refined into `S`, then `S`
    is dense-covering. Forward direction is definitional (`Iff.rfl`). -/
theorem mem_dense_of_refines {C : Type*} [Category C] {X : C} {S : Sieve X}
    (h : ∀ {Y : C} (f : Y ⟶ X), ∃ (Z : _) (g : Z ⟶ Y), S.arrows (g ≫ f)) :
    S ∈ GrothendieckTopology.dense X := by
  rw [GrothendieckTopology.dense_covering]
  exact h

/-- A dense-covering sieve refines every incoming arrow `f : Y ⟶ X`.
    Backward direction of `dense_covering`, made into a usable lemma. -/
theorem dense_refines_of_mem {C : Type*} [Category C] {X : C} {S : Sieve X}
    (hS : S ∈ GrothendieckTopology.dense X) {Y : C} (f : Y ⟶ X) :
    ∃ (Z : _) (g : Z ⟶ Y), S.arrows (g ≫ f) :=
  GrothendieckTopology.dense_covering.mp hS f

/-!
## Pullback stability

Dense-covering is stable under pullback: if `S` is dense-covering on `X` and
`f : Y ⟶ X`, then `Sieve.pullback f S` is dense-covering on `Y`. This is the
stability axiom of the Grothendieck topology, specialized to `dense`.
-/

/-- The pullback of a dense-covering sieve is dense-covering.
    This is `GrothendieckTopology.pullback_stable` applied to the dense
    topology. Note `dense` is written without an explicit `C` argument. -/
theorem dense_pullback_stable {C : Type*} [Category C] {X Y : C}
    {S : Sieve X} (hS : S ∈ GrothendieckTopology.dense X) (f : Y ⟶ X) :
    Sieve.pullback f S ∈ GrothendieckTopology.dense Y :=
  GrothendieckTopology.dense.pullback_stable f hS

end Grothendieck
