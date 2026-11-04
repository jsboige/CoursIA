/-

# Grothendieck tribute — Part 12: The dense topology

Copyright (c) 2026 CoursIA. All rights reserved.
Released under the Apache 2.0 license, see LICENSE file at the repository root.

## The dense topology (EN sibling mirror)

This module is the English-language mirror of `DenseTopology.lean` (FR canonical).
Per the EPIC #4980 convention (ratified by user 2026-07-04), the FR-first file is
the canonical source; this sibling carries the same theorems, signatures, and proof
bodies, with English documentation. Anti-§D byte-identity (L298) holds: every
`theorem` signature, `def`, `import`, `open`, and proof body is BYTE-IDENTICAL to
the FR canonical — only the docstrings and headers differ. The namespace
suffix is `Grothendieck.DenseTopology_en` to avoid collisions.

For the canonical French version, see `DenseTopology.lean`.
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck.DenseTopology_en

open CategoryTheory

/-!
## 1. The maximal sieve is dense-covering

Every arrow `f : Y ⟶ X` is refined by itself via the identity: `g := 𝟙 Y`
gives `⊤ (𝟙 Y ≫ f)`. So the maximal sieve covers for the dense topology at
every object — this is the identity axiom of a Grothendieck topology,
specialized to the dense topology.
-/


/-- The maximal sieve is dense-covering at every object.
    Unfolds `dense_covering` and witnesses the refinement via 𝟙. -/

theorem dense_top_mem {C : Type*} [Category C] (X : C) :
    (⊤ : Sieve X) ∈ GrothendieckTopology.dense X := by
  rw [GrothendieckTopology.dense_covering]
  intro Y _f
  exact ⟨Y, 𝟙 Y, trivial⟩

/-!
## 2. The dense topology lies between trivial and discrete

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
## 3. Explicit membership characterization

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
## 4. Pullback stability

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

/-!
## Proper theorems (c.1301+126)

The theorems below *prove* definitional equalities exposed by the fields
of the structure `GrothendieckTopology C` via the `dense` topology
(a namespace-level `def`). They exploit:
- `GrothendieckTopology.dense.top_mem X`: user-facing lemma (simp+grind
  tagged) on the dense topology, β-equivalent to `dense.top_mem' X`
- `GrothendieckTopology.dense.pullback_stable f hS`: user-facing lemma
  on pullback stability
- `GrothendieckTopology.dense_covering`: `iff` characterizing
  membership `S ∈ GrothendieckTopology.dense X`

All these fields/lemmas operate on the resident structure
`GrothendieckTopology C` non polymorphic over universes — so
**L902 ★★ SAFE** (cf. c.1301+108-L1 ★★ : polymorphic universe
constructors are to be proscribed, unlike resident fields on C).

1. `dense_top_mem_field`: restatement of `dense_top_mem` that uses
   directly the Mathlib lemma `GrothendieckTopology.dense.top_mem X`.
2. `dense_pullback_stable_field`: restatement of `dense_pullback_stable`
   that uses directly the Mathlib lemma
   `GrothendieckTopology.dense.pullback_stable f hS`.
3. `mem_dense_iff_forall_refines`: restatement of the characterization
   `mem_dense_of_refines` (forward) and `dense_refines_of_mem` (backward)
   combined into a `↔` via `GrothendieckTopology.dense_covering.symm`.

These are "showcase" theorems that certify the fields/lemmas of the
`GrothendieckTopology C` structure are effectively computable in the
same Lean execution.
-/

/-- Theorem: the maximal sieve is dense-covering in the sense of the
    `top_mem` field of the `dense` topology. Direct restatement of the
    lemma `GrothendieckTopology.dense.top_mem X` (itself β-equivalent
    to `dense.top_mem' X`, the identity axiom of the resident structure
    `GrothendieckTopology C`). -/
theorem dense_top_mem_field {C : Type*} [Category C] (X : C) :
    (⊤ : Sieve X) ∈ GrothendieckTopology.dense X :=
  GrothendieckTopology.dense.top_mem X

/-- Theorem: pullback stability of the dense-covering sieve, via the
    Mathlib lemma `GrothendieckTopology.dense.pullback_stable`
    (itself β-equivalent to `dense.pullback_stable' f hS`, the
    stability axiom of the resident structure `GrothendieckTopology C`). -/
theorem dense_pullback_stable_field {C : Type*} [Category C] {X Y : C}
    {S : Sieve X} (hS : S ∈ GrothendieckTopology.dense X) (f : Y ⟶ X) :
    Sieve.pullback f S ∈ GrothendieckTopology.dense Y :=
  GrothendieckTopology.dense.pullback_stable f hS

/-- Theorem: explicit membership characterization of a dense-covering
    sieve, as a biconditional equivalence between `S ∈ GrothendieckTopology.dense X`
    and the universal property "every incoming arrow admits a refinement
    in S". This is the statement `GrothendieckTopology.dense_covering.symm`
    (the forward and backward directions are already proven by
    `mem_dense_of_refines` and `dense_refines_of_mem` respectively). -/
theorem mem_dense_iff_forall_refines {C : Type*} [Category C] {X : C}
    {S : Sieve X} :
    (S ∈ GrothendieckTopology.dense X) ↔
      ∀ {Y : C} (f : Y ⟶ X), ∃ (Z : _) (g : Z ⟶ Y), S.arrows (g ≫ f) :=
  GrothendieckTopology.dense_covering.symm

end Grothendieck.DenseTopology_en
