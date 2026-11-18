/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Part 36 : the bundled covering

Alexandre Grothendieck (1928-2014).

Phase 5 extension (#2159, EPIC #1646).

Parts 1-29 laid the foundations : categories, sieves, topologies, lattice
laws, pullback identities, sheaf bases, covering closure, calibration,
subcanonicity, dense topologies, sheaves, internal hom, Cech cohomology,
Mayer-Vietoris limits, Kan extensions, adjunctions, monads, equivalences,
monoidal categories, limits and colimits, comma pairs, direct images. Part 35
recorded proper theorems on the arrow form of the covering (`J.Covers S f`).

This module records **proper theorems** on the **bundled covering** : for a
Grothendieck topology `J` on a category `C` and an object `X`, the type
`J.Cover X` gathers the covering sieves of `X` :
`J.Cover X = { S : Sieve X // S ∈ J X }` (a subtype with coercible
coefficient `↑S : Sieve X` and membership `S f` via `CoeFun`). The bundled
covering carries the order, the lattice, the pullback laws, the `Arrow`
structure (the arrows of `S`) and the refinement operation `bind` — the whole
structure coming from the pullback stability axiom.

The theorems stated here are **genuine tactical proofs** (DEEP vein, unlike
the re-export bridges of the previous parts) :

  - `cover_iff_coe_mem` : a sieve `S` is covering iff it is the coefficient
    of a covering (the subtype reconstructs the family).
  - `coe_injective` : the coefficient is injective (the subtype is faithful).
  - `top_coe`, `top_apply` : the largest element is the universal sieve.
  - `inf_apply` : the infimum of two coverings is their intersection.
  - `pullback_top`, `pullback_inf` : pullback commutes with top and inf.
  - `pullback_monotone` : pullback is monotone.
  - `pullbackId_apply`, `pullbackComp_apply` : identity and composition laws
    of the pullback (coincide with `pullbackId`/`pullbackComp`).
  - `precomp_condition`, `base_condition` : the membership conditions of
    precomposed and lifted arrows.
  - `precompRelation_spec` : the precomposition relation is a refinement
    (equality in the square).
  - `bind_mem_iff` : the exact membership of `S.bind T`.
  - `bindToBase_le` : the refinement sits above the base (the bind is finer
    than the starting covering).

Each proof mobilises a distinct Mathlib lemma (`Sieve.ext`, `Subtype.ext`,
`Sieve.top_apply`, `Sieve.inter_apply`, `Sieve.pullback_monotone`,
`Category.id_comp`, `Category.assoc`, `Sieve.downward_closed`) and the
definitional laws of the `J.Cover` structure — no proof is a plain re-export.

EPIC #1646, Phase 5 (#2159). All `sorry`s eliminated at creation.

### i18n convention (EPIC #4980 ratified by user 2026-07-04)

This module is paired with its French twin in the sibling file
`Cover.lean` (sibling-pair model, see PR #6154 for the pilot on
`Utility.lean`). The `_en` namespace suffix is applied to this EN file
(collision avoidance, per code-style.md #4980). Theorem statements, lemma
names, Lean tactics and Mathlib references remain in English ; only the
docstrings `/-- ... -/` and comments `-- ...` differ between the two files
(byte-identity preservation).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck.Cover_en

open CategoryTheory

/-!
## Section 1 : extensionality and constants

Recall : `J.Cover X` is definitionally `{ S : Sieve X // S ∈ J X }`, the
coefficient is the projection `(T : Sieve X)` and the membership `T f` is
that of the coefficient. The first theorem characterises the membership
`S ∈ J X` by the existence of a covering with coefficient `S` ; the second
expresses the faithfulness of the subtype.
-/

/-- A sieve `S` is covering iff there exists a covering with coefficient
    `S` : `S ∈ J X ↔ ∃ T : J.Cover X, (T : Sieve X) = S`.
    Proof : the forward direction builds the subtype `⟨S, h⟩` (the
    membership is the hypothesis) and concludes by reflexivity ; the reverse
    direction rewrites the membership of `S` into that of `T` (`rw [← hT]`)
    and invokes `T.condition`, the subtype property. -/
theorem cover_iff_coe_mem {C : Type*} [Category C] {X : C}
    (J : GrothendieckTopology C) (S : Sieve X) :
    S ∈ J X ↔ ∃ T : J.Cover X, (T : Sieve X) = S := by
  constructor
  · intro h
    exact ⟨⟨S, h⟩, rfl⟩
  · rintro ⟨T, hT⟩
    rw [← hT]
    exact T.condition

/-- The coefficient is injective : `Function.Injective (fun T : J.Cover X =>
    (T : Sieve X))`.
    Proof : we split the two subtypes `⟨S, _hS⟩` and `⟨T, _hT⟩` ; the
    equality of the coefficients provides `S = T` (beta-reduction of the
    lambda), which `Subtype.ext` lifts to an equality of the subtypes. -/
theorem coe_injective {C : Type*} [Category C] {X : C}
    (J : GrothendieckTopology C) :
    Function.Injective (fun T : J.Cover X => (T : Sieve X)) := by
  rintro ⟨S, _hS⟩ ⟨T, _hT⟩ h
  change S = T at h
  exact Subtype.ext h

/-- The coefficient of the largest element is the universal sieve :
    `((⊤ : J.Cover X) : Sieve X) = ⊤`.
    Proof : definitional — the `OrderTop` of `J.Cover X` is the subtype
    `⟨⊤, J.top_mem _⟩` and the coefficient is the projection. -/
theorem top_coe {C : Type*} [Category C] {X : C}
    (J : GrothendieckTopology C) : ((⊤ : J.Cover X) : Sieve X) = ⊤ := rfl

/-- The largest element is covering for every arrow :
    `(⊤ : J.Cover X) f`.
    Proof : we pass to the coefficient, rewrite by `top_coe` and invoke
    `Sieve.top_apply`, the membership of the universal sieve (which is not
    a `simp` rule : the call is explicit). -/
theorem top_apply {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (f : Y ⟶ X) : (⊤ : J.Cover X) f := by
  rw [top_coe]
  exact Sieve.top_apply f

/-- The membership of the infimum is the conjunction of the memberships :
    `(S ⊓ T) f ↔ S f ∧ T f`.
    Proof : the infimum of the subtype is the subtype of the intersection of
    the coefficients (`SemilatticeInf.inf = fun S T => ⟨↑S ⊓ ↑T, _⟩`), so we
    pass to the coefficients and invoke `Sieve.inter_apply` (a `simp`
    rule). -/
theorem inf_apply {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (S T : J.Cover X) (f : Y ⟶ X) :
    (S ⊓ T) f ↔ S f ∧ T f := by
  change ((S : Sieve X) ⊓ (T : Sieve X)) f ↔ (S : Sieve X) f ∧ (T : Sieve X) f
  rw [Sieve.inter_apply]

/-!
## Section 2 : pullback identities

The five following theorems concern `pullback (S : J.Cover X) (f : Y ⟶ X)`,
the covering `S.pullback f` on `Y`, whose membership is given by the
`simp` rule `GrothendieckTopology.Cover.coe_pullback : (S.pullback f) g ↔ S (g ≫ f)`.
-/

/-- The pullback of the largest element is the largest element :
    `(⊤ : J.Cover X).pullback f = ⊤`.
    Proof : we reason by extensionality (`Cover.ext`), rewrite by
    `GrothendieckTopology.Cover.coe_pullback` then by `top_coe` on both sides, and conclude by
    `Sieve.top_apply` in each direction. -/
theorem pullback_top {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (f : Y ⟶ X) :
    (⊤ : J.Cover X).pullback f = ⊤ := by
  apply GrothendieckTopology.Cover.ext
  intro Z g
  rw [GrothendieckTopology.Cover.coe_pullback, top_coe, top_coe]
  exact ⟨fun _ => Sieve.top_apply g, fun _ => Sieve.top_apply (g ≫ f)⟩

/-- Pullback commutes with the infimum :
    `(S ⊓ T).pullback f = S.pullback f ⊓ T.pullback f`.
    Proof : extensionality then rewriting by `GrothendieckTopology.Cover.coe_pullback` and `inf_apply`
    on each side (the `rw` reduces the three members to the same
    conjunction). -/
theorem pullback_inf {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (S T : J.Cover X) (f : Y ⟶ X) :
    (S ⊓ T).pullback f = S.pullback f ⊓ T.pullback f := by
  apply GrothendieckTopology.Cover.ext
  intro Z g
  rw [GrothendieckTopology.Cover.coe_pullback, inf_apply, inf_apply, GrothendieckTopology.Cover.coe_pullback, GrothendieckTopology.Cover.coe_pullback]

/-- Pullback is monotone : if `S ≤ T` then `S.pullback f ≤ T.pullback f`.
    Proof : the orders are pointwise ; we bring the hypothesis back to the
    coefficients, transform the members of the conclusion into sieve
    pullbacks, and invoke `Sieve.pullback_monotone`. -/
theorem pullback_monotone {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) {S T : J.Cover X} (f : Y ⟶ X) (h : S ≤ T) :
    S.pullback f ≤ T.pullback f := by
  change (S : Sieve X) ≤ (T : Sieve X) at h
  change (S : Sieve X).pullback f ≤ (T : Sieve X).pullback f
  exact Sieve.pullback_monotone f h

/-- The pullback along the identity is the identity :
    `S.pullback (𝟙 X) = S`.
    Proof : extensionality then rewriting by `GrothendieckTopology.Cover.coe_pullback` ; the membership
    becomes `S (g ≫ 𝟙 X)` and `simp` reduces `g ≫ 𝟙 X` to `g`
    (`Category.comp_id`). -/
theorem pullbackId_apply {C : Type*} [Category C] {X : C}
    (J : GrothendieckTopology C) (S : J.Cover X) :
    S.pullback (𝟙 X) = S := by
  apply GrothendieckTopology.Cover.ext
  intro Y g
  rw [GrothendieckTopology.Cover.coe_pullback]
  simp

/-- The pullback along a composition is the composition of the pullbacks :
    `S.pullback (f ≫ g) = (S.pullback g).pullback f`.
    Proof : extensionality, three rewrites by `GrothendieckTopology.Cover.coe_pullback` then
    `Category.assoc` (reverse orientation) bring the left membership to the
    right one. -/
theorem pullbackComp_apply {C : Type*} [Category C] {X Y Z : C}
    (J : GrothendieckTopology C) (S : J.Cover X) (f : Z ⟶ Y) (g : Y ⟶ X) :
    S.pullback (f ≫ g) = (S.pullback g).pullback f := by
  apply GrothendieckTopology.Cover.ext
  intro W h
  rw [GrothendieckTopology.Cover.coe_pullback, GrothendieckTopology.Cover.coe_pullback, GrothendieckTopology.Cover.coe_pullback, ← Category.assoc]

/-!
## Section 3 : arrows of the covering

Recall : `S.Arrow` is the structure of arrows `I : I.Y ⟶ X` whose membership
`S I.f` is the condition `I.hf`. The precomposition `I.precomp g` answers the
stability under precomposition : `(I.precomp g).f = g ≫ I.f` (simps of
`precomp`).
-/

/-- The precomposed arrow is still an arrow of the covering :
    `S (g ≫ I.f)`.
    Proof : definitional — `(I.precomp g).f` is `g ≫ I.f` (the body of
    `precomp`), so `(I.precomp g).hf` has exactly the sought type. -/
theorem precomp_condition {C : Type*} [Category C] {X Z : C}
    (J : GrothendieckTopology C) {S : J.Cover X} (I : S.Arrow)
    (g : Z ⟶ I.Y) : S (g ≫ I.f) :=
  (I.precomp g).hf

/-- The arrow lifted along `f` is an arrow of the starting covering :
    `S (I.f ≫ f)`.
    Proof : definitional — `I.base` is `⟨I.Y, I.f ≫ f, I.hf⟩`, so
    `I.base.hf` has exactly the sought type (the membership of `S.pullback f`
    is the membership of `S` after composing by `f`). -/
theorem base_condition {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) {S : J.Cover X} (f : Y ⟶ X)
    (I : (S.pullback f).Arrow) : S (I.f ≫ f) :=
  I.base.hf

/-- The precomposition relation is a refinement :
    `𝟙 Z ≫ (I.precomp g).f = g ≫ I.f`.
    Proof : the field `w` of `I.precompRelation g` states
    `g₁ ≫ (I.precomp g).f = g₂ ≫ I.f` with `g₁ = 𝟙 (I.precomp g).Y` and
    `g₂ = g` ; since `(I.precomp g).Y` reduces definitionally to `Z`, `w` has
    exactly the type of the conclusion and `exact` concludes. -/
theorem precompRelation_spec {C : Type*} [Category C] {X Z : C}
    (J : GrothendieckTopology C) {S : J.Cover X} (I : S.Arrow)
    (g : Z ⟶ I.Y) : 𝟙 Z ≫ (I.precomp g).f = g ≫ I.f := by
  exact (I.precompRelation g).w

/-!
## Section 4 : the bind refinement

Recall : `S.bind T` assembles a family of coverings `T I` indexed by the
arrows of `S` into a covering of `X` : `f` belongs to it iff it factors
through an arrow `e2` of `S` (this one covering `e1`).
-/

/-- The membership of `S.bind T` :
    `(S.bind T) f ↔ ∃ (Z) (e1 : Y ⟶ Z) (e2 : Z ⟶ X) (hS : S e2),
     (T ⟨Z, e2, hS⟩) e1 ∧ e1 ≫ e2 = f`.
    Proof : definitional — the left member is the membership of the sieve
    `Sieve.bind S (fun Y f hf => T ⟨Y, f, hf⟩)` whose definition is exactly
    this factorisation (binder by binder, conjunction included). -/
theorem bind_mem_iff {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) {S : J.Cover X} (T : ∀ I : S.Arrow, J.Cover I.Y)
    (f : Y ⟶ X) :
    (S.bind T) f ↔
      ∃ (Z : C) (e1 : Y ⟶ Z) (e2 : Z ⟶ X) (hS : S e2),
        (T ⟨Z, e2, hS⟩) e1 ∧ e1 ≫ e2 = f := by
  rfl

/-- The refinement sits above the base : `S.bind T ≤ S`.
    Proof : the orders are pointwise ; a membership of `S.bind T` factors as
    `e1 ≫ e2 = f` with `S e2`, we rewrite then invoke
    `Sieve.downward_closed` (the argument `h1` then the morphism `e1`), the
    stability under precomposition of the sieve. -/
theorem bindToBase_le {C : Type*} [Category C] {X : C}
    (J : GrothendieckTopology C) {S : J.Cover X} (T : ∀ I : S.Arrow, J.Cover I.Y) :
    S.bind T ≤ S := by
  intro Y f hf
  rcases hf with ⟨Z, e1, e2, h1, _hT, h3⟩
  rw [← h3]
  exact (S : Sieve X).downward_closed h1 e1

end Grothendieck.Cover_en
