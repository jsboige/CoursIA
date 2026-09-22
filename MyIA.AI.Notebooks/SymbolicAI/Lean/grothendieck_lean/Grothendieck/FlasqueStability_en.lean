/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Grothendieck tribute — Part 80 (EN sibling of `Grothendieck/FlasqueStability.lean`):
stability of flasqueness, isomorphisms and products, the boundary of
acyclicity.

Alexandre Grothendieck (1928-2014).

Phase 2 extension (#2159, Epic #1646).

Part 79 defined flasqueness at the level of sites
(`Grothendieck.Flasque`, `IsFlasqueSieves`): any compatible family on any
sieve admits an amalgamation. This part studies the **stability** of that
notion — the question one asks of any sheaf property as soon as it is
defined: by which functors is it preserved?

What Mathlib formalizes is the topological version
(`Mathlib.Topology.Sheaves.Flasque`): stability of flasqueness under
**direct image** (`pushforward_isFlasque`). What this part adds, for the
site version of Part 79:

  - `isFlasqueSieves_of_iso`: flasqueness is a property **invariant under
    isomorphism** of a presheaf. Godement counts it as obvious (II.3.1);
    recording it makes it consumable by later parts without
    re-proving. The proof transports family and amalgamation along the
    iso, compatibility following from naturality.

  - `isFlasqueSieves_pi`: any **product** of flasque presheaves is flasque
    (Godement II.3.2, first half: products and direct sums of flasque
    sheaves are flasque; direct sums live on the side of abelian sheaves).
    A compatible family on a product projects to compatible families
    component by component, each amalgamates, and the global amalgamation
    is the vector of the amalgamations. The technical point is the
    transport through `piObjIso`
    (`Mathlib.CategoryTheory.Limits.FunctorCategory`): evaluating a
    product of functors is taking the product of the evaluations.

  - `subsingleton_H_succ_of_flasque_of_injective`: the **crossing** with
    the cohomology of Part 20 (`Grothendieck.SheafCohomology.Basic`): a
    flasque **and** injective abelian sheaf is acyclic —
    `Subsingleton (H F (n+1))`. This theorem delivers its content in the
    statement, not the proof (`inferInstance`, the cancellation being a
    Mathlib instance already bridged in Part 20): it lays the stone where
    Godement uses Zorn. The full Godement theorem (II.5.2-5.3) is
    *flasque => injective => Γ-acyclic*; here, **the only missing link is
    `flasque => injective`** (II.5.2, proof by inductive extension via
    Zorn's lemma), explicitly documented as a boundary of the lake: the
    chain provable without Zorn is recorded, the Zorn link is left open.

The conceptual reading: the stabilities recorded here are the ones that
cost **no choice** — an isomorphism transports a structure canonically, a
product amalgamates component by component because compatibility and
amalgamation are read component by component. The boundary is exactly
where a choice (Zorn's maximal extension) becomes necessary: *flasque =>
injective* is not canonical. This dividing line — what can be done
without choice, what requires choice — is a thoroughly Grothendieckian
line.

References:
  - R. Godement, *Topologie algebrique et theorie des faisceaux* [God58],
    Chap. II §3 (prop. 2: stability under products) and §5 (acyclicity of
    flasque sheaves, theorem 5.2: flasque => injective via Zorn).
  - SGA 4, Expose II (sites and sieves).
  - Mathlib, `Mathlib.CategoryTheory.Limits.FunctorCategory` (`piObjIso`).
  - Part 20 (`Grothendieck.SheafCohomology.Basic`): Ext cohomology.
  - Part 79 (`Grothendieck.Flasque`): `IsFlasqueSieves`.
  - Part 63 (`Grothendieck.SheafCondition`): the product-equalizer
    decomposition of which flasqueness is the existence half.

i18n convention (EPIC #4980 ratified 2026-07-04): this module is the
English canonical twin of `Grothendieck/FlasqueStability.lean` — `_en`
suffix on the namespace (`Grothendieck.FlasqueStability_en`), translated
docstrings and comments. Theorem statements, Lean tactics, lemma names
and Mathlib references remain in English (Mathlib 4, standard tactic
DSL). Only the `/-- ... -/` docstrings and `-- ...` comments differ
between the two files. Anti-§D byte-identity guaranteed: the namespace
body is preserved bit-for-bit (statements and proofs byte-identical
between `FlasqueStability.lean` and `FlasqueStability_en.lean`).

Epic #1646, Phase 2 (#2159). All `sorry`s eliminated at creation.
-/

import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Grothendieck.Flasque
import Grothendieck.SheafCohomology.Basic

namespace Grothendieck.FlasqueStability_en

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

section Site

variable {C : Type u} [Category.{v} C]

/-- **Invariance under isomorphism**: if `P ≅ Q` and `P` is flasque,
`Q` is too. The `Q`-family transports to a `P`-family via `e.inv`,
compatibility follows from naturality, and the amalgamation `t` comes
back through `e.hom`. Godement counts this as obvious (II.3.1);
recording it spares each downstream part from re-proving the
transport. -/
theorem isFlasqueSieves_of_iso {P Q : Cᵒᵖ ⥤ Type (max v u)} (e : P ≅ Q)
    [IsFlasqueSieves P] : IsFlasqueSieves Q where
  amalgamates := by
    intro X S x hx
    obtain ⟨t, ht⟩ := IsFlasqueSieves.amalgamates (P := P) S
      (fun Y f hf => e.inv.app (op Y) (x f hf))
      (fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ h => by
        show P.map g₁.op (e.inv.app (op Y₁) (x f₁ hf₁))
          = P.map g₂.op (e.inv.app (op Y₂) (x f₂ hf₂))
        rw [← NatTrans.naturality_apply (φ := e.inv) g₁.op (x f₁ hf₁),
          ← NatTrans.naturality_apply (φ := e.inv) g₂.op (x f₂ hf₂),
          hx g₁ g₂ hf₁ hf₂ h])
    refine ⟨e.hom.app (op X) t, ?_⟩
    intro Y f hf
    have nat : (Q.map f.op) (e.hom.app (op X) t)
        = e.hom.app (op Y) ((P.map f.op) t) :=
      (NatTrans.naturality_apply (φ := e.hom) f.op t).symm
    rw [nat, ht f hf]
    simp

end Site

section Produit

variable {C : Type u} [Category.{v} C]

/-- **Stability under product** (Godement II.3.2, first half): any
indexed product of flasque presheaves is flasque. A compatible family
projects component by component via `piObjIso`, each component
amalgamates by flasqueness, and the vector of the amalgamations
amalgamates the original family. This is a stability the topological
version of Mathlib does not record: it only lives on the side of
sites. -/
theorem isFlasqueSieves_pi {ι : Type (max v u)} (P : ι → (Cᵒᵖ ⥤ Type (max v u)))
    [∀ i, IsFlasqueSieves (P i)] : IsFlasqueSieves (∏ᶜ P) where
  amalgamates := by
    intro X S x hx
    -- Projecting then evaluating is evaluating the natural component (in any z).
    have proj : ∀ (i : ι) (Y : C) (z : (∏ᶜ P).obj (op Y)),
        (Pi.π (fun s => (P s).obj (op Y)) i) ((piObjIso P (op Y)).hom z)
          = (Pi.π P i).app (op Y) z := by
      intro i Y z
      have h := piObjIso_hom_comp_π P (op Y) i
      exact ConcreteCategory.congr_hom h z
    -- The component family is compatible: naturality of the projections.
    have hcomp : ∀ i,
        Presieve.FamilyOfElements.Compatible
          (fun Y f hf => (Pi.π P i).app (op Y) (x f hf)) := by
      intro i Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ h
      show (P i).map g₁.op ((Pi.π P i).app (op Y₁) (x f₁ hf₁))
          = (P i).map g₂.op ((Pi.π P i).app (op Y₂) (x f₂ hf₂))
      rw [← NatTrans.naturality_apply (φ := Pi.π P i) g₁.op (x f₁ hf₁),
        ← NatTrans.naturality_apply (φ := Pi.π P i) g₂.op (x f₂ hf₂),
        hx g₁ g₂ hf₁ hf₂ h]
    choose t ht using fun i =>
      IsFlasqueSieves.amalgamates (P := P i) S
        (fun Y f hf => (Pi.π P i).app (op Y) (x f hf)) (hcomp i)
    -- The global amalgamation: the family t lifted to the product of evaluations.
    let w : ∏ᶜ (fun s => (P s).obj (op X)) :=
      (Pi.lift (fun i => TypeCat.ofHom (fun _ : PUnit.{max v u + 1} => t i))) PUnit.unit
    refine ⟨(piObjIso P (op X)).inv w, ?_⟩
    intro Y f hf
    -- The i-th component of the candidate is exactly t i.
    have hπ : ∀ i : ι, (Pi.π P i).app (op X) ((piObjIso P (op X)).inv w) = t i := by
      intro i
      have h := piObjIso_inv_comp_π P (op X) i
      have h2 : (Pi.π P i).app (op X) ((piObjIso P (op X)).inv w)
          = (Pi.π (fun s => (P s).obj (op X)) i) w :=
        ConcreteCategory.congr_hom h w
      rw [h2]
      simp [w, TypeCat.ofHom_apply]
    -- Component-by-component equality after the piObjIso transport.
    have comp : ∀ i : ι,
        (Pi.π (fun s => (P s).obj (op Y)) i) ((piObjIso P (op Y)).hom
          ((∏ᶜ P).map f.op ((piObjIso P (op X)).inv w)))
          = (Pi.π (fun s => (P s).obj (op Y)) i) ((piObjIso P (op Y)).hom
            (x f hf)) := by
      intro i
      rw [proj i Y ((∏ᶜ P).map f.op ((piObjIso P (op X)).inv w)),
        proj i Y (x f hf),
        NatTrans.naturality_apply (φ := Pi.π P i) f.op ((piObjIso P (op X)).inv w),
        hπ i, ht i f hf]
    -- Extensionality of the elements of a product of types is the Mathlib
    -- lemma Types.limit_ext (same pattern as Equalizer.FirstObj.ext).
    have heq : (piObjIso P (op Y)).hom
        ((∏ᶜ P).map f.op ((piObjIso P (op X)).inv w))
        = (piObjIso P (op Y)).hom (x f hf) := by
      apply Limits.Types.limit_ext
      rintro ⟨i⟩
      exact comp i
    -- An iso is injective: conclude through the inverse transport.
    have inj : ∀ a b : (∏ᶜ P).obj (op Y),
        (piObjIso P (op Y)).hom a = (piObjIso P (op Y)).hom b → a = b := by
      intro a b hab
      calc a = (piObjIso P (op Y)).inv ((piObjIso P (op Y)).hom a) := by simp
        _ = (piObjIso P (op Y)).inv ((piObjIso P (op Y)).hom b) := by rw [hab]
        _ = b := by simp
    exact inj _ _ heq

end Produit

section Acyclicite

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **Crossing Part 20 x Part 79 — flasque and injective is acyclic**:
for an abelian sheaf `F` flasque at the level of sieves (composed with
`forget`) **and** injective in the category of sheaves, the cohomology
`H^{n+1}` is trivial. The cancellation is the Mathlib instance already
bridged by Part 20; this theorem consumes it in the flasque setting.
The stone laid here points exactly at the missing link of Godement's
theorem II.5: *flasque => injective* (II.5.2, via Zorn) — a documented
boundary of the lake, consciously not crossed. -/
theorem subsingleton_H_succ_of_flasque_of_injective
    (F : Sheaf J AddCommGrpCat.{max v u}) [Injective F]
    [HasSheafify J AddCommGrpCat.{max v u}]
    [HasExt (Sheaf J AddCommGrpCat.{max v u})]
    [IsFlasqueSieves (F.obj ⋙ forget AddCommGrpCat.{max v u})] {n : ℕ} :
    Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) := by
  infer_instance

end Acyclicite

end Grothendieck.FlasqueStability_en
