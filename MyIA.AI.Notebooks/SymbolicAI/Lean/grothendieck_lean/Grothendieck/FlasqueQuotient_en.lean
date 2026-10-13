/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Grothendieck tribute — Part 83 (EN sibling of `Grothendieck/FlasqueQuotient.lean`):
the bridge closes — sieves, Mathlib, and the Godement II.3.1 quotient.

Alexandre Grothendieck (1928-2014).

Phase 2 extension (#2159, Epic #1646).
-/
/-
Part 83 — The bridge closes: sieves, Mathlib, and the Godement II.3.1 quotient
===============================================================================

Context (Parts 79, 80, 81, 82): sieve flasqueness `IsFlasqueSieves` (Part 79)
demands amalgamation of every compatible family on **every** sieve — covering
or not — where Mathlib's definition `TopCat.Presheaf.IsFlasque` only demands
epimorphy of restrictions. Part 82 documented the residual gap: the bridge
`IsFlasque → IsFlasqueSieves` was established for **single-generator** sieves
(`exists_isAmalgamation_of_isFlasque_generate_singleton`), the
multi-generator frontier remaining open.

This Part closes both ends:

* **Forward** (`isFlasqueSieves_of_isFlasque_of_isSheaf`): a **sheaf** of
  types that is flasque in Mathlib's sense is sieve-flasque. On `Opens X`,
  the multi-generator frontier of Part 82 disappears **without Zorn**: the
  lattice of opens bounds the family — the supremum `V₀` of the members of
  the sieve is an open, the family glues there by the sheaf condition
  (`presieveOfCovering.mem_grothendieckTopology`), and flasqueness extends
  the section from `V₀` to `U`. This is the elementary "glue then extend"
  argument, where a general site would require transfinite reasoning.

* **Back** (`isFlasque_of_isFlasqueSieves`): sieve flasqueness implies
  Mathlib's for **every** arrow of `Opens X` — the site is thin, every arrow
  there is mono, and the mono lift of Part 82
  (`exists_lift_of_isFlasqueSieves_of_mono`) applies to each restriction.
  On a general site the forward direction only holds for single-generator
  sieves and the return only for mono arrows: on `Opens X`, the two notions
  coincide for sheaves.

* **Quotient** (`isFlasqueSieves_of_shortExact_of_isFlasque₁₂`): Godement
  II.3.1, second half, read on the sieve side — in a short exact sequence of
  sheaves of abelian groups whose first two terms are sieve-flasque, so is
  the third. Mirror of `TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂`
  (Mathlib), whose proof consumes the flasqueness of `X₁` (via
  `epi_of_shortExact`, Zorn) for the epimorphy of `S.g` on each open, and
  that of `X₂` for the epimorphy of the composite's restrictions. Here both
  ingredients come from the sieve counterparts: the epi of `S.g` from Part
  82 (`epi_of_shortExact_of_isFlasqueSieves`), the restrictions of `X₂`
  from the return bridge above.
-/
import Grothendieck.Flasque
import Grothendieck.FlasqueExact
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Topology.Sheaves.SheafCondition.Sites

universe u v

namespace Grothendieck.FlasqueQuotient_en

open CategoryTheory TopCat TopCat.Presheaf TopologicalSpace Opposite

set_option maxHeartbeats 800000

section Pont

variable {X : TopCat.{u}}

/-- **Return bridge**: sieve-flasque ⇒ flasque in Mathlib's sense. Every
arrow of `Opens X` is mono (thin site), so the mono lift of Part 82 provides
a preimage for every section along every restriction — epimorphy in
Mathlib's sense. No sheaf hypothesis: the return holds for any presheaf of
types on `Opens X`. -/
theorem isFlasque_of_isFlasqueSieves {P : TopCat.Presheaf (Type (max u u)) X}
    [IsFlasqueSieves P] : P.IsFlasque where
  epi {U V} i := by
    refine (CategoryTheory.epi_iff_surjective (P.map i)).mpr (fun s => ?_)
    obtain ⟨t, ht⟩ := exists_lift_of_isFlasqueSieves_of_mono (P := P) i.unop s
    exact ⟨t, ht⟩

/-- **Forward bridge**: sheaf + flasque in Mathlib's sense ⇒ sieve-flasque.
The proof closes the multi-generator frontier documented at the head of
`Grothendieck.FlasqueExact`: given a sieve `R` on `U`, the supremum `V₀` of
its members is an open of `X`, the sieve becomes covering there, the sheaf
condition glues the family into a section of `V₀`, and flasqueness extends
that section along the inclusion `V₀ ⟶ U`. The lattice of opens plays the
role that Zorn plays on a general site: it bounds the family before
gluing. -/
theorem isFlasqueSieves_of_isFlasque_of_isSheaf {P : TopCat.Presheaf (Type (max u u)) X}
    (hsheaf : Presieve.IsSheaf (Opens.grothendieckTopology X) P)
    (hfla : P.IsFlasque) : IsFlasqueSieves P where
  amalgamates {U} R x hx := by
    -- The covering family of the sieve's members, and its supremum.
    set fam := coveringOfPresieve _ R.arrows with hfam
    set V₀ : Opens X := iSup fam with hV₀
    -- Flasqueness will extend the section of `V₀` to `U` along the inclusion.
    have hle : V₀ ≤ U := iSup_le fun j => leOfHom j.2.1
    -- Every arrow `g : W ⟶ V₀` of the covering presieve comes from a member
    -- of the sieve: the composite `g ≫ (V₀ ⟶ U)` is an arrow of `R` (the
    -- arrows of `Opens X` form a subsingleton: the composite coincides with
    -- the original member arrow).
    have kar : ∀ {W : Opens X} {g : W ⟶ V₀}, presieveOfCovering fam g →
        R.arrows (g ≫ homOfLE hle) := by
      intro W g ⟨i, hi⟩
      subst hi
      have heq : (g ≫ homOfLE hle : fam i ⟶ U) = i.2.1 := Subsingleton.elim _ _
      rw [heq]
      exact i.2.2
    -- The transported family on the covering presieve of `V₀`.
    set z : Presieve.FamilyOfElements P (presieveOfCovering fam) :=
      fun W g hg => x (g ≫ homOfLE hle) (kar hg) with hzdef
    have hz : z.Compatible := by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ _
      exact hx g₁ g₂ (kar h₁) (kar h₂) (Subsingleton.elim _ _)
    -- The covering presieve generates a sieve of the topology: the sheaf
    -- condition glues the family into a section of `V₀`.
    have hmem : Sieve.generate (presieveOfCovering fam) ∈ Opens.grothendieckTopology X V₀ :=
      presieveOfCovering.mem_grothendieckTopology fam
    obtain ⟨t₀, ht₀⟩ := hsheaf _ hmem z.sieveExtend hz.sieveExtend
    have hz₀ : z.IsAmalgamation t₀ := by
      rw [← Presieve.restrict_extend hz]
      exact Presieve.isAmalgamation_restrict _ _ _ ht₀.1
    obtain ⟨t, ht⟩ := (CategoryTheory.epi_iff_surjective (P.map (homOfLE hle).op)).mp
      (hfla.epi (homOfLE hle).op) t₀
    refine ⟨t, ?_⟩
    intro Y f hf
    -- `Y` is a member of the covering family: arrow towards `V₀`.
    have hYle : Y ≤ V₀ := le_iSup fam ⟨Y, f, hf⟩
    have hmemY : presieveOfCovering fam (homOfLE hYle) := ⟨⟨Y, f, hf⟩, rfl⟩
    have hstep : P.map f.op t = P.map (homOfLE hYle : Y ⟶ V₀).op t₀ := by
      have hfeq : f = (homOfLE hYle : Y ⟶ V₀) ≫ homOfLE hle := Subsingleton.elim _ _
      rw [hfeq, op_comp, Functor.map_comp, CategoryTheory.comp_apply, ht]
    have hzY : P.map (homOfLE hYle : Y ⟶ V₀).op t₀
        = x ((homOfLE hYle : Y ⟶ V₀) ≫ homOfLE hle) (kar hmemY) :=
      hz₀ _ hmemY
    have hxm : x ((homOfLE hYle : Y ⟶ V₀) ≫ homOfLE hle) (kar hmemY) = x f hf := by
      have heq : (homOfLE hYle : Y ⟶ V₀) ≫ homOfLE hle = f := Subsingleton.elim _ _
      rw [heq]
    rw [hstep, hzY]
    exact hxm

end Pont

section Exact

variable {X : TopCat.{u}}

/-- **Godement II.3.1, second half, sieve flavour**: in a short exact
sequence of sheaves of abelian groups `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` where `X₁` and
`X₂` are sieve-flasque, `X₃` is sieve-flasque. Mirror of
`TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂` (Mathlib): the
epimorphy of `S.g` on each open comes from Part 82 (starting from the sieve
flasqueness of `X₁`), the epimorphy of the restrictions of `X₂` from the
return bridge above, and the conclusion from the forward bridge — `X₃` is a
sheaf and its restrictions are epi, hence it amalgamates every sieve.
[God58] Chap. II §3.1. -/
theorem isFlasqueSieves_of_shortExact_of_isFlasque₁₂
    {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    [IsFlasqueSieves (S.X₁.obj ⋙ CategoryTheory.forget AddCommGrpCat)]
    [IsFlasqueSieves (S.X₂.obj ⋙ CategoryTheory.forget AddCommGrpCat)] :
    IsFlasqueSieves (S.X₃.obj ⋙ CategoryTheory.forget AddCommGrpCat) := by
  -- Epimorphy of `S.g` on each open, from the sieve flasqueness of `X₁`
  -- (Part 82).
  have hg : ∀ U : Opens X, Epi (S.g.hom.app (op U)) := fun U =>
    epi_of_shortExact_of_isFlasqueSieves hS
  -- Restrictions of `X₂` epi on types: return bridge, then transfer to
  -- AddCommGrpCat via surjectivity (the forgetful functor does not change
  -- the underlying map).
  have hI₂ : TopCat.Presheaf.IsFlasque (S.X₂.obj ⋙ CategoryTheory.forget AddCommGrpCat) :=
    isFlasque_of_isFlasqueSieves
  have hX₂ : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), Epi (S.X₂.obj.map i) := by
    intro U V i
    refine (AddCommGrpCat.epi_iff_surjective _).mpr (fun s => ?_)
    obtain ⟨t, ht⟩ := (CategoryTheory.epi_iff_surjective
      ((S.X₂.obj ⋙ CategoryTheory.forget AddCommGrpCat).map i)).mp (hI₂.epi i) s
    exact ⟨t, ht⟩
  -- Restrictions of `X₃` epi: mirror of the Mathlib proof — by naturality
  -- the composite `X₂.map i ≫ S.g.app` is epi (two epi factors), and the
  -- epi of the composite transfers to `X₃.map i` after cancelling
  -- `S.g.app`.
  have hX₃ : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), Epi (S.X₃.obj.map i) := by
    intro U V i
    have hgV : Epi (S.g.hom.app V) := hg V.unop
    have hcomp : Epi (S.g.hom.app U ≫ S.X₃.obj.map i) := by
      rw [← S.g.hom.naturality i]
      exact CategoryTheory.epi_comp' (hX₂ i) hgV
    exact @CategoryTheory.epi_of_epi _ _ _ _ _ (S.g.hom.app U) (S.X₃.obj.map i) hcomp
  -- `X₃` is a sheaf of types (transfer through the forgetful functor, which
  -- creates limits) and Mathlib-flasque on types: the forward bridge
  -- concludes.
  have hX₃sheaf : Presieve.IsSheaf (Opens.grothendieckTopology X)
      (S.X₃.obj ⋙ CategoryTheory.forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp ((isSheaf_iff_isSheaf_comp _ _).mp S.X₃.2)
  exact isFlasqueSieves_of_isFlasque_of_isSheaf hX₃sheaf
    ⟨fun i => by
      refine (CategoryTheory.epi_iff_surjective _).mpr (fun s => ?_)
      obtain ⟨t, ht⟩ := (AddCommGrpCat.epi_iff_surjective (S.X₃.obj.map i)).mp (hX₃ i) s
      exact ⟨t, ht⟩⟩

end Exact

end Grothendieck.FlasqueQuotient_en
