/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.Godement

/-!
# Functoriality of the Godement sheaf: `C⁰` is an endofunctor

English canonical sibling of `Grothendieck/GodementFunctor.lean` (Part 85).

Continuation of Part 84 [God58, Chap. II §4.1]. The construction
`C⁰F : U ↦ ∏_{x ∈ U} Fₓ` is defined there **object by object**, together with
its three properties (flasque, sheaf, injective unit on sheaves). To build the
canonical resolution — iterating `C⁰` on kernels — one prerequisite is
missing: that `C⁰` be a **functor**. That is the object of this Part, and
nothing else.

Three facts, in the narrative order:

1. `godementHomApp`: a morphism `φ : F ⟶ G` of presheaves of abelian groups
   acts on Godement sections **pointwise in the stalks**, via
   `Presheaf.stalkFunctor`. No compatibility condition to check: a Godement
   section is a freely chosen function, and the action is the induced one on
   the values.
2. `godementFunctor`: `C⁰` is an **endofunctor** of `X.Presheaf AddCommGrpCat`.
   Identity and composition are those of the stalks — the functoriality of
   `C⁰` is free, like its flasqueness: everything comes from the fact that
   `C⁰` is a product of evaluations.
3. `toGodementNatTrans`: the unit `F → C⁰F` is **natural** in `F` — a natural
   transformation `𝟭 ⟶ C⁰`. Naturality is an instance of
   `Presheaf.stalkFunctor_map_germ_apply`: the germ of the morphism is the
   morphism of the germs.

What is acquired is what is proved: an endofunctor, and a natural unit. The
lake claims nothing more — in particular, the preservation of monomorphisms by
`C⁰` is **not** established here.

i18n convention (EPIC #4980 ratified 2026-07-04): `_en` suffix on the
namespace (`Grothendieck.GodementFunctor_en`), mirror imports, translated
docstrings and comments. Theorem statements, Lean tactics, lemma names and
Mathlib references remain in English. Anti-§D byte-identity guaranteed:
the namespace body is preserved bit for bit (statements and proofs
byte-identical between `GodementFunctor.lean` and `GodementFunctor_en.lean`).

## References

  - R. Godement, *Topologie algebrique et theorie des faisceaux* [God58],
    Chap. II §4.1. The construction `C⁰(F)` of the discontinuous sections.
-/

universe u

open CategoryTheory Category Limits TopCat TopologicalSpace Opposite

namespace Grothendieck.GodementFunctor_en

variable {X : TopCat.{u}}

/-- The action on stalks, pointwise: `C⁰` acts on a Godement section by
transporting each germ through the stalk functor. -/
noncomputable def godementHomApp {F G : X.Presheaf AddCommGrpCat.{u}} (φ : F ⟶ G)
    (U : Opens X) (s : godementSection F U) : godementSection G U :=
  fun x => (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X)).map φ (s x)

/-- `C⁰` is additive: transport in the stalks is. -/
theorem godementHomApp_add {F G : X.Presheaf AddCommGrpCat.{u}} (φ : F ⟶ G)
    (U : Opens X) (s t : godementSection F U) :
    godementHomApp φ U (s + t) = godementHomApp φ U s + godementHomApp φ U t := by
  funext x
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X)).map φ (s x + t x)
      = (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X)).map φ (s x)
        + (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X)).map φ (t x)
  exact map_add
    (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X)).map φ))
    (s x) (t x)

/-- `C⁰` preserves zero. -/
theorem godementHomApp_zero {F G : X.Presheaf AddCommGrpCat.{u}} (φ : F ⟶ G)
    (U : Opens X) : godementHomApp φ U (0 : godementSection F U) = 0 := by
  funext x
  exact map_zero
    (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X)).map φ))

/-- `C⁰(𝟙 F) = 𝟙 (C⁰F)`: `stalkFunctor` is a functor, its `map_id` suffices. -/
theorem godementHomApp_id (F : X.Presheaf AddCommGrpCat.{u}) (U : Opens X)
    (s : godementSection F U) : godementHomApp (𝟙 F) U s = s := by
  funext x
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X)).map (𝟙 F) (s x) = s x
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- `C⁰(φ ≫ ψ) = C⁰ψ ∘ C⁰φ`: same reason, `Functor.map_comp`. -/
theorem godementHomApp_comp {F G H : X.Presheaf AddCommGrpCat.{u}} (φ : F ⟶ G)
    (ψ : G ⟶ H) (U : Opens X) (s : godementSection F U) :
    godementHomApp (φ ≫ ψ) U s = godementHomApp ψ U (godementHomApp φ U s) := by
  funext x
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X)).map (φ ≫ ψ) (s x)
      = (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X)).map ψ
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X)).map φ (s x))
  rw [CategoryTheory.Functor.map_comp]
  rfl

/-- `C⁰φ` is a morphism of presheaves. Naturality is **definitional**:
restricting then transporting in the stalks, or transporting then restricting,
are the same function — both sides restrict before applying `stalkFunctor`. -/
noncomputable def godementMapHom {F G : X.Presheaf AddCommGrpCat.{u}} (φ : F ⟶ G) :
    godementPresheaf F ⟶ godementPresheaf G where
  app U :=
    AddCommGrpCat.ofHom
      { toFun := godementHomApp φ U.unop
        map_zero' := godementHomApp_zero φ U.unop
        map_add' := godementHomApp_add φ U.unop }
  naturality U V f := by
    ext s
    rfl

/-- `C⁰` preserves the identity. -/
theorem godementMapHom_id (F : X.Presheaf AddCommGrpCat.{u}) :
    godementMapHom (𝟙 F) = 𝟙 (godementPresheaf F) := by
  ext U s
  funext x
  exact congrFun (godementHomApp_id F U s) x

/-- `C⁰` preserves composition. -/
theorem godementMapHom_comp {F G H : X.Presheaf AddCommGrpCat.{u}} (φ : F ⟶ G)
    (ψ : G ⟶ H) :
    godementMapHom (φ ≫ ψ) = godementMapHom φ ≫ godementMapHom ψ := by
  ext U s
  funext x
  exact congrFun (godementHomApp_comp φ ψ U s) x

/-- **`C⁰` is an endofunctor** of the category of presheaves of abelian groups
on `X`. This is the prerequisite that was missing in order to iterate the
construction on kernels and form the Godement complex. [God58] Chap. II §4.1. -/
noncomputable def godementFunctor :
    X.Presheaf AddCommGrpCat.{u} ⥤ X.Presheaf AddCommGrpCat.{u} where
  obj F := godementPresheaf F
  map φ := godementMapHom φ
  map_id F := godementMapHom_id F
  map_comp φ ψ := godementMapHom_comp φ ψ

/-- Naturality of the Godement unit: taking the germ of each point commutes
with the action of a morphism. This is `Presheaf.stalkFunctor_map_germ_apply` —
the germ of the morphism is the morphism of the germs. -/
theorem toGodement_naturality {F G : X.Presheaf AddCommGrpCat.{u}} (φ : F ⟶ G) :
    toGodement F ≫ godementMapHom φ = φ ≫ toGodement G := by
  ext U s
  funext x
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply U (x : X) x.2 φ s

/-- **The Godement unit is natural**: `toGodement` is a natural transformation
from the identity to the endofunctor `C⁰`. With `C⁰` functorial, the natural
unit `𝟭 ⟶ C⁰` is exactly what allows writing the first step of the Godement
complex `0 → F → C⁰F → C⁰(K) → ⋯`. -/
noncomputable def toGodementNatTrans :
    𝟭 (X.Presheaf AddCommGrpCat.{u}) ⟶ godementFunctor (X := X) where
  app F := toGodement F
  naturality F G φ := by
    exact (toGodement_naturality φ).symm

end Grothendieck.GodementFunctor_en
