/-
Grothendieck Part 16 — Subcanonical Grothendieck topologies

A Grothendieck topology J on a category C is **subcanonical** when every
representable presheaf y(X) = Hom(—, X) is already a J-sheaf. This is the
bridge between the Yoneda embedding and the sheaf category: when J is
subcanonical, the Yoneda lemma descends from presheaves to sheaves, yielding
the equivalence  (y(X) → F) ≃ F(X)  for any sheaf F of types.

SGA 4 I 3.4 — the canonical topology is the finest subcanonical topology;
the trivial topology is always subcanonical; the atomic topology is subcanonical
iff pullbacks of covering families are covering.

Epic #1646, See #2159. All `sorry`s eliminated at creation.
-/

import Mathlib.CategoryTheory.Sites.Subcanonical

universe v u

namespace Grothendieck.Subcanonical

open CategoryTheory GrothendieckTopology Opposite Functor

/-! ## 1. Subcanonical hypothesis and ordering

A topology is subcanonical iff it is smaller than the canonical topology.
Equivalently, every representable presheaf is a sheaf.
-/

/-- If J ≤ K and K is subcanonical, then J is subcanonical.
Finer topologies have fewer sheaves; coarser topologies inherit subcanonicality. -/
theorem subcanonical_of_le {C : Type u} [Category.{v} C]
    {J K : GrothendieckTopology C} (h : J ≤ K) [K.Subcanonical] :
    J.Subcanonical := Subcanonical.of_le h

/-- Constructing subcanonicality from the sheaf condition on yoneda objects. -/
theorem subcanonical_of_yoneda_sheaf {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (h : ∀ X : C, Presieve.IsSheaf J (yoneda.obj X)) :
    J.Subcanonical := Subcanonical.of_isSheaf_yoneda_obj J h

/-! ## 2. Bridge theorem: representable presheaves are sheaves

When J is subcanonical, the Yoneda embedding factors through the sheaf
category. Sheafification acts as the identity on representables.
-/

/-- For a subcanonical topology, any representable presheaf is a J-sheaf
(in the Presieve sense). -/
theorem isSheaf_presieve_of_subcanonical {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [Subcanonical J] (X : C) :
    Presieve.IsSheaf J (yoneda.obj X) :=
  Subcanonical.isSheaf_of_isRepresentable (yoneda.obj X)

/-- For a subcanonical topology, any representable presheaf is a J-sheaf
(in the Presheaf sense). This uses the equivalence between the two notions
of sheaf for Type-valued presheaves. -/
theorem isSheaf_presheaf_of_subcanonical {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [Subcanonical J] (X : C) :
    Presheaf.IsSheaf J (yoneda.obj X) :=
  (isSheaf_iff_isSheaf_of_type J (yoneda.obj X)).mpr
    (Subcanonical.isSheaf_of_isRepresentable (yoneda.obj X))

/-! ## 3. Constructing a Sheaf from a representable (Yoneda sheaf) -/

/-- The Yoneda embedding factors through the sheaf category when J is
subcanonical: every representable presheaf is automatically a sheaf. -/
noncomputable def yonedaSheaf {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [Subcanonical J] (X : C) :
    Sheaf J (Type v) :=
  ⟨yoneda.obj X, isSheaf_presheaf_of_subcanonical X⟩

/-! ## 4. Transfer of subcanonicality along fully faithful functors

If a fully faithful functor is continuous (preserves covers) and the
target topology is subcanonical, then the source topology is subcanonical.
-/

/-- Pullback-stability of subcanonicality along fully faithful continuous
functors. -/
theorem subcanonical_pullback {C : Type u} [Category.{v} C]
    {D : Type*} [Category.{v} D] (F : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.Full] [F.Faithful] [F.IsContinuous J K] [K.Subcanonical] :
    J.Subcanonical := subcanonical_of_full_of_faithful F J K

end Grothendieck.Subcanonical
