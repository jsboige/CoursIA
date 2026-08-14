/-
# Hommage Grothendieck — Part 16: Subcanonical Grothendieck topologies (English mirror)

Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Subcanonical Grothendieck topologies (English mirror)

This module hosts **5 theorem + 1 def** on **subcanonicality** (bridge Yoneda
→ sheaves), organised in 4 thematic sections: (1) subcanonical hypothesis and ordering,
(2) bridge theorem: representable presheaves are sheaves, (3) constructing a Sheaf from a
representable, (4) transfer along fully faithful functors.

### Accessibility note Epic #1452/#1453

This module is **voluntarily didactic**: each target exercises a Mathlib 4 canonical
lemma on the subcanonical hypothesis (4 thematic sections, 4 tactics on Yoneda,
presieve/presheaf sheaf condition, definitional extension). The substance is not in the
mathematical difficulty but in the **canonical-leverage diversity** — every theorem
applies a named Mathlib 4 lemma (Subcanonical.of_le, Subcanonical.of_isSheaf_yoneda_obj,
Subcanonical.isSheaf_of_isRepresentable, subcanonical_of_full_of_faithful).

### i18n convention (EPIC #4980 ratified by user 2026-07-04, see code-style.md Lean i18n)

This substantial module is paired with its French canonical counterpart in the sibling file
Subcanonical.lean (sibling pair model, see PR #6154 for the pilot on Utility.lean).
-/

import Mathlib.CategoryTheory.Sites.Subcanonical

universe w v u

namespace Grothendieck.Subcanonical_en

open CategoryTheory GrothendieckTopology Opposite Functor Sheaf

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

/-! ## 5. Canonical Mathlib bridges (Grothendieck tribute)

Bridges to the 4 canonical constructors in `Mathlib/CategoryTheory/Sites/Canonical.lean`
extending the namespace `Grothendieck` with the foundational operators of subcanonicality:
(5.1) the Subcanonical instance on the canonical topology + extraction of the `le_canonical`
field, (5.2) the functors `J.yoneda` / `J.uliftYoneda` that link the category C to the
category of J-sheaves, and (5.3) the theorem `isSheaf_yoneda_obj` for the canonical topology. -/

/-! ### 5.1 Bridge-instance: the canonical topology is subcanonical

The canonical topology `canonicalTopology C` is the **finest** subcanonical
topology (the upper bound of subcanonical topologies on C). -/
instance subcanonical_canonical {C : Type u} [Category.{v} C] :
    (canonicalTopology C).Subcanonical :=
  inferInstance

/-- Bridge-lemma: extraction of the `le_canonical` field of a Subcanonical instance. -/
theorem subcanonical_le_canonical {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [Subcanonical J] :
    J ≤ canonicalTopology C :=
  Subcanonical.le_canonical

/-! ### 5.2 Bridge-def: the Yoneda functor to the category of J-sheaves

For a subcanonical topology J, the Yoneda embedding factors through the
category of J-sheaves: the operator `J.yoneda` explicitly returns a functor
`C ⥤ Sheaf J (Type v)`. -/
noncomputable def subcanonical_yoneda {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [h : Subcanonical J] :
    C ⥤ Sheaf J (Type v) :=
  J.yoneda

/-- Ulift variant of the Yoneda embedding to the category of J-sheaves,
allowing a universe raise to `Sheaf J (Type (max v w))`. -/
noncomputable def subcanonical_uliftYoneda {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [Subcanonical J] :
    C ⥤ Sheaf J (Type (max v w)) :=
  J.uliftYoneda

/-! ### 5.3 Bridge-theorem: yoneda.obj is a sheaf for the canonical topology

For the canonical topology, every `yoneda.obj X` is automatically a sheaf
(key point: this is the definition of `canonicalTopology C` as the topology
generated by representables). -/
theorem isSheaf_yoneda_obj_canonical {C : Type u} [Category.{v} C] (X : C) :
    Presieve.IsSheaf (canonicalTopology C) (yoneda.obj X) :=
  isSheaf_yoneda_obj X

end Grothendieck.Subcanonical_en
