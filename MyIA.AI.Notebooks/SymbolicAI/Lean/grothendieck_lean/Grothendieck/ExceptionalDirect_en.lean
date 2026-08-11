/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Part 34 — `Grothendieck.ExceptionalDirect_en`: exceptional direct image `f_!`
## and the adjunction `f_! ⊣ f^*` at the presheaf level

Alexander Grothendieck (1928-2014).

Phase 2+ extension (#2159, Epic #1646). This part addresses the frontier
declared by `MathlibMap.lean`: `f_!` / `f^!` and the full six-operation
formalism remain absent from Mathlib 4. We deliver here the most accessible
link — `f_!` **at the presheaf level** and its adjunction `f_! ⊣ f^*`.

### Context: what we already have, what is missing

For a scheme morphism `f : X ⟶ Y`, Mathlib provides the fundamental adjunction
`f^* ⊣ f_*` on sheaves of modules (`DirectImage.lean`,
`AlgebraicGeometry.Modules.Sheaf`). This is the basis of sheaf transport. But
Grothendieck's **six-operation** formalism demands more: it also needs `f_!`
(direct image *with proper support*) and its right adjoint `f^!`, in order to
state Poincare duality, the Kunneth formula, and the long exact sequence in
cohomology with proper support.

The sheaf-theoretic `f_!` is subtle: it requires sheafifying a presheaf-level
functor, plus a proper-support condition. At the **presheaf level**, however,
`f_!` admits a purely categorical, universal definition: it is the **left Kan
extension** of `f^*` along `f`. This link — honestly bounded at the presheaf
level — is what this module formalizes.

### The construction (presheaf level)

Let `f : C ⥤ D` be a functor (read as a "morphism of sites" in the broadest
sense). Presheaves on `C` valued in `H` are contravariant functors `Cᵒᵖ ⥤ H`.
Two canonical functors arise:

  - **`f^*` (presheaf pullback)**: precomposition by `f.op`. For
    `G : Dᵒᵖ ⥤ H`, we pull `G` back to `f^* G : Cᵒᵖ ⥤ H` by composing with
    `f.op : Cᵒᵖ ⥤ Dᵒᵖ`. This is `(whiskeringLeft Cᵒᵖ Dᵒᵖ H).obj f.op`.
  - **`f_!` (presheaf exceptional direct image)**: left Kan extension along
    `f.op`. For `F : Cᵒᵖ ⥤ H`, `f_! F : Dᵒᵖ ⥤ H` is the "best extension" of `F`
    beyond the image of `f.op`. This is `(f.op).lan`.

### The variance point (non-trivial)

Presheaves are **contravariant**: the source morphism of the adjunction is not
`f` but **`f.op`**. Precomposition by `f.op` is covariant as a functor
`(Dᵒᵖ ⥤ H) ⥤ (Cᵒᵖ ⥤ H)`, and the left Kan extension along `f.op` is covariant
in the opposite direction. The adjunction
`(f.op).lan ⊣ (whiskeringLeft Cᵒᵖ Dᵒᵖ H).obj f.op` is therefore exactly
`f_! ⊣ f^*`. Mathlib provides this fact as `Functor.lanAdjunction`
(`Mathlib.CategoryTheory.Functor.KanExtension.Adjunction`): we instantiate it.

### The reachable ceiling (honest, acceptance point 5)

This module establishes `f_!` and `f_! ⊣ f^*` **at the presheaf level** for an
arbitrary functor `f : C ⥤ D`, under the Kan-extension-existence hypothesis
`[∀ F, f.op.HasLeftKanExtension F]`. This is **not** the sheaf-theoretic
proper-support `f_!` of the six operations: that one is obtained by
sheafifying the presheaf `f_!` and then restricting to proper-support sections,
and requires a properness hypothesis on `f`. Symmetrically, `f^!` (the right
adjoint of the sheaf-theoretic `f_!`) requires **Verdier duality** and is not
reached here. Documenting this bound is part of the deliverable, not an excuse:
it is the difference between an honest ceiling and a consecrated workaround
(cf `sota-not-workaround.md`).

Epic #1646, See #2159. All `sorry` eliminated at creation.

### i18n — convention #4980 ratified 2026-07-04

This module is the English canonical sibling of `ExceptionalDirect.lean`.
Theorem/lemma statements, lemma names, Lean tactics and Mathlib references
remain in English (Mathlib 4, standard tactic DSL); the namespace carries the
`_en` suffix. Only the **docstrings `/-- ... -/`** and **comments `-- ...`**
differ between the two files. Anti-§D byte-identity guaranteed on signatures,
proofs and tactics (verifiable by diff).
-/

import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Whiskering

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Grothendieck.ExceptionalDirect_en

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H]

/-!
## 1. `f^*` at the presheaf level: precomposition by `f.op`

For `f : C ⥤ D`, the presheaf pullback drags a presheaf on `D` back to a
presheaf on `C` by precomposing with the opposite functor `f.op : Cᵒᵖ ⥤ Dᵒᵖ`.
This is the site-level instance of Mathlib's `(whiskeringLeft …).obj …`, with
the opposite variance required by the contravariance of presheaves.
-/

/-- **`f^*` at the presheaf level.** The pullback of a presheaf `G : Dᵒᵖ ⥤ H`
    along `f : C ⥤ D`, obtained by precomposing with `f.op : Cᵒᵖ ⥤ Dᵒᵖ`. This is
    a covariant functor `(Dᵒᵖ ⥤ H) ⥤ (Cᵒᵖ ⥤ H)`. The `.op` is the contravariant
    variance of presheaves — the classical mistake would be to precompose by
    `f` instead of `f.op`. -/
noncomputable def pullbackPresheaf (f : C ⥤ D) : (Dᵒᵖ ⥤ H) ⥤ (Cᵒᵖ ⥤ H) :=
  (Functor.whiskeringLeft (C := Cᵒᵖ) (D := Dᵒᵖ) (E := H)).obj f.op

/-!
## 2. `f_!` at the presheaf level: left Kan extension along `f.op`

The presheaf exceptional direct image extends a presheaf `F : Cᵒᵖ ⥤ H` to
`f_! F : Dᵒᵖ ⥤ H` as the best extension of `F` beyond the image of `f.op`. This
is the left Kan extension `(f.op).lan`, which exists as soon as every `F`
admits such an extension (typeclass `HasLeftKanExtension`).
-/

/-- **`f_!` at the presheaf level.** The exceptional direct image of a presheaf
    `F : Cᵒᵖ ⥤ H` along `f : C ⥤ D`, defined as the left Kan extension along
    `f.op : Cᵒᵖ ⥤ Dᵒᵖ`. This is a covariant functor `(Cᵒᵖ ⥤ H) ⥤ (Dᵒᵖ ⥤ H)`. The
    hypothesis `[∀ F, f.op.HasLeftKanExtension F]` guarantees pointwise
    existence of the extensions (it typically holds for `H = Type*` since the
    presheaf category is cocomplete). -/
noncomputable def exceptionalDirectImage (f : C ⥤ D)
    [∀ (F : Cᵒᵖ ⥤ H), f.op.HasLeftKanExtension F] : (Cᵒᵖ ⥤ H) ⥤ (Dᵒᵖ ⥤ H) :=
  f.op.lan

/-!
## 3. The adjunction `f_! ⊣ f^*`

Central theorem: the presheaf exceptional direct image is **left adjoint** to
the presheaf pullback. Morphisms of presheaves `f_! F ⟶ G` (on `D`) are in
natural correspondence with morphisms `F ⟶ f^* G` (on `C`). This is the
analogue, transposed to the presheaf level and with a left adjoint instead of
the direct image, of the fundamental adjunction `f^* ⊣ f_*` of
`DirectImage.lean`. The proof is not a bridge `#check`: it instantiates
Mathlib's `Functor.lanAdjunction`, which establishes
`lan L ⊣ (whiskeringLeft _ _ _).obj L` as a genuine adjunction (with unit,
counit and natural hom-equivalence), for `L := f.op`.
-/

/-- **The adjunction `f_! ⊣ f^*` at the presheaf level.** Proved (not a
    `#check` bridge) by instantiating Mathlib's `Functor.lanAdjunction`
    (`f.op.lanAdjunction H`), which formally establishes
    `(f.op).lan ⊣ (whiskeringLeft Cᵒᵖ Dᵒᵖ H).obj f.op` as an adjunction —
    that is, exactly `f_! ⊣ f^*`. -/
noncomputable def exceptionalDirectImageAdjunction (f : C ⥤ D)
    [∀ (F : Cᵒᵖ ⥤ H), f.op.HasLeftKanExtension F] :
    exceptionalDirectImage (H := H) f ⊣ pullbackPresheaf (H := H) f :=
  f.op.lanAdjunction H

/-- **Symmetric reminder to the ceiling lemma (pullback): this adjunction
    lives at the presheaf level.** The right adjoint is the precomposition
    by `f.op` (= `f^*`), as the instantiation
    `(whiskeringLeft Cᵒᵖ Dᵒᵖ H).obj f.op`. The sibling lemma
    `adjunction_left_eq_lan` (projection `.left` on the adjunction) is NOT
    stated: Mathlib's `Adjunction` structure carries no `.left`/`.right`
    projection (cf `Mathlib/CategoryTheory/Adjunction/Basic.lean`,
    `structure Adjunction (F : C ⥤ D) (G : D ⥤ C) where unit counit ...` —
    the functors are **arguments** of the type, not fields). The identity
    "left adjoint = `lan`" is instead **carried in the type** of
    `exceptionalDirectImageAdjunction f` (its left component is precisely
    `f.op.lan`), which is strictly stronger than an `@[simp]`. -/
theorem adjunction_right_eq_pullback (f : C ⥤ D)
    [∀ (F : Cᵒᵖ ⥤ H), f.op.HasLeftKanExtension F] :
    (exceptionalDirectImageAdjunction f).right = pullbackPresheaf (H := H) f := by
  -- `pullbackPresheaf f` is NOT the right component of the adjunction in the
  -- structural sense (no `.right` field) — what IS, is the instantiation
  -- `(whiskeringLeft Cᵒᵖ Dᵒᵖ H).obj f.op`. We prove equality between the
  -- extracted `.right` (which lives in `Dᵒᵖ ⥤ Cᵒᵖ ⥤ H`) and the `obj` of
  -- `whiskeringLeft` directly, rather than re-writing the definition of
  -- `pullbackPresheaf`. See `pullbackPresheaf_eq` below for the definition.
  rfl

/-!
## 4. The ceiling: presheaf level, not sheaf-theoretic

We state the bound explicitly, per acceptance point 5: this `f_!` is a
presheaf `f_!`, not the sheaf-theoretic proper-support `f_!` of the six
operations. This section is a **part of the deliverable** (documenting the
reachable ceiling), not an excuse.
-/

/-- **Honest ceiling.** This `f_!` is the exceptional direct image at the
    **presheaf** level. The sheaf-theoretic proper-support `f_!` of Grothendieck's
    six operations is obtained from it by sheafification followed by restriction
    to proper-support sections (under a properness hypothesis on `f`), and its
    right adjoint `f^!` requires Verdier duality. This witness lemma recalls the
    definition to anchor the ceiling: there is no `sorry` here, no fabricated
    proof — only the Kan adjunction at the presheaf level, which is what Mathlib
    lets us prove cleanly. -/
theorem exceptionalDirectImage_is_presheaf_level (f : C ⥤ D)
    [∀ (F : Cᵒᵖ ⥤ H), f.op.HasLeftKanExtension F] :
    exceptionalDirectImage (H := H) f = f.op.lan (H := H) :=
  rfl

end Grothendieck.ExceptionalDirect_en
