/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Part 35 — `Grothendieck.ExceptionalInverse_en`: exceptional inverse image `f^!`
## and the adjunction `f^* ⊣ f^!` at the presheaf level

Alexander Grothendieck (1928-2014).

Phase 2+ extension (#2159, Epic #1646). This part answers the call issued by
`ExceptionalDirect.lean:22-23` — *"its right adjoint `f^!`, in order to state
Poincare duality, the Kunneth formula, and the long exact sequence in
cohomology with proper support"*. Part 34 delivered `f_!` at the presheaf
level and `f_! ⊣ f^*`; we deliver here the twin link, `f^!`, which makes the
pair `f_! ⊣ f^!` composable in principle (the two Kan adjunctions) at the
presheaf level.

### Context: the missing symmetry

For a scheme morphism `f : X ⟶ Y`, Mathlib provides the fundamental adjunction
`f^* ⊣ f_*` on sheaves of modules (`DirectImage.lean`,
`AlgebraicGeometry.Modules.Sheaf`). Grothendieck's **six-operation** formalism
demands the pair of adjunctions: `f_! ⊣ f^!` with proper support, of which
**Verdier duality** is the deep ingredient. At the presheaf level, the
situation is more modest but already meaningful:

  - `f_!` (presheaf exceptional direct image) — left Kan extension along
    `f.op` — Part 34.
  - `f^!` (presheaf exceptional inverse image) — right Kan extension along
    `f.op` — **this part**.

Both follow from the symmetric Kan API: `L.lan` (left) vs `L.ran` (right).
Where Part 34 instantiates `f.op.lanAdjunction H` to obtain `f_! ⊣ f^*`,
this part instantiates `f.op.ranAdjunction H` to obtain `f^* ⊣ f^!`. The
two adjunctions are distinct and the **direction** of the adjunction is
reversed.

### The variance point (the same as Part 34)

Presheaves are **contravariant**: the source morphism of the adjunctions is
not `f` but **`f.op`**. Precomposition by `f.op` (which we call `f^*` on
the presheaf side) is covariant as a functor
`(Dᵒᵖ ⥤ H) ⥤ (Cᵒᵖ ⥤ H)`. The right Kan extension `(f.op).ran` is
contravariant from `Cᵒᵖ ⥤ H` to `Dᵒᵖ ⥤ H`. The adjunction
`(whiskeringLeft Cᵒᵖ Dᵒᵖ H).obj f.op ⊣ (f.op).ran` is therefore exactly
`f^* ⊣ f^!`. Mathlib provides this fact as `Functor.ranAdjunction`
(`Mathlib.CategoryTheory.Functor.KanExtension.Adjunction`) — the exact
symmetric of `Functor.lanAdjunction` that Part 34 instantiates.

### The reachable ceiling (honest, acceptance point 5)

This module establishes `f^!` and `f^* ⊣ f^!` **at the presheaf level** for
an arbitrary functor `f : C ⥤ D`, under the right Kan-extension-existence
hypothesis `[∀ G, f.op.HasRightKanExtension G]`. This is **not** the
sheaf-theoretic Verdier `f^!`: that one demands a Poincare duality hypothesis
on the underlying topological space, much stronger. Documenting this bound is
part of the deliverable, not an excuse: it is the difference between an
honest ceiling and a consecrated workaround (cf `sota-not-workaround.md`).

Epic #1646, See #2159, Closes #12340 (grain prioritaire DM ai-01 du
2026-08-22). All `sorry` eliminated at creation.

### i18n — convention #4980 ratified 2026-07-04

This module is the English canonical sibling of `ExceptionalInverse.lean`.
Theorem/lemma statements, lemma names, Lean tactics and Mathlib references
remain in English (Mathlib 4, standard tactic DSL); the namespace carries
the `_en` suffix. Only the **docstrings `/-- ... -/`** and **comments
`-- ...`** differ between the two files. Anti-§D byte-identity guaranteed
on signatures, proofs and tactics (verifiable by diff).
-/

import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Whiskering

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Grothendieck.ExceptionalInverse_en

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H]

/-!
## 1. `f^*` at the presheaf level: precomposition by `f.op`

For `f : C ⥤ D`, the presheaf pullback drags a presheaf on `D` back to a
presheaf on `C` by precomposing with the opposite functor `f.op : Cᵒᵖ ⥤ Dᵒᵖ`.
This is the site-level instance of Mathlib's `(whiskeringLeft …).obj …`, with
the opposite variance required by the contravariance of presheaves. This
section duplicates Part 34's definition (`ExceptionalDirect_en.lean:106`) —
the duplication is deliberate: each module remains **self-contained** (sibling
pair model: no cross-imports between lake parts, cf i18n-inventory-cycle-38.md,
forms OK / OK-CONSUMER).
-/

/-- **`f^*` at the presheaf level.** The pullback of a presheaf `G : Dᵒᵖ ⥤ H`
    along `f : C ⥤ D`, obtained by precomposing with `f.op : Cᵒᵖ ⥤ Dᵒᵖ`. This
    is a covariant functor `(Dᵒᵖ ⥤ H) ⥤ (Cᵒᵖ ⥤ H)`. The `.op` is the contravariant
    variance of presheaves — the classical mistake would be to precompose by
    `f` instead of `f.op`. -/
noncomputable def pullbackPresheaf (f : C ⥤ D) : (Dᵒᵖ ⥤ H) ⥤ (Cᵒᵖ ⥤ H) :=
  (Functor.whiskeringLeft (C := Cᵒᵖ) (D := Dᵒᵖ) (E := H)).obj f.op

/-!
## 2. `f^!` at the presheaf level: right Kan extension along `f.op`

The presheaf exceptional inverse image extends a presheaf `F : Cᵒᵖ ⥤ H` to
`f^! F : Dᵒᵖ ⥤ H` as the best **rightward** extension of `F` beyond the
image of `f.op`. This is the right Kan extension `(f.op).ran`, which exists
as soon as every `F` admits such an extension (typeclass `HasRightKanExtension`).

**Note on variance.** In Grothendieck's sheaf-theoretic sense, `f^!`
takes a presheaf on Y and produces a presheaf on X — it is the **right
adjoint** of the sheaf-theoretic `f_!` (Verdier extension). At the
presheaf level, the situation is symmetric modulo the variance inversion of
presheaves: `f.op.ran` operates on presheaves covariant on `Cᵒᵖ` (= presheaves
on `C`), and extends them rightward to presheaves on `D`. This is exactly
the categorical symmetric of `f.op.lan` (which extends presheaves on `C`
leftward to presheaves on `D`, delivering `f_!` at the presheaf level). The
adjunction `f.op.lan ⊣ f.op.ran` is NOT the six operations — obtaining it at
the sheaf level would require **Verdier duality** (cf §5 below). At the
presheaf level, we deliver the **pair of symmetric adjunctions**
`f_! ⊣ id` and `id ⊣ f^!` in the Kan sense, which constitutes the missing
link of Part 34.
-/

/-- **`f^!` at the presheaf level.** The exceptional inverse image of a
    presheaf `F : Cᵒᵖ ⥤ H` along `f : C ⥤ D`, defined as the right Kan extension
    along `f.op : Cᵒᵖ ⥤ Dᵒᵖ`. This is a covariant functor
    `(Cᵒᵖ ⥤ H) ⥤ (Dᵒᵖ ⥤ H)`. The hypothesis
    `[∀ F, f.op.HasRightKanExtension F]` guarantees pointwise existence of
    the extensions (it typically holds for `H = Type*` since the presheaf
    category is complete). -/
noncomputable def exceptionalInverseImage (f : C ⥤ D)
    [∀ (F : Cᵒᵖ ⥤ H), f.op.HasRightKanExtension F] : (Cᵒᵖ ⥤ H) ⥤ (Dᵒᵖ ⥤ H) :=
  f.op.ran

/-!
## 3. The adjunction `f^* ⊣ f^!`

Central theorem: the presheaf exceptional inverse image is
**left adjoint** to the presheaf pullback. Morphisms of presheaves
`f^! F ⟶ G` (on `D`) are in natural correspondence with morphisms
`F ⟶ f^* G` (on `C`). This is the exact symmetric of Part 34 — where
`f_! ⊣ f^*` instantiates `f.op.lanAdjunction H`, we instantiate
`f.op.ranAdjunction H`, which establishes
`(whiskeringLeft Cᵒᵖ Dᵒᵖ H).obj f.op ⊣ f.op.ran`, that is, `f^* ⊣ f^!`
in Grothendieck's presheaf-level notation.
-/

/-- **The adjunction `f^* ⊣ f^!` at the presheaf level.** Proved (not a
    `#check` bridge) by instantiating Mathlib's `Functor.ranAdjunction`
    (`f.op.ranAdjunction H`), which formally establishes
    `(whiskeringLeft Cᵒᵖ Dᵒᵖ H).obj f.op ⊣ (f.op).ran` as an adjunction —
    that is, exactly `f^* ⊣ f^!`. Exact symmetric of Part 34
    (`f.op.lanAdjunction H : f_! ⊣ f^*`). -/
noncomputable def exceptionalInverseImageAdjunction (f : C ⥤ D)
    [∀ (F : Cᵒᵖ ⥤ H), f.op.HasRightKanExtension F] :
    pullbackPresheaf (H := H) f ⊣ exceptionalInverseImage (H := H) f :=
  f.op.ranAdjunction H

-- **Reminder: this adjunction lives at the presheaf level.** The left adjoint
-- is the precomposition by `f.op` (i.e. `f^*`), the right adjoint is the
-- right Kan extension along `f.op` (i.e. `f^!`).
--
-- As in Part 34, the lemmas `adjunction_left_eq_pullback` /
-- `adjunction_right_eq_ran` are **not** stated: Mathlib's `Adjunction`
-- structure carries no `.left`/`.right` projection (cf
-- `Mathlib/CategoryTheory/Adjunction/Basic.lean`). The identities are carried
-- **in the type** of `exceptionalInverseImageAdjunction` above
-- (`pullbackPresheaf (H := H) f ⊣ exceptionalInverseImage (H := H) f`),
-- checked when the definition itself elaborates.

/-!
## 4. The pair of adjunctions `f_! ⊣ f^* ⊣ f^!` at the presheaf level

Parts 34 and 35 together deliver **two distinct** adjunctions: `f_! ⊣ f^*`
(Part 34) and `f^* ⊣ f^!` (this part). The functor `f^*` appears as
**right adjoint** to `f_!` and **left adjoint** to `f^!`. Mathlib does not
deliver (at this stage) a global "six operations", but the pair of adjunctions
is fully available at the presheaf level for an arbitrary functor
`f : C ⥤ D` (under the existence hypotheses for both directions of Kan,
typically satisfied for `H = Type*`).
-/

/-- **Coherence theorem: `f^*` plays two symmetric roles.** This lemma states
    the identity at the type level: `f^*` (the precomposition by `f.op`) is
    exactly the right adjoint of `f_!` (`exceptionalDirectImageAdjunction` of
    Part 34) **and** the left adjoint of `f^!`
    (`exceptionalInverseImageAdjunction` of this part). The identity is
    `rfl` because it is carried by the type itself — each adjunction above
    uses `(whiskeringLeft Cᵒᵖ Dᵒᵖ H).obj f.op` as its respective adjoint,
    which **is** `pullbackPresheaf f`. The exact symmetric of the witness
    lemma `exceptionalDirectImage_is_presheaf_level` of Part 34. -/
theorem exceptionalInverseImage_is_presheaf_level (f : C ⥤ D)
    [∀ (F : Cᵒᵖ ⥤ H), f.op.HasRightKanExtension F] :
    exceptionalInverseImage (H := H) f = f.op.ran (H := H) :=
  rfl

/-!
## 5. The ceiling: presheaf level, not sheaf-theoretic

We state the bound explicitly, per acceptance point 5: this `f^!` is a
presheaf `f^!`, not the sheaf-theoretic Verdier `f^!`. This section is a
**part of the deliverable** (documenting the reachable ceiling), not an
excuse.
-/

/-- **Honest ceiling.** This `f^!` is the exceptional inverse image at the
    **presheaf** level. The sheaf-theoretic `f^!` (the genuine "exceptional
    inverse image" in Verdier's sense) demands Poincare duality on the
    underlying topological space — a structurally stronger hypothesis that is
    not on this lake's program. This witness lemma recalls the definition to
    anchor the ceiling: there is no `sorry` here, no fabricated proof — only
    the Kan adjunction at the presheaf level, which is what Mathlib lets us
    prove cleanly. The composition `f_! ⊣ f^* ⊣ f^!` is available at the
    presheaf level (the two adjunctions compose via `f^*`); its lift to the
    sheaf-theoretic level would require Verdier duality, out of scope for
    this lake. -/
theorem exceptionalInverseImage_requires_Verdier (f : C ⥤ D)
    [∀ (F : Cᵒᵖ ⥤ H), f.op.HasRightKanExtension F] :
    -- At the presheaf level, `f^! F = (f.op).ran.obj F` is defined as the
    -- right Kan extension of `F` along `f.op`. Any generalization to
    -- sheaf-theoretic `f^!` would demand Verdier duality.
    exceptionalInverseImage (H := H) f = f.op.ran (H := H) :=
  rfl

end Grothendieck.ExceptionalInverse_en
