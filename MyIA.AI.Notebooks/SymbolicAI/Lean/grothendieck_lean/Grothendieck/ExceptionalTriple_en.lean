/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Part 35 — `Grothendieck.ExceptionalTriple_en`: the adjoint triple `f_! ⊣ f^* ⊣ f_*`
## and the collapse of the exceptional inverse image at the presheaf level

Alexander Grothendieck (1928-2014).

Phase 2+ extension (#2159, Epic #1646). Part 34 (`ExceptionalDirect.lean`)
delivered `f_!` at the presheaf level (left Kan extension along `f.op`) and its
adjunction `f_! ⊣ f^*`. This part completes the picture by assembling the
**adjoint triple** `f_! ⊣ f^* ⊣ f_*`: the third leg `f^* ⊣ f_*` is the ordinary
direct image (right Kan extension along `f.op`), and it is their nesting into a
**triple** that constitutes the substance here.

### What the presheaf level offers as non-degenerate

Neither adjunction taken in isolation is new: `f_! ⊣ f^*` is Part 34, and
`f^* ⊣ f_*` is but a re-instantiation of `Functor.ranAdjunction` (Mathlib).
What is **not** copied Mathlib is the **triple** and the properties that exist
only because there is one:

  - **`presheafSixOpsTriple`**: the nesting `f_! ⊣ f^* ⊣ f_*` as a
    `CategoryTheory.Adjunction.Triple`.
  - **The coherence**: `f_!` is fully faithful **if and only if** `f_*` is
    (`Adjunction.Triple.fullyFaithfulEquiv`). This is a statement about `f_!`
    proved *via* `f_*` — out of reach of Part 34 alone.
  - **`exceptionalInverse_collapses_to_pullback`**: for every `G` with
    `f_! ⊣ G`, we have `G ≅ f^*` (`rightAdjointUniq`). This is the honest
    ceiling: at the presheaf level there is **no** exceptional inverse image
    `f^!` distinct from `f^*`.

### The ceiling (honest, per acceptance point 5)

This triple lives at the **presheaf** level. The sheaf-theoretic proper-support
`f_!` of the six operations requires sheafification and a properness hypothesis
on `f`; its right adjoint `f^!` requires **Verdier duality**. The collapse
`G ≅ f^*` above makes this impossibility **provable** in Lean, not merely
asserted in prose — exactly the bound Part 34 announced.

Epic #1646, See #2159. All `sorry` eliminated at creation.

### i18n — convention #4980 ratified 2026-07-04

This module is the English canonical sibling of `ExceptionalTriple.lean`
(**consumer-twin** model: the `_en` imports the FR module
`Grothendieck.ExceptionalDirect` and does not re-declare its definitions —
cf `CoversLattice_en.lean`). Theorem/lemma statements, lemma names, Lean
tactics and Mathlib references remain in English (Mathlib 4, standard tactic
DSL); the namespace carries the `_en` suffix. Only the **docstrings `/-- ... -/`**
and **comments `-- ...`** differ between the two files. Anti-§D byte-identity
guaranteed on signatures, proofs and tactics (verifiable by diff).
-/

import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Whiskering
import Grothendieck.ExceptionalDirect

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Grothendieck.ExceptionalTriple_en

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H]

/-!
## 1. `f_*` at the presheaf level: right Kan extension along `f.op`

The third leg of the triple. The ordinary direct image `f_*` extends a presheaf
`F : Cᵒᵖ ⥤ H` to `f_* F : Dᵒᵖ ⥤ H` as the best right extension of `F` — the
right Kan extension `(f.op).ran`. It is **right adjoint** to the pullback
`f^*`: this is the presheaf analogue of the fundamental adjunction
`f^* ⊣ f_*` on sheaves of modules, instantiated here by `Functor.ranAdjunction`.
-/

/-- **`f_*` at the presheaf level.** The direct image of a presheaf
    `F : Cᵒᵖ ⥤ H` along `f : C ⥤ D`, defined as the right Kan extension along
    `f.op : Cᵒᵖ ⥤ Dᵒᵖ`. This is a covariant functor `(Cᵒᵖ ⥤ H) ⥤ (Dᵒᵖ ⥤ H)`.
    The hypothesis `[∀ G, f.op.HasRightKanExtension G]` guarantees pointwise
    existence of the extensions. -/
noncomputable def directImagePresheaf (f : C ⥤ D)
    [∀ (G : Cᵒᵖ ⥤ H), f.op.HasRightKanExtension G] : (Cᵒᵖ ⥤ H) ⥤ (Dᵒᵖ ⥤ H) :=
  f.op.ran

/-- **The adjunction `f^* ⊣ f_*` at the presheaf level.** Proved by instantiating
    Mathlib's `Functor.ranAdjunction` (`f.op.ranAdjunction H`), which formally
    establishes `(whiskeringLeft Cᵒᵖ Dᵒᵖ H).obj f.op ⊣ (f.op).ran` — that is,
    exactly `f^* ⊣ f_*`. -/
noncomputable def directImagePresheafAdjunction (f : C ⥤ D)
    [∀ (G : Cᵒᵖ ⥤ H), f.op.HasRightKanExtension G] :
    ExceptionalDirect.pullbackPresheaf (H := H) f ⊣ directImagePresheaf (H := H) f :=
  f.op.ranAdjunction H

/-!
## 2. The triple `f_! ⊣ f^* ⊣ f_*`

The nesting of the two adjunctions into an **adjoint triple**. Part 34 supplies
`adj₁ : f_! ⊣ f^*`; this part supplies `adj₂ : f^* ⊣ f_*`. Their union is the
triple `f_! ⊣ f^* ⊣ f_*`, the brick of the six operations (at the presheaf
level).
-/

/-- **The adjoint triple `f_! ⊣ f^* ⊣ f_*` at the presheaf level.** Assembles
    the Part 34 adjunction (`exceptionalDirectImageAdjunction`, `adj₁`) with the
    `f^* ⊣ f_*` adjunction of section 1 (`directImagePresheafAdjunction`,
    `adj₂`) into a `CategoryTheory.Adjunction.Triple`. -/
noncomputable def presheafSixOpsTriple (f : C ⥤ D)
    [∀ (F : Cᵒᵖ ⥤ H), f.op.HasLeftKanExtension F]
    [∀ (G : Cᵒᵖ ⥤ H), f.op.HasRightKanExtension G] :
    CategoryTheory.Adjunction.Triple
      (ExceptionalDirect.exceptionalDirectImage (H := H) f)
      (ExceptionalDirect.pullbackPresheaf (H := H) f) (directImagePresheaf (H := H) f) where
  adj₁ := ExceptionalDirect.exceptionalDirectImageAdjunction (H := H) f
  adj₂ := directImagePresheafAdjunction (H := H) f

/-!
## 3. Coherence: `f_!` and `f_*` are simultaneously fully faithful

A statement that **neither half gives**: `f_!` is fully faithful **if and only
if** `f_*` is. It is proved *via* `Adjunction.Triple.fullyFaithfulEquiv`, which
relates the two ends of the triple.
-/

/-- **`f_!` fully faithful iff `f_*` fully faithful.** Coherence statement of
    the triple, proved by `presheafSixOpsTriple.fullyFaithfulEquiv`
    (`Adjunction.Triple.fullyFaithfulEquiv`). This is the only property of the
    triple that is not copied from one half: a statement about `f_!` proved
    *via* `f_*`. -/
noncomputable def exceptionalDirectImage_fullyFaithful_iff_directImage (f : C ⥤ D)
    [∀ (F : Cᵒᵖ ⥤ H), f.op.HasLeftKanExtension F]
    [∀ (G : Cᵒᵖ ⥤ H), f.op.HasRightKanExtension G] :
    (ExceptionalDirect.exceptionalDirectImage (H := H) f).FullyFaithful ≃
      (directImagePresheaf (H := H) f).FullyFaithful :=
  (presheafSixOpsTriple (H := H) f).fullyFaithfulEquiv

/-!
## 4. The ceiling: the exceptional inverse image collapses onto `f^*`

This is the methodological result. At the presheaf level, there is **no** `f^!`
distinct from `f^*`: if a functor `G` is right adjoint to `f_!`, then
`G ≅ f^*`. The proof uses `rightAdjointUniq` (uniqueness of the right adjoint)
applied to the Part 34 adjunction (and to the given adjunction `adj`). This fact
durably documents why the lake will only have a `f^!` with Verdier duality.
-/

/-- **The exceptional inverse image collapses onto `f^*`.** For every
    `G : (Dᵒᵖ ⥤ H) ⥤ (Cᵒᵖ ⥤ H)` with `f_! ⊣ G`, we have `G ≅ f^*`. This is
    the uniqueness of the right adjoint (`rightAdjointUniq`) applied to
    `exceptionalDirectImageAdjunction` (Part 34) and to the given adjunction
    `adj`. Honest ceiling: at the presheaf level, `f^! = f^*`. -/
noncomputable def exceptionalInverse_collapses_to_pullback (f : C ⥤ D)
    [∀ (F : Cᵒᵖ ⥤ H), f.op.HasLeftKanExtension F]
    (G : (Dᵒᵖ ⥤ H) ⥤ (Cᵒᵖ ⥤ H))
    (adj : ExceptionalDirect.exceptionalDirectImage (H := H) f ⊣ G) :
    G ≅ ExceptionalDirect.pullbackPresheaf (H := H) f :=
  (CategoryTheory.Adjunction.rightAdjointUniq
    (ExceptionalDirect.exceptionalDirectImageAdjunction (H := H) f) adj).symm

end Grothendieck.ExceptionalTriple_en
