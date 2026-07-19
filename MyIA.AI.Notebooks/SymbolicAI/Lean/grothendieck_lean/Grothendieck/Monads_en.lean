/-
Grothendieck Part 26 — Monads and monadic adjunctions (English mirror of Monads.lean)

Alexander Grothendieck (1928-2014).

Extension Phase 2+ (#2159, Epic #1646).

Every adjunction L ⊣ R (Part 25) generates a monad T = R ⋙ L on the base
category C. Conversely, every monad T arises from an adjunction (two
canonical factorisations: Eilenberg-Moore via algebras, Kleisli via free
coextensions). Grothendieck uses this correspondence in topos theory (a
topos is the category of sheaves, which is monadic over the category of
presheaves via sheafification ⊣ inclusion) and in descent (morphisms of
effective descent are characterised by a monadic property of the fibre
functor).

A monad on C is an endofunctor T : C ⥤ C equipped with a unit
η : 𝟭 C ⟶ T and a multiplication μ : T ⋙ T ⟶ T satisfying the unit and
associativity identities. It is "a monoid in the category of endofunctors"
(Godement's formulation, who introduced them in 1958 under the name
"standard constructions").

Mathlib 4 formalises all of this infrastructure in
`Mathlib.CategoryTheory.Monad`:
  - `CategoryTheory.Monad : Type*` — the T = (T, η, μ) structure
  - `CategoryTheory.Adjunction.toMonad : (L ⊣ R) → Monad C` — the induced monad
  - `CategoryTheory.Adjunction.adjToMonadIso` — every monad arises from an adjunction (up to iso)
  - `CategoryTheory.Monad.Algebra` — the Eilenberg-Moore category of algebras
  - `CategoryTheory.Monad.forget` / `CategoryTheory.Monad.free` — forget ⊣ free
  - `CategoryTheory.Kleisli` — the Kleisli category
  - `CategoryTheory.Monad.comparison` — the Eilenberg-Moore comparison functor
  - `CategoryTheory.MonadicRightAdjoint` — monadic functor (Beck's theorem)

This module re-exposes these facts as an organised pedagogical tour for
learners encountering categorical monads for the first time.

Epic #1646, See #2159. No `sorry` at creation.

### i18n — convention #4980 ratified 2026-07-04

This module is the English mirror of `Monads.lean`. Theorem statements,
lemma names, Lean tactics and Mathlib references stay in English. Only the
**docstrings `/-- ... -/`** and **comments `-- ...`** differ between the two
files. Anti-§D byte-identity guaranteed.
-/

import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monad.Algebra
import Mathlib.CategoryTheory.Monad.Kleisli

universe v₁ u₁

namespace Grothendieck.Monads_en

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

/-!
## 1. The monad structure

A monad on C is an endofunctor `T : C ⥤ C` equipped with the unit
`η : 𝟭 C ⟶ T` and the multiplication `μ : T ⋙ T ⟶ T` satisfying the three
axioms (left unit, right unit, associativity). It is a monoid in the
monoidal category of endofunctors.
-/

-- The monad structure (T, η, μ) on a category. Fully qualified since `Monad`
-- is also a Lean core typeclass.
#check @CategoryTheory.Monad

-- The unit η : 𝟭 C ⟶ T of a monad (field `η`).
#check @CategoryTheory.Monad.η

-- The multiplication μ : T ⋙ T ⟶ T of a monad (field `μ`).
#check @CategoryTheory.Monad.μ

/-!
## 2. Every adjunction generates a monad

The founding theorem: an adjunction `L ⊣ R` (Part 25) induces a monad
`R ⋙ L` on C. Conversely, every monad arises from an adjunction — the
correspondence is essential (up to isomorphism), closing the
adjunction ↔ monad bridge.
-/

-- The monad R ⋙ L induced by an adjunction L ⊣ R (here on a single
-- category C via the Kleisli / Eilenberg-Moore category).
#check @CategoryTheory.Adjunction.toMonad

-- Converse: every monad T arises from its free ⊣ forget adjunction, and
-- `T.adj.toMonad ≅ T`.
#check @CategoryTheory.Adjunction.adjToMonadIso

/-!
## 3. The Eilenberg-Moore category (algebras)

The category of algebras of a monad T is the "universal solution" to the
problem of factoring T through an adjunction. A T-algebra is an object A
equipped with an action `a : T A ⟶ A` compatible with η (unit) and μ
(associativity). The forgetful functor forgets the action; its left adjoint
builds the free algebra.
-/

-- The T-algebra structure (underlying object A + action a : T A ⟶ A).
#check @CategoryTheory.Monad.Algebra

-- The Eilenberg-Moore category of T-algebras (category instance),
-- exhibited as a `Category` instance for any monad T.
#check fun (T : CategoryTheory.Monad C) ↦ (inferInstance : Category (T.Algebra))

-- The forgetful functor Algebra T ⥤ C (forgets the monad action).
#check @CategoryTheory.Monad.forget

-- The free algebra functor C ⥤ Algebra T (left adjoint of forget).
#check @CategoryTheory.Monad.free

/-!
## 4. The free ⊣ forget adjunction (Eilenberg-Moore)

The free algebra functor `free` and the forgetful functor `forget` form an
adjunction `free ⊣ forget` whose induced monad is exactly T — this is the
canonical Eilenberg-Moore factorisation.
-/

-- The free ⊣ forget adjunction for Eilenberg-Moore algebras.
#check @CategoryTheory.Monad.adj

/-!
## 5. The Kleisli category

Symmetric to Eilenberg-Moore: the Kleisli category is the other universal
solution (morphisms A ⟶ B in Kleisli T are arrows A ⟶ T B in C). The
Kleisli and Eilenberg-Moore adjunctions are the two extremal factorisations
of the monad T (Kleisli = initial, Eilenberg-Moore = terminal among the
adjunctions that generate T).
-/

-- The Kleisli category of the monad T (under `CategoryTheory`, not `Monad`).
#check @CategoryTheory.Kleisli

/-!
## 6. Bridge theorems

Reformulations in the project namespace, bridging the Mathlib facts.
-/

/-- Bridge: the monad induced by an adjunction L ⊣ R, viewed as an
    endofunctor of C. This is the object part of the monad (without its η, μ
    structure), i.e. the composite R ⋙ L viewed functorially. -/
def toMonad_underlying {D : Type u₁} [Category.{v₁} D] {L : C ⥤ D} {R : D ⥤ C}
    (h : L ⊣ R) : C ⥤ C :=
  (h : CategoryTheory.Adjunction L R).toMonad

/-- Bridge: the Eilenberg-Moore forgetful functor, from the category of
    algebras to the base category. This is the "right" forgetful functor whose
    monadicity (Beck's theorem) detects categories of algebraic structures
    (groups, rings, sheaves). -/
def forget_family (T : CategoryTheory.Monad C) :
    CategoryTheory.Monad.Algebra T ⥤ C :=
  T.forget

/-- Bridge: the free algebra functor, left adjoint of the forgetful functor.
    It embodies the "free" construction (free group, free ring, free sheaf)
    central to algebra and algebraic geometry. -/
def free_family (T : CategoryTheory.Monad C) :
    C ⥤ CategoryTheory.Monad.Algebra T :=
  T.free

end Grothendieck.Monads_en
