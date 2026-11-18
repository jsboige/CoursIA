/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted to `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, i18n convention #4980.

The original Dahia source lives in the repository `gdahia/Komlos` (module
`Komlos/Transport.lean`, toolchain v4.34.0, `Finsupp` framework over `E →₀ ℝ`).
The adaptation takes the module over **name for name** in the lake's explicit
Finset framework (k1.1 convention) — see the scope below.

**Scope of this commit** (brick k2.3, `lake build SUCCESS` required, 0 `sorry`) :

Brick k2.2 **measured** the blocker of `pullback` : the oracle states it over
`E →₀ ℝ` with `E` an `ℝ`-module, the hull being taken in
`convexHull ℝ (P.support : Set E)` ; this lake's base is `Fin d → ℤ`, which is
**not** an `ℝ`-module. This brick delivers the **dimension transport** that
lifts the blocker : the coordinate-by-coordinate embedding
`toReal : (Fin d → ℤ) →+ (Fin d → ℝ)`, its pushforward `push`, and the **two
bridges** the k2.4 convexity conclusion reads on the transported support —
membership (`toReal_mem_map_iff`) and the barycenter (`coordMoment_toReal`).

Transposed from `Komlos/Transport.lean` (l.27-67) :

- `toReal` + `toReal_injective` — the lake's instance of the transport
  (`g ↦ g` coordinate-by-coordinate, the oracle's `g ↦ g / N` being a further
  homothety) ;
- `push e P` — the pushforward along any additive morphism `e` between the
  two grids, on `Function.extend` (Mathlib's organ for extending along an
  injection — the exact counterpart of the oracle's `Finsupp.embDomain` ;
  injectivity is only required by the lemmas) ;
- `push_apply`, `push_eq_zero` — the two computation identities (l.32 and
  the off-image case) ;
- `sum_push` — the reindexing (l.35-36), in the lake's `Finset` form ;
- `push_mass` — mass is preserved (l.41-42, `mass_push`) ;
- `coordMomentReal_push` then `coordMoment_toReal` — the transported
  barycenter (l.66-67, `mean_push`) : on the real grid, the pushed
  coordinate moment of `toReal` **is** the lake's `coordMoment` (k2.0) ;
- `toReal_mem_map_iff`, `toReal_mem_coe_iff` — the membership bridge that
  `convexHull ℝ ↑(S.map …)` will consume in k2.4.

**Deferred, with measured reason** :

1. `shiftDist_push` (l.63-64) — the transported shift distance. In the
   oracle, `shiftDist` lives on the **canonical** Finsupp support ; the
   lake's convention (k1.1) passes the support `Finset` **explicitly**, and
   the transported statement requires reindexing `S ∪ (S + u)` on the
   target side — a union of `Finset`s whose sum is not the sum of sums.
   No k2.4 consumer reads it : the convexity conclusion reads only the
   support and the barycenter, both delivered above.
2. `tvDist_push`, `IsDist.push` (l.44-55) — the vocabulary `tvDist`/`IsDist`
   does not exist in this lake (k1.1 framing decision : plain functions,
   explicit support). Restating them here would be **new vocabulary**, not
   transport ; if k4 needs them, they will come with their framework.

The detailed state lives in `FORMAL_STATUS.md`.
-/

import Discrepancy.Komlos.MeanSplit_en

/-!
# Dimension transport (brick k2.3, Karingula–Lovett)

`Fin d → ℤ` is not an `ℝ`-module : that is the blocker k2.2 measured for
`pullback`. This module lifts it by embedding the whole grid into
`Fin d → ℝ` — where `convexHull ℝ` makes sense — through `toReal`, and by
delivering the two bridges the Lemma 1.4 conclusion reads on the image :
membership in the transported support, and preservation of the
coordinate-by-coordinate barycenter.

**Why a separate module.** The transport is the piece that **changes
category** (from ℤ to ℝ) : isolating it makes every future build failure
attributable — the pullback algebra (k2.1), the convexity (k2.2) and the
transport (k2.3) each live in their module, and the full step (k2.4) will
consume them by name.

**Genericity.** As in the oracle, the pushforward `push` is delivered for
any **injective** additive morphism between the two grids — `toReal` is but
one instance. The paper also transports through the homothety `g ↦ g / N`
(`N > 0`) : composed with `toReal`, it enters the same genericity.
-/

namespace Discrepancy.Komlos_en

/-- **Dimension transport** : the coordinate-by-coordinate embedding of the
integer grid into the real grid, `(x i : ℤ) ↦ ((x i : ℤ) : ℝ)`.

This is the morphism lifting the blocker measured in k2.2 : `Fin d → ℤ` is
not an `ℝ`-module, `Fin d → ℝ` is — it is there that `convexHull ℝ` (k2.2)
becomes statable on the transported support. Additive by coordinate
additivity of the `ℤ → ℝ` cast ; injective because the cast is. -/
def toReal {d : ℕ} : (Fin d → ℤ) →+ (Fin d → ℝ) where
  toFun x := fun i => (x i : ℝ)
  map_zero' := by funext i; simp
  map_add' := by intro x y; funext i; simp

/-- Coordinate reading of the transport : `toReal x i = ((x i : ℤ) : ℝ)`. -/
@[simp] lemma toReal_apply {d : ℕ} (x : Fin d → ℤ) (i : Fin d) :
    toReal x i = (x i : ℝ) := rfl

/-- The transport is **injective** : the `ℤ → ℝ` cast is, coordinate by
coordinate. This is what makes `toReal` an embedding and enables the
`sum_push` reindexing on the image. -/
lemma toReal_injective {d : ℕ} : Function.Injective (toReal (d := d)) := by
  intro x y h
  funext i
  exact Int.cast_injective (congrFun h i)

/-- **Pushforward of a distribution along an additive morphism** :
`push e P (e x) = P x` (under injectivity, cf `push_apply`) and
`push e P y = 0` off the image of `e` (cf `push_eq_zero`).

This is the oracle's `Finsupp.embDomain` (`Komlos/Transport.lean` l.27-28),
transposed to the lake's plain functions : Mathlib's organ for extending
along an injection is `Function.extend`, whose off-image default is here the
zero function. Generic in `e` (any additive morphism between the two grids
— injectivity is only required by the **lemmas**, `Function.extend` being
well-defined without) ; `toReal` is the lake's instance. -/
noncomputable def push {d : ℕ} (e : (Fin d → ℤ) →+ (Fin d → ℝ))
    (P : (Fin d → ℤ) → ℝ) :
    (Fin d → ℝ) → ℝ :=
  Function.extend ⇑e P 0

/-- On the image, the pushforward reads the source distribution :
`push e P (e x) = P x` — under injectivity of `e`, failing which two
antecedents would share an image. (In the oracle : `push_apply`, l.32.) -/
@[simp] lemma push_apply {d : ℕ} (e : (Fin d → ℤ) →+ (Fin d → ℝ))
    (he : Function.Injective e) (P : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) :
    push e P (e x) = P x :=
  Function.Injective.extend_apply he P 0 x

/-- Off the morphism's image, the pushforward is zero : real-grid points
with no integer antecedent carry no mass. -/
lemma push_eq_zero {d : ℕ} (e : (Fin d → ℤ) →+ (Fin d → ℝ))
    (P : (Fin d → ℤ) → ℝ) {y : Fin d → ℝ}
    (hy : ∀ x, e x ≠ y) : push e P y = 0 := by
  have hb : ¬∃ a, ⇑e a = y := by
    rintro ⟨a, rfl⟩
    exact hy a rfl
  exact Function.extend_apply' P (0 : (Fin d → ℝ) → ℝ) y hb

/-- **Pushforward reindexing** : summing over the transported support is
summing over the source support. (In the oracle : `sum_push`, l.35-36, in
the lake's `Finset` form — the content is the reindexing by the embedding.) -/
lemma sum_push {d : ℕ} {β : Type*} [AddCommMonoid β]
    (e : (Fin d → ℤ) →+ (Fin d → ℝ)) (he : Function.Injective e)
    (S : Finset (Fin d → ℤ)) (f : (Fin d → ℝ) → β) :
    ∑ y ∈ S.map ⟨⇑e, he⟩, f y = ∑ x ∈ S, f (e x) :=
  Finset.sum_map S ⟨⇑e, he⟩ f

/-- **Mass is preserved by the pushforward** : the order-0 moment
transports without loss. (In the oracle : `mass_push`, l.41-42.) -/
lemma push_mass {d : ℕ} (e : (Fin d → ℤ) →+ (Fin d → ℝ))
    (he : Function.Injective e) (P : (Fin d → ℤ) → ℝ) (S : Finset (Fin d → ℤ)) :
    ∑ y ∈ S.map ⟨⇑e, he⟩, push e P y = ∑ x ∈ S, P x := by
  rw [sum_push]
  exact Finset.sum_congr rfl fun x _ => push_apply e he P x

/-- **Coordinate moment on the real grid** : the barycenter of a
distribution on `Fin d → ℝ`, read coordinate by coordinate. This is the
exact counterpart of `coordMoment` (k2.0) for the target grid — the
coordinates there are already real, the cast is the identity. -/
noncomputable def coordMomentReal {d : ℕ} (Q : (Fin d → ℝ) → ℝ)
    (T : Finset (Fin d → ℝ)) (i : Fin d) : ℝ :=
  ∑ y ∈ T, Q y * y i

/-- **Generic form of the transported barycenter** : the coordinate moment
of the pushforward, on the transported support, reads on the source
coordinate by coordinate — each pushed into `ℝ` by `e`. (In the oracle :
`mean_push`, l.66-67, the scalarization `r • e x` becoming the lake's
coordinate reading.) -/
lemma coordMomentReal_push {d : ℕ} (e : (Fin d → ℤ) →+ (Fin d → ℝ))
    (he : Function.Injective e) (P : (Fin d → ℤ) → ℝ) (S : Finset (Fin d → ℤ))
    (i : Fin d) :
    coordMomentReal (push e P) (S.map ⟨⇑e, he⟩) i = ∑ x ∈ S, P x * e x i := by
  rw [coordMomentReal, sum_push]
  exact Finset.sum_congr rfl fun x _ => by rw [push_apply e he P x]

/-- **The barycenter bridge** : for the lake's transport (`e = toReal`), the
coordinate moment of the pushforward on the transported support **is** the
lake's `coordMoment` (k2.0). This is the piece the k2.4 convexity conclusion
will read : the barycenter asserted to lie in the hull is exactly the one
the k2.0 moments compute. -/
lemma coordMoment_toReal {d : ℕ} (P : (Fin d → ℤ) → ℝ) (S : Finset (Fin d → ℤ))
    (i : Fin d) :
    coordMomentReal (push toReal P)
        (S.map ⟨⇑toReal, toReal_injective⟩) i = coordMoment P S i := by
  rw [coordMomentReal_push, coordMoment]
  exact Finset.sum_congr rfl fun x _ => by rw [toReal_apply]

/-- **Membership bridge (`Finset` form)** : `toReal x` belongs to the
transported support exactly when `x` belongs to the source support —
injectivity forbids two integer points from sharing an image. -/
lemma toReal_mem_map_iff {d : ℕ} (x : Fin d → ℤ) (S : Finset (Fin d → ℤ)) :
    toReal x ∈ (S.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ)) ↔ x ∈ S := by
  rw [Finset.mem_map]
  constructor
  · rintro ⟨x', hx', hxx'⟩
    have hxe : x' = x := toReal_injective hxx'
    rw [hxe] at hx'
    exact hx'
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- **Membership bridge (`Set` form)** : the same reading at the set level —
the form `convexHull ℝ (↑(S.map …) : Set (Fin d → ℝ))` will consume in k2.4. -/
lemma toReal_mem_coe_iff {d : ℕ} (x : Fin d → ℤ) (S : Finset (Fin d → ℤ)) :
    toReal x ∈ (↑(S.map ⟨⇑toReal, toReal_injective⟩) : Set (Fin d → ℝ)) ↔ x ∈ S := by
  rw [Finset.mem_coe]
  exact toReal_mem_map_iff x S

end Discrepancy.Komlos_en
