/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted to `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, i18n convention #4980.

The original Dahia source lives in the `gdahia/Komlos` repository: `Komlos/Transport.lean`
(l.54-64 — `tvDist_push` and `shiftDist_push`). Both statements are written there over
`Finsupp` (`E →₀ ℝ`), where the shift distance lives on the **canonical** support. k2.3
had deferred them with a measured reason: this lake's convention (k1.1) passes the
`Finset` support **explicitly**, and the transported statement seemed to require a
re-indexation of `S ∪ (S + u)` — a `Finset` union whose sum is not the sum of the sums.

**This commit lifts the deferral, and the barrier dissolves instead of being crossed.**
k4.2b (`TvDistance.lean`) delivered `tvDistance`, generic in its index type, together
with the bridge `shiftDistance_eq_tvDistance` : a shift *is* a total variation, the one
of a weight against its translate. In that form the shift is carried by the
**function** (`x ↦ P (x + u)`), not by the summation set: a single `Finset` suffices on
both sides, and the union `S ∪ (S + u)` never appears. The required re-indexation is the
one already delivered by `sum_push` (k2.3).

**Scope of this commit** (brick k4.2c, `lake build SUCCESS` required, 0 `sorry`) :

Closed bricks: `shiftDistanceTV` (the shift distance in total-variation form — the form
that transports), `tvDistance_push` (the oracle's `tvDist_push`, l.54-55),
`shiftDistanceTV_push` (the oracle's `shiftDist_push`, l.63-64 — **the last k2.3
deferral**), `shiftDistance_eq_shiftDistanceTV` (the bridge to k1.1's `shiftDistance`)
and `shiftDistanceTV_push_toReal` (the lake's transport instance, `toReal`).

**Deferred, with a measured reason**: `IsDist.push` (l.44-49) — it awaits the `IsDist`
vocabulary ("is a distribution"), which this lake does not have (k1.1 framing decision:
plain functions, explicit support). It is not transport to be restated, it is a
vocabulary to be paid for with its consumer; k4.3 will pay it if it demands it, as
k4.2c pays its own here.

**Consumed by**: brick k4.3 (`NearInvariant.lean`, Lemma 1.5), whose
`exists_nearInvariant` reads `shiftDist_push` on `gridEmb d N` in its third goal.
-/

import Discrepancy.Komlos.TvDistance_en
import Discrepancy.Komlos.Transport_en

/-!
# Transported shift distance (brick k4.2c)

`shiftDistanceTV s P u = tvDistance s (fun x ↦ P (x + u)) P` : the shift distance
written as **a total variation between a weight and its translate** — the form under
which it transports along an injective additive embedding.

Two forms of the same quantity now coexist in the lake: `shiftDistance` (k1.1), posed on
the integer grid `Fin d → ℤ`, and `shiftDistanceTV`, generic in any **additive** index
type — hence available on the real grid `Fin d → ℝ`, where `Fin d → ℤ` is not an
`ℝ`-module. The bridge `shiftDistance_eq_shiftDistanceTV` identifies them on the integer
grid.

The carrying result is `shiftDistanceTV_push`: **pushing a weight along an injective
additive map does not change its shift distance**, the shift becoming the image of the
source shift. This is the statement k4.3 (Lemma 1.5) needs in order to read the
`Komlos.Cube` bound on the real grid: the weight `cubeF` is pushed there by
`gridEmb d N` (`g ↦ g / N`), and `shiftDistanceTV_push` transports the distance without
recomputing it.
-/

namespace Discrepancy.Komlos_en

open Finset

variable {ι : Type*} [Add ι]

/-- **Shift distance in total-variation form**:
`shiftDistanceTV s P u = tvDistance s (fun x ↦ P (x + u)) P`.

This is k1.1's shift distance in the form the transport reads: the shift is carried by
the **function** (`x ↦ P (x + u)`), and a single `Finset` `s` carries both weights —
where the "translate the summation set" reading would require a union `S ∪ (S + u)`.

Generic in any additive index type `ι`: this is what makes it available on the real grid
`Fin d → ℝ` (k4.3), where k1.1's `shiftDistance` is posed on the integer grid
`Fin d → ℤ`. -/
noncomputable def shiftDistanceTV (s : Finset ι) (P : ι → ℝ) (u : ι) : ℝ :=
  tvDistance s (fun x ↦ P (x + u)) P

/-- **The bridge to k1.1's shift distance**: on the integer grid, the two forms are the
same quantity — it is k4.2b's bridge `shiftDistance_eq_tvDistance`, read back in this
module's vocabulary.

It makes the carrying result applicable to k1.1's `shiftDistance` without restating it:
`shiftDistance S P u = shiftDistanceTV S P u`. -/
lemma shiftDistance_eq_shiftDistanceTV {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ) :
    shiftDistance S P u = shiftDistanceTV S P u := by
  unfold shiftDistanceTV
  exact shiftDistance_eq_tvDistance S P u

/-- **Total variation is preserved by the push** (in the oracle: `tvDist_push`,
`Komlos/Transport.lean` l.54-55).

Pushing two weights along the same injective additive map and summing over the image of
the support is summing over the source support: the re-indexation is `sum_push` (k2.3),
and on the image the push reads the source back (`push_apply`). The `Finset` form makes
the statement **unconditional** — no support hypothesis to carry, the summation set is a
parameter. -/
lemma tvDistance_push {d : ℕ} (e : (Fin d → ℤ) →+ (Fin d → ℝ))
    (he : Function.Injective e) (S : Finset (Fin d → ℤ))
    (P Q : (Fin d → ℤ) → ℝ) :
    tvDistance (S.map ⟨⇑e, he⟩) (push e P) (push e Q) = tvDistance S P Q := by
  unfold tvDistance
  congr 1
  rw [sum_push e he S (fun y ↦ |push e P y - push e Q y|)]
  exact sum_congr rfl fun x _ ↦ by rw [push_apply e he P x, push_apply e he Q x]

/-- **The shift distance is preserved by the push** — the oracle's `shiftDist_push`
(`Komlos/Transport.lean` l.63-64), **the last k2.3 deferral**.

Pushing a weight along an injective additive map `e` transports its shift distance: the
one of the pushed weight under the image shift `e u` is the one of the source weight
under `u`. The proof is the re-indexation `sum_push` (k2.3) — the shift does not have to
be transported separately, because it is **already** carried by the function
(`shiftDistanceTV`) and `e` is additive: `e x + e u = e (x + u)`. The union
`S ∪ (S + u)` that k2.3 dreaded appears nowhere. -/
lemma shiftDistanceTV_push {d : ℕ} (e : (Fin d → ℤ) →+ (Fin d → ℝ))
    (he : Function.Injective e) (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ) :
    shiftDistanceTV (S.map ⟨⇑e, he⟩) (push e P) (e u) = shiftDistanceTV S P u := by
  unfold shiftDistanceTV tvDistance
  congr 1
  rw [sum_push e he S (fun y ↦ |push e P (y + e u) - push e P y|)]
  exact sum_congr rfl fun x _ ↦ by
    rw [← map_add, push_apply e he P (x + u), push_apply e he P x]

/-- **The lake's transport instance**: the shift transports along `toReal`, k2.3's
coordinatewise embedding — the injective additive map on which the whole dimension
transport is built.

This is the case k4.3 instantiates, its `gridEmb d N` (`g ↦ g / N`) being a scaling
composed with `toReal`: the shift distance of `push toReal P` under `toReal u` is the
one of `P` under `u`. -/
lemma shiftDistanceTV_push_toReal {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ) :
    shiftDistanceTV (S.map ⟨⇑toReal, toReal_injective⟩) (push toReal P) (toReal u)
      = shiftDistanceTV S P u :=
  shiftDistanceTV_push toReal toReal_injective S P u

/-! ## Adaptation note (brick k4.2c)

**Status**: 5 bricks closed — the oracle's `tvDist_push` / `shiftDist_push`
(`Komlos/Transport.lean` l.54-64) is carried into the lake's `Finset` convention, and
the **last k2.3 deferral** is settled. Brick k4.3 (Lemma 1.5) no longer awaits any
deferred statement.

**What changed relative to the oracle**: there the push is a `Finsupp.embDomain`, which
transports the support **together with** the weight, and its `shiftDist` sums over that
canonical support — the statement then proves by rewriting
(`rw [shiftDist, tr_push, tvDist_push, shiftDist]`). In the lake, the support is a
parameter: the push transports the summation **set** (`S.map ⟨e, he⟩`), and the shift
stays inside the function. The two statements therefore bear on different objects — but
say the same thing, and it is the second that composes with `convexHull ℝ` (k2.4) and
with the `Komlos.Cube` bound (k4.2).

**What the transport does not do**: it does not change the distance, it **re-reads** it
on the target. `shiftDistanceTV_push` is an equality, not an inequality — there is no
loss in transporting, and k4.3 can therefore read the bound `shiftDistance_cubeF_sq_le`
(k4.2, over `Fin d → ℤ`) on the real grid without re-proving anything.

**Verification**: `lake build Discrepancy.Komlos.ShiftPush` (module + twin),
0 `sorry`, `distinct_code_sorry = 0` on the lake. -/

end Discrepancy.Komlos_en