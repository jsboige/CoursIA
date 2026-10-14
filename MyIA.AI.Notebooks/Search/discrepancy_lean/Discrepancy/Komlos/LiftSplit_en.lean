/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted for `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979): toolchain v4.33.0, Mathlib `db584cd6`, i18n convention #4980.

The original Dahia source lives in the `gdahia/Komlos` repository (toolchain
v4.34.0, `Finsupp` framework over `E →₀ ℝ`). This module has **no
name-for-name oracle counterpart**: at the oracle, the induction hypothesis
applies to the split distribution in `E × ℝ` with no support precondition
whatsoever — the `Finsupp` transports its support for free
(`Finsupp.embDomain`); it is the lake's explicit `Finset` framework that
must pay for this transport, and that payment is precisely the subject of
this brick.

**Scope of this commit** (brick k2.6b, `lake build SUCCESS` required, 0
`sorry`) — the split under containment, read in the grown dimension
`Fin (d+1) → ℤ`:

- `pushUp_split_ne_zero` — reading the pushed support: any mass of
  `pushUp (split w P)` lives on the image of `liftUp` and originates
  from a mass of `P` at distance `± w` from its base (the auxiliary
  consumed by the containment transfer);
- `supportContained_pushUp_split` — **the containment transfer across
  the split**: if `S` contains the support of `P` and its translates by
  `A`, and `A` is stable under `± w`, then the lifted image
  `(S ×ˢ univ).map liftUpEmb` contains the support of `pushUp (split w P)`
  and its translates by the embedded shifts `Fin.snoc · 0` of `A`;
- `coordMoment_pushUp_split_of_support` — **conservation of the base
  moment under containment, at the lifted level**: the coordinate moment
  of the split-push, read on an inherited coordinate `i.castSucc`, is
  the moment of `P` at `i` — the composition of the bridge
  `coordMoment_pushUp_castSucc` (k2.6a) with `prodMoment_split_of_support`
  (k2.0);
- `coordMoment_pushUp_split_last` — the height component: the moment of
  the split-push on the last coordinate is the split bit
  (`coordMoment_pushUp_last` (k2.6a) × `heightMoment_split` (k2.0));
- `supportContained_pushUp_split_three` — the `{0, snoc u 0, −snoc u 0}`
  form consumed by the next induction step: an instance of the transfer
  by monotonicity (`SupportContained.mono`), the three shifts being the
  `snoc · 0` images of `0`, `u`, `−u`.

**Measured consumer**: the Lemma 1.4 induction (brick k2.6c, oracle
`Komlos/SignedSums.lean` l.44-55) applies its induction hypothesis to
`split (3 • v_last) P` in the grown space — on our side, to `pushUp
(split w P)` in `Fin (d+1) → ℤ`. The support preconditions and the
barycenter rewrites this call requires are exactly the five statements
above: containment to instantiate the hypothesis
(`supportContained_pushUp_split_three`), moments to rewrite the point it
produces (`coordMoment_pushUp_split_of_support` and `_last`, the lake
mirror of l.54's `rw [mean_split, …] at hmem`).

**Deferred**: the induction itself (`SignedSums.lean` name for name,
k2.6c). The detailed state lives in `FORMAL_STATUS.md`.
-/

import Discrepancy.Komlos.Containment_en
import Discrepancy.Komlos.Lift_en
import Discrepancy.Komlos.MeanSplit_en
import Discrepancy.Komlos.Split_en

/-!
# The split under containment, in the grown dimension (k2.6b)

At the oracle, the induction step of Lemma 1.4 is free on the support
side: `split v P` is a `Finsupp` over `E × ℝ`, whose support is
transported by `Finsupp.embDomain` with no precondition. In the lake's
explicit `Finset` framework, the same step must **prove** that the
support of the split-push `pushUp (split w P)` is contained — and will
remain so at the next induction step — in the lifted image of the
starting support.

This module pays that double cost in one brick: the **containment
transfer** (the split-pushed support obeys the containment transported
by `snoc · 0`) and the **conservation of moments under containment** at
the lifted level (the two components of `mean_split_of_support` k2.0
read through the k2.6a bridges).
-/

namespace Discrepancy.Komlos_en

/-- **Any mass of the split-push originates from a mass of `P` at
distance `± w`**: if `pushUp (split w P) z ≠ 0`, then `z` is on the
image of `liftUp` — `z = liftUp (x, b)` — and one of `P (x + w)`,
`P (x − w)` is nonzero. Half comes from `pushUp_eq_zero` (off the
image, the push is zero), the other half from the `max`/`min` shapes of
`split` (a nonzero half forces one of the two arguments nonzero).

This is the support auxiliary consumed by the containment transfer
`supportContained_pushUp_split`: it reduces any support question on the
push to a support question on `P`. -/
lemma pushUp_split_ne_zero {d : ℕ} (w : Fin d → ℤ) {P : (Fin d → ℤ) → ℝ}
    {z : Fin (d + 1) → ℤ} (hz : pushUp (split w P) z ≠ 0) :
    ∃ (x : Fin d → ℤ) (b : Bool), z = liftUp (x, b) ∧
      (P (x + w) ≠ 0 ∨ P (x - w) ≠ 0) := by
  by_cases hex : ∃ y : (Fin d → ℤ) × Bool, liftUp y = z
  · obtain ⟨⟨x, b⟩, rfl⟩ := hex
    rw [pushUp_apply] at hz
    refine ⟨x, b, rfl, ?_⟩
    cases b with
    | false =>
        rw [split_apply_zero] at hz
        rcases le_total (P (x + w)) (P (x - w)) with h | h
        · rw [max_eq_right h] at hz
          exact Or.inr (by intro h0; rw [h0, mul_zero] at hz; exact hz rfl)
        · rw [max_eq_left h] at hz
          exact Or.inl (by intro h0; rw [h0, mul_zero] at hz; exact hz rfl)
    | true =>
        rw [split_apply_one] at hz
        rcases le_total (P (x + w)) (P (x - w)) with h | h
        · rw [min_eq_left h] at hz
          exact Or.inl (by intro h0; rw [h0, mul_zero] at hz; exact hz rfl)
        · rw [min_eq_right h] at hz
          exact Or.inr (by intro h0; rw [h0, mul_zero] at hz; exact hz rfl)
  · rw [pushUp_eq_zero _ (fun y hy => hex ⟨y, hy⟩)] at hz
    exact absurd rfl hz

/-- **Containment transfer across the split**: if `S` contains the
support of `P` and its translates by `A`, and `A` is stable under
`± w`, then the lifted image `(S ×ˢ univ).map liftUpEmb` contains the
support of the split-push `pushUp (split w P)` and its translates by
the embedded shifts `Fin.snoc · 0` of `A`.

This is the support precondition the induction step (k2.6c) must
establish to apply the induction hypothesis at dimension `d + 1`: at
the oracle (`Komlos/SignedSums.lean` l.44-53), the `Finsupp` pays this
transport for free (`Finsupp.embDomain`); the lake's `Finset` framework
pays it here. The stability of `A` under `± w` is the exact price of
the split: a mass point `P (x ± w) ≠ 0` moved by `a` lands at `x + a`,
reached from `x ± w` through the shift `a ∓ w ∈ A`. -/
theorem supportContained_pushUp_split {d : ℕ} (w : Fin d → ℤ)
    {P : (Fin d → ℤ) → ℝ} {S A : Finset (Fin d → ℤ)}
    (hS : SupportContained S P A)
    (hA : ∀ a ∈ A, a + w ∈ A ∧ a - w ∈ A) :
    SupportContained ((S ×ˢ (Finset.univ : Finset Bool)).map liftUpEmb)
      (pushUp (split w P)) (A.image (fun a => Fin.snoc a 0)) := by
  intro z hz t ht
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨x, b, rfl, hPw⟩ := pushUp_split_ne_zero w hz
  rw [liftUp_add_snoc]
  show liftUp (x + a, b) ∈ (S ×ˢ (Finset.univ : Finset Bool)).map liftUpEmb
  refine Finset.mem_map.mpr ⟨(x + a, b), ?_, liftUpEmb_apply _⟩
  refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
  rcases hPw with h | h
  · have hxw := hS (x + w) h (a - w) (hA a ha).2
    have hxa : (x + w) + (a - w) = x + a := by
      funext j; simp only [Pi.add_apply, Pi.sub_apply]; ring
    rw [← hxa]; exact hxw
  · have hxw := hS (x - w) h (a + w) (hA a ha).1
    have hxa : (x - w) + (a + w) = x + a := by
      funext j; simp only [Pi.add_apply, Pi.sub_apply]; ring
    rw [← hxa]; exact hxw

/-- **Conservation of the base moment under containment, at the lifted
level**: the coordinate moment of the split-push, read on an inherited
coordinate `i.castSucc`, is the moment of `P` at `i` — under the same
containment `SupportContained S P {0, w, −w}` as
`prodMoment_split_of_support` (k2.0). This is the composition of the
moment bridge `coordMoment_pushUp_castSucc` (k2.6a, unconditional) with
the k2.0 conservation identity: the base barycenter crosses the split
**and then** the level bridge unchanged.

Measured consumer: the `rw [mean_split, sum_smul_inl, …] at hmem` of
the induction step (`Komlos/SignedSums.lean` l.54), spatial component. -/
theorem coordMoment_pushUp_split_of_support {d : ℕ} (w : Fin d → ℤ)
    {P : (Fin d → ℤ) → ℝ} {S : Finset (Fin d → ℤ)}
    (hS : SupportContained S P ({0, w, -w} : Finset (Fin d → ℤ)))
    (i : Fin d) :
    coordMoment (pushUp (split w P))
        ((S ×ˢ (Finset.univ : Finset Bool)).map liftUpEmb) i.castSucc
      = coordMoment P S i := by
  rw [coordMoment_pushUp_castSucc, prodMoment_split_of_support w hS i]

/-- **The height moment of the split-push, at the lifted level**: read
on the last coordinate, it is the split bit `splitBit w P S` — the
height component of `mean_split_of_support` (k2.0) through the bridge
`coordMoment_pushUp_last` (k2.6a). No containment is required: the
height moment is read slice by slice (`heightMoment_split`, k2.0).

Measured consumer: the `rw [mean_split, …] at hmem` of the induction
step (`Komlos/SignedSums.lean` l.54), height component. -/
theorem coordMoment_pushUp_split_last {d : ℕ} (w : Fin d → ℤ)
    (P : (Fin d → ℤ) → ℝ) (S : Finset (Fin d → ℤ)) :
    coordMoment (pushUp (split w P))
        ((S ×ˢ (Finset.univ : Finset Bool)).map liftUpEmb) (Fin.last d)
      = splitBit w P S := by
  rw [coordMoment_pushUp_last, heightMoment_split]

/-- **The next step's containment, in the exact form the induction
consumes**: if `A` contains `0`, `u` and `−u` and is stable under
`± w`, the split-push obeys the containment `{0, snoc u 0, −snoc u 0}`
on the lifted image. This is the instance by monotonicity
(`SupportContained.mono`) of the generic transfer, the three shifts
being the `snoc · 0` images of `0` (`snoc 0 0 = 0`), `u` and `−u`
(`−snoc u 0 = snoc (−u) 0`).

The next induction step (k2.6c) splits `pushUp (split w P)` in the
direction `u` embedded at height zero — the `_of_support` forms of
k2.0 (applied at dimension `d + 1`) require exactly this three-shift
containment. -/
theorem supportContained_pushUp_split_three {d : ℕ} (w u : Fin d → ℤ)
    {P : (Fin d → ℤ) → ℝ} {S A : Finset (Fin d → ℤ)}
    (hS : SupportContained S P A)
    (hA : ∀ a ∈ A, a + w ∈ A ∧ a - w ∈ A)
    (h0 : (0 : Fin d → ℤ) ∈ A) (hu : u ∈ A) (hu' : -u ∈ A) :
    SupportContained ((S ×ˢ (Finset.univ : Finset Bool)).map liftUpEmb)
      (pushUp (split w P))
      ({0, Fin.snoc u 0, -(Fin.snoc u 0)} : Finset (Fin (d + 1) → ℤ)) := by
  refine (supportContained_pushUp_split w hS hA).mono ?_
  intro t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · refine Finset.mem_image.mpr ⟨0, h0, ?_⟩
    funext j
    induction j using Fin.lastCases <;> simp
  · exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
  · refine Finset.mem_image.mpr ⟨-u, hu', ?_⟩
    funext j
    induction j using Fin.lastCases <;> simp [Pi.neg_apply]

end Discrepancy.Komlos_en
