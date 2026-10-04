/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted to `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, i18n convention #4980.

The original Dahia source lives in the repository `gdahia/Komlos` (module
`Komlos/Split.lean`, toolchain v4.34.0, `Finsupp` framework over `E →₀ ℝ`,
height `E × ℝ`). The adaptation below follows the lake convention established
by brick k1.1 (`ShiftDistance.lean`) : **explicit Finset** framework with the
support passed as an argument, `Bool` height for the product space (k1.2).

**Scope of this commit** (brick k2.0, `lake build SUCCESS` required, 0 `sorry`) :

Bricks closed : `coordMoment` and `prodMoment` (the **moments** — the
barycentre read coordinate by coordinate, on the base and on the product
space), `heightMoment` (the height moment), `heightMoment_split` (the height
moment of `T_v P` is the split bit), `prodMoment_split` (the split
**preserves** the base moment), and `mean_split` — the lake form of Dahia's
`mean_split`, **the item brick k1.6 explicitly deferred to k2**.

**Why this brick is a prerequisite of k2 rather than an ornament.** Dahia's
`mean_split` is stated over a `Finsupp` of `E × ℝ` :
`mean (split v P) = (mean P, splitBit v P)`, with `mean P = ∑_x P x • x`. That
framework does not exist in this lake : `x : Fin d → ℤ` is not an `ℝ`-module,
so the scaling `P x • x` has no meaning. The faithful decomposition is
therefore **component-wise** — and that is what this module delivers :

- the **height** component `∑_y (T_v P)(y) · (y.2)` equals `splitBit v P S`
  (a generalisation of k1.6's `sum_split_high` to the height weighting) ;
- the **base** component `∑_y (T_v P)(y) · (y.1 i)` equals the moment of `P`
  in coordinate `i` — the split **preserves the barycentre**, which
  `split_mass` did not state (it preserves only the mass, the order-0 moment).

It is this order-1 moment preservation that carries k2's statement : Lemma 1.4
concludes `μ(P) + ∑ ε_i v_i ∈ conv(supp P)`, a claim about the **barycentre**,
not about the mass.

**Deferred to k2 (Lemma 1.4)** : the entropy lemma and the simultaneous
induction on `n` and `d`. The detailed state lives in `FORMAL_STATUS.md`.
-/

import Discrepancy.Komlos.SplitBit_en

/-!
# Moments of the split and `mean_split` (Karingula–Lovett)

This module closes the identity `mean_split` — the mean of `T_v P` under its
two components : the base barycentre is **preserved** by the split, and the
height moment **is** the split bit. This is the order-1 ingredient that
Lemma 1.4 consumes, where the k1 bricks provided only the order-0 moment
(`split_mass`).

**Reading convention.** The Dahia oracle writes `mean (split v P) = (mean P,
splitBit v P)` in a real framework `E` where `P x • x` makes sense. Here the
base is `Fin d → ℤ` : the moment is therefore read **coordinate by coordinate**
(`i : Fin d`), each coordinate being pushed into `ℝ` by `(x i : ℝ)`. No real
module structure is required on the base — this is the framework adaptation,
declared rather than worked around by an artificial `Fintype` or embedding.

**Hypotheses.** `prodMoment_split` requires the invariance of the support
under `±v` — the same hypotheses as `split_mass` (k1.2), and for the same
reason : the re-indexation `x ↦ x ± v` must be exact on `S`.
`heightMoment_split` requires none : the height moment reads slice by slice.
-/

namespace Discrepancy.Komlos_en

/-- **Coordinate moment** (barycentre) of a distribution `P` over its support
`S`, in coordinate `i` : `∑ x ∈ S, P x * (x i : ℝ)`. This is the coordinate
analogue of Dahia's `mean P = ∑_x P x • x` — the lake base being
`Fin d → ℤ` (not an `ℝ`-module), the moment is read coordinate by
coordinate, each coordinate pushed into `ℝ`. -/
noncomputable def coordMoment {d : ℕ} (P : (Fin d → ℤ) → ℝ)
    (S : Finset (Fin d → ℤ)) (i : Fin d) : ℝ :=
  ∑ x ∈ S, P x * (x i : ℝ)

/-- **Height moment** of a distribution over the product space
`(Fin d → ℤ) × Bool` : `∑ y ∈ T, P y * (y.2 : ℝ)`, the `Bool` height being
read `false ↦ 0`, `true ↦ 1`. This is the height component of Dahia's `mean`,
whose second factor is `r : ℝ` in his `E × ℝ` framework. -/
noncomputable def heightMoment {d : ℕ} (P : ((Fin d → ℤ) × Bool) → ℝ)
    (T : Finset ((Fin d → ℤ) × Bool)) : ℝ :=
  ∑ y ∈ T, P y * (if y.2 then (1 : ℝ) else 0)

/-- **Base moment** of a distribution over the product space, in coordinate
`i` : `∑ y ∈ T, P y * (y.1 i : ℝ)`. Base component of Dahia's `mean`
(`x • x` replaced by the coordinate reading, cf `coordMoment`). -/
noncomputable def prodMoment {d : ℕ} (P : ((Fin d → ℤ) × Bool) → ℝ)
    (T : Finset ((Fin d → ℤ) × Bool)) (i : Fin d) : ℝ :=
  ∑ y ∈ T, P y * (y.1 i : ℝ)

/-- **The height moment of the split is the split bit** :
`∑_y (T_v P)(y) · (y.2) = splitBit v P S`. Generalises k1.6's
`sum_split_high` — the unweighted case — to the height reading : the `false`
slice carries weight `0`, the `true` slice weight `1`, and only the mass of
the high slice remains. No support invariance is required. -/
lemma heightMoment_split {d : ℕ} (v : Fin d → ℤ) (P : (Fin d → ℤ) → ℝ)
    (S : Finset (Fin d → ℤ)) :
    heightMoment (split v P) (S ×ˢ (Finset.univ : Finset Bool)) = splitBit v P S := by
  have hbool : ∀ x : Fin d → ℤ,
      (∑ b ∈ (Finset.univ : Finset Bool), split v P (x, b) * (if b then (1 : ℝ) else 0))
        = split v P (x, true) := by
    intro x
    simp
  rw [heightMoment, Finset.sum_product,
    Finset.sum_congr rfl fun x _ => hbool x]
  exact sum_split_high v P S

/-- **The split preserves the base moment** : `∑_y (T_v P)(y) · (y.1 i)`
equals the coordinate moment of `P` in `i`. This is the order-1 statement that
`split_mass` (k1.2, order 0) did not carry, and the base component of
`mean_split`. Proof : for fixed `x`, the two slices sum to
`½(P(x+v) + P(x−v))` (the `max_add_min` identity already consumed by
`split_mass`), then the two terms are re-indexed by `x ↦ x ∓ v`
(`sum_translate_image`, k1.2) and become the two halves of the same moment
`((x−v) i) + ((x+v) i) = 2 · (x i)`. -/
lemma prodMoment_split {d : ℕ} (v : Fin d → ℤ) {P : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)}
    (hSv : S.image (fun x => x + v) = S)
    (hSvm : S.image (fun x => x - v) = S) (i : Fin d) :
    prodMoment (split v P) (S ×ˢ (Finset.univ : Finset Bool)) i
      = coordMoment P S i := by
  have hbool : ∀ x : Fin d → ℤ,
      (∑ b ∈ (Finset.univ : Finset Bool), split v P (x, b)) * (x i : ℝ)
        = (1 / 2 : ℝ) * (P (x + v) + P (x - v)) * (x i : ℝ) := by
    intro x
    have h2 : (∑ b ∈ (Finset.univ : Finset Bool), split v P (x, b))
        = split v P (x, false) + split v P (x, true) := by
      simp
      ac_rfl
    rw [h2, split_apply_zero, split_apply_one, ← mul_add, max_add_min]
  have hreindex_plus : ∑ x ∈ S, (1 / 2 : ℝ) * P (x + v) * (x i : ℝ)
      = ∑ x ∈ S, (1 / 2 : ℝ) * P x * (((x - v) i : ℤ) : ℝ) := by
    have h := sum_translate_image v hSv
      (P := fun x => (1 / 2 : ℝ) * P x * (((x - v) i : ℤ) : ℝ))
    rw [← h]
    refine Finset.sum_congr rfl fun x _ => ?_
    have : ((x + v) - v) i = x i := by simp [Pi.sub_apply, Pi.add_apply]
    rw [this]
  have hreindex_minus : ∑ x ∈ S, (1 / 2 : ℝ) * P (x - v) * (x i : ℝ)
      = ∑ x ∈ S, (1 / 2 : ℝ) * P x * (((x + v) i : ℤ) : ℝ) := by
    have h := sum_translate_image (-v) hSvm
      (P := fun x => (1 / 2 : ℝ) * P x * (((x + v) i : ℤ) : ℝ))
    rw [← h]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hkey : (((x + -v) + v) i : ℤ) = x i := by
      simp [Pi.add_apply]
    rw [hkey]
    have hx : x + -v = x - v := by
      funext j
      simp [Pi.sub_apply, Pi.add_apply, sub_eq_add_neg]
    rw [hx]
  have hinner : ∀ x ∈ S,
      (∑ b ∈ (Finset.univ : Finset Bool), split v P (x, b) * (x i : ℝ))
        = (1 / 2 : ℝ) * (P (x + v) + P (x - v)) * (x i : ℝ) := by
    intro x _
    rw [← Finset.sum_mul]
    exact hbool x
  have hsplit : ∀ x ∈ S,
      (1 / 2 : ℝ) * (P (x + v) + P (x - v)) * (x i : ℝ)
        = (1 / 2 : ℝ) * P (x + v) * (x i : ℝ)
          + (1 / 2 : ℝ) * P (x - v) * (x i : ℝ) := by
    intro x _
    ring
  unfold prodMoment coordMoment
  rw [Finset.sum_product]
  rw [Finset.sum_congr rfl hinner, Finset.sum_congr rfl hsplit,
    Finset.sum_add_distrib, hreindex_plus, hreindex_minus,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.sub_apply, Pi.add_apply, Int.cast_sub, Int.cast_add]
  ring

/-- **`mean_split`** (lake form of Dahia's `mean_split`) : the mean of `T_v P`
over `S × {false, true}` equals, component by component, the pair
`(base moment of P, split bit)`. This is the order-1 identity that Lemma 1.4
consumes : `splitBit` carries the split information over to the shift distance
(k1.6), and the base moment carries the barycentre towards the conclusion
`μ(P) + ∑ ε_i v_i ∈ conv(supp P)`. -/
theorem mean_split {d : ℕ} (v : Fin d → ℤ) {P : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)}
    (hSv : S.image (fun x => x + v) = S)
    (hSvm : S.image (fun x => x - v) = S) (i : Fin d) :
    (prodMoment (split v P) (S ×ˢ (Finset.univ : Finset Bool)) i,
      heightMoment (split v P) (S ×ˢ (Finset.univ : Finset Bool)))
      = (coordMoment P S i, splitBit v P S) := by
  rw [prodMoment_split v hSv hSvm i, heightMoment_split v P S]

end Discrepancy.Komlos_en
