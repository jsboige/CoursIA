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

**What remains for k2 (Lemma 1.4) — a list measured against the oracle, not
assumed.** The formal oracle of that lemma (`gdahia/Komlos`,
`Komlos/SignedSums.lean`) **consumes this `mean_split`** (l.54) and proceeds by
**induction on `n` alone** (l.37), the ambient space growing at each split
(`E × ℝ`). Measured on this lake, what is missing: the **pullback triple**
(`exists_sign_mul_add_eq`, `add_smul_mem_convexHull`, `pullback`), the finitary
counterpart of `mean_mem_convexHull`, `sum_smul_inl`, the **convexity machinery**
(no occurrence of `convexHull` in this lake, while the conclusion is one) and the
**dimension transport** that replaces the generality of `E` here. The detailed
state lives in `FORMAL_STATUS.md`. The earlier wording "entropy lemma" is
**retracted** : it has no referent in the oracle.

**Correction k2.0 — the consumable forms.** `prodMoment_split` and `mean_split`
carry the invariance `S.image (· ± v) = S`, which k1.7
(`Discrepancy/Komlos/Containment_en.lean`) proved unsatisfiable at nonzero
shifts on a nonempty `Finset` of `ℤ^d` (`eq_zero_of_image_add_eq_self`) :
these two statements are true but not instantiable at the shifts Lemma 1.4
consumes. The module therefore adds the forms under support containment
`SupportContained S P {0, v, -v}` : `prodMoment_split_of_support` (same
skeleton as `prodMoment_split`, the re-indexing `x ↦ x ∓ v` carried by
`sum_comp_add_eq_sum_of_support` on the weighted functions
`x ↦ ½ · P x · ((x ∓ v) i : ℝ)`, the weighted support derived from that of
`P` by `mul_zero` contradiction) and `mean_split_of_support` (which reuses
`heightMoment_split` unchanged). The invariant forms remain in place ; the
addendum does not claim to discharge Lemma 1.4 (the list of missing bricks
above remains accurate).
-/

import Discrepancy.Komlos.Containment_en
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
Since k1.7 (`Containment_en.lean`) this invariance is proved unsatisfiable
at nonzero shifts (`eq_zero_of_image_add_eq_self`) : `prodMoment_split` and
`mean_split` are the historical invariant forms, and the module adds the
consumable forms `prodMoment_split_of_support` / `mean_split_of_support`
under `SupportContained S P {0, v, -v}`.
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

/-- **The split preserves the base moment, under containment** : the
consumable version of `prodMoment_split` — the invariance
`S.image (· ± v) = S` is replaced by `SupportContained S P {0, v, -v}`
(k1.7), satisfiable at the nonzero shifts where `eq_zero_of_image_add_eq_self`
empties the invariance. The proof is that of `prodMoment_split` (same
`hbool`/`hinner`/`hsplit` and assembly), the re-indexing `x ↦ x ∓ v` being
carried by `sum_comp_add_eq_sum_of_support` applied to the weighted functions
`x ↦ ½ · P x · ((x ∓ v) i : ℝ)` — the weighted support is derived from that
of `P` by contradiction (`mul_zero` : zero weight as soon as `P z = 0`). -/
lemma prodMoment_split_of_support {d : ℕ} (v : Fin d → ℤ)
    {P : (Fin d → ℤ) → ℝ} {S : Finset (Fin d → ℤ)}
    (hS : SupportContained S P ({0, v, -v} : Finset (Fin d → ℤ)))
    (i : Fin d) :
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
  have hPz_sub : ∀ z, (1 / 2 : ℝ) * P z * (((z - v) i : ℤ) : ℝ) ≠ 0 →
      P z ≠ 0 := by
    intro z hz h0
    exact hz (by rw [h0, mul_zero, zero_mul])
  have hPz_add : ∀ z, (1 / 2 : ℝ) * P z * (((z + v) i : ℤ) : ℝ) ≠ 0 →
      P z ≠ 0 := by
    intro z hz h0
    exact hz (by rw [h0, mul_zero, zero_mul])
  have hreindex_plus : ∑ x ∈ S, (1 / 2 : ℝ) * P (x + v) * (x i : ℝ)
      = ∑ x ∈ S, (1 / 2 : ℝ) * P x * (((x - v) i : ℤ) : ℝ) := by
    have h : ∑ x ∈ S, (1 / 2 : ℝ) * P (x + v) * ((((x + v) - v) i : ℤ) : ℝ)
        = ∑ x ∈ S, (1 / 2 : ℝ) * P x * (((x - v) i : ℤ) : ℝ) :=
      sum_comp_add_eq_sum_of_support
        (P := fun x => (1 / 2 : ℝ) * P x * (((x - v) i : ℤ) : ℝ)) (v := v)
        (fun z hz => by simpa using hS z (hPz_sub z hz) 0 (by simp))
        (fun z hz => by
          have hmem := hS z (hPz_sub z hz) (-v)
            (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
          simpa [sub_eq_add_neg] using hmem)
    rw [← h]
    refine Finset.sum_congr rfl fun x _ => ?_
    have : ((x + v) - v) i = x i := by simp [Pi.sub_apply, Pi.add_apply]
    rw [this]
  have hreindex_minus : ∑ x ∈ S, (1 / 2 : ℝ) * P (x - v) * (x i : ℝ)
      = ∑ x ∈ S, (1 / 2 : ℝ) * P x * (((x + v) i : ℤ) : ℝ) := by
    have h : ∑ x ∈ S, (1 / 2 : ℝ) * P (x + -v) * ((((x + -v) + v) i : ℤ) : ℝ)
        = ∑ x ∈ S, (1 / 2 : ℝ) * P x * (((x + v) i : ℤ) : ℝ) :=
      sum_comp_add_eq_sum_of_support
        (P := fun x => (1 / 2 : ℝ) * P x * (((x + v) i : ℤ) : ℝ)) (v := -v)
        (fun z hz => by simpa using hS z (hPz_add z hz) 0 (by simp))
        (fun z hz => by
          have hmem := hS z (hPz_add z hz) v
            (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
          simpa [sub_neg_eq_add] using hmem)
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

/-- **`mean_split` under containment** : the consumable version of
`mean_split` — the invariance `S.image (· ± v) = S` is replaced by
`SupportContained S P {0, v, -v}` (k1.7). Base component by
`prodMoment_split_of_support`, height component by `heightMoment_split`
reused unchanged — it requires no support hypothesis, the height moment reads
slice by slice. -/
theorem mean_split_of_support {d : ℕ} (v : Fin d → ℤ)
    {P : (Fin d → ℤ) → ℝ} {S : Finset (Fin d → ℤ)}
    (hS : SupportContained S P ({0, v, -v} : Finset (Fin d → ℤ)))
    (i : Fin d) :
    (prodMoment (split v P) (S ×ˢ (Finset.univ : Finset Bool)) i,
      heightMoment (split v P) (S ×ˢ (Finset.univ : Finset Bool)))
      = (coordMoment P S i, splitBit v P S) := by
  rw [prodMoment_split_of_support v hS i, heightMoment_split v P S]

/-- **Positive control at a nonzero shift** : the containment hypothesis is
satisfiable where the invariance is not. For `d = 1`, `v` the constant
function `1` and `P` the Dirac mass at `0`, the `S` built by
`supportContained_biUnion` (which equals `{-1, 0, 1}` here) is nonempty,
carries `SupportContained S P {0, v, -v}`, and the invariance
`S.image (· + v) = S` **fails** on it — it would force `v = 0` by
`eq_zero_of_image_add_eq_self` (k1.7). The `_of_support` forms of this module
therefore have nonempty instances of their hypotheses at the shifts Lemma 1.4
consumes, where the k2.0 invariant forms admit no nontrivial instance. -/
theorem exists_supportContained_nonzero_shift :
    ∃ (S : Finset (Fin 1 → ℤ)) (P : (Fin 1 → ℤ) → ℝ),
      (fun _ => (1 : ℤ)) ≠ (0 : Fin 1 → ℤ) ∧ S.Nonempty ∧
      SupportContained S P
        ({0, (fun _ => (1 : ℤ)), -((fun _ => (1 : ℤ)))} : Finset (Fin 1 → ℤ)) ∧
      S.image (fun x => x + (fun _ => (1 : ℤ))) ≠ S := by
  refine ⟨({0} : Finset (Fin 1 → ℤ)) ∪
    ({0, (fun _ => (1 : ℤ)), -((fun _ => (1 : ℤ)))} : Finset (Fin 1 → ℤ)).biUnion
      (fun w => ({0} : Finset (Fin 1 → ℤ)).image (fun z => z + w)),
    fun x => if x = 0 then (1 : ℝ) else 0, ?_, ?_, ?_, ?_⟩
  · -- The constant function `1` is not zero.
    intro h
    have h0 : (1 : ℤ) = 0 := congrFun h (0 : Fin 1)
    omega
  · -- `S` is nonempty : it contains `0`.
    exact ⟨(0 : Fin 1 → ℤ), Finset.mem_union_left _ (Finset.mem_singleton_self _)⟩
  · -- Containment : `supportContained_biUnion` with `S₀ = {0}`.
    exact supportContained_biUnion
      (fun z hz => by
        refine Finset.mem_singleton.mpr ?_
        by_contra hne
        have hz0 : (if z = (0 : Fin 1 → ℤ) then (1 : ℝ) else 0) = 0 := by
          rw [if_neg hne]
        exact hz hz0)
  · -- The invariance fails : it would force `v = 0` (k1.7).
    intro hinv
    have hne : (({0} : Finset (Fin 1 → ℤ)) ∪
      ({0, (fun _ => (1 : ℤ)), -((fun _ => (1 : ℤ)))} : Finset (Fin 1 → ℤ)).biUnion
        (fun w => ({0} : Finset (Fin 1 → ℤ)).image (fun z => z + w))).Nonempty :=
      ⟨(0 : Fin 1 → ℤ), Finset.mem_union_left _ (Finset.mem_singleton_self _)⟩
    have hv0 : (fun _ => (1 : ℤ)) = (0 : Fin 1 → ℤ) :=
      eq_zero_of_image_add_eq_self hinv hne
    have h1 : (1 : ℤ) = 0 := congrFun hv0 (0 : Fin 1)
    omega

end Discrepancy.Komlos_en
