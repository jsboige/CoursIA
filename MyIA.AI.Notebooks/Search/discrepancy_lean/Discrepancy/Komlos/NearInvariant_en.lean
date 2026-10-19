/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted to `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, i18n convention #4980.

The original Dahia source lives in the `gdahia/Komlos` repository:
`Komlos/NearInvariant.lean` (Lemma 1.5, `exists_nearInvariant`). The adaptation carries
the module over **name for name** within the lake's explicit-`Finset` framing
(convention k1.1) — see the scope below.

**Scope of this commit** (brick k4.3, `lake build SUCCESS` required, 0 `sorry`):

Closed bricks: `gridEmb` + `gridEmb_apply` + `gridEmb_injective` (the embedding
`g ↦ g / N` of the integer grid into `N⁻¹ • ℤ^d` — in the oracle l.28-43), `gridF_neg` /
`cubeF_neg` (the two parity identities of the product weight), `nearBox` + `nearBox_neg`
(this module's **uniform** working box), `shiftDistance_nearBox_eq_shiftBox` +
`shiftDistance_cubeF_sq_le_nearBox` (the k4.2 quadratic bound read back on that uniform
box), and finally `exists_nearInvariant` (Lemma 1.5 itself).

**The port's own difficulty, and how it dissolves.** In the oracle, `P` is a `Finsupp`:
its support is **canonical**, and its `shiftDist P u` sums over the support of
`P - tr u P` — hence over the union of the two translated supports, automatically. In
the lake the summation `Finset` is a **parameter** (k1.1) and the statement's support is
**existential**: the same `Finset` must therefore serve **all** shifts `g` of the
conclusion, whereas the k4.2 box (`shiftBox N h`) depends on `h`. It is `nearBox d N`
that reconciles them: the box `[-7N, 7N]^d`, which contains `shiftBox N h` for **every**
admissible `h` (`|h k| ≤ N`, a consequence of the hypothesis `Σ k, ((h k)/N)² ≤ 1`),
and where off-support contributions vanish — the sum there **is** the shift distance
(k1.1's contract: "`S` may be larger than needed"), and it agrees term by term with the
one over `shiftBox` (`shiftDistance_nearBox_eq_shiftBox`).

**What the lake pays, and where.** The oracle's `IsDist` vocabulary stays outside the
lake (k1.1 framing decision): `exists_nearInvariant` writes it **in the clear** in its
conclusion — pointwise positivity, mass 1, support within `‖x‖ ≤ 6`, zero mean — as
k2.5 had done for `mean_mem_convexHull`. The zero mean is read coordinate by coordinate
(`coordMomentReal`, k2.3): the real grid has no vector `mean` in this lake, it has
moments, and the vanishing of each of them *is* the statement "zero mean". The oracle's
generic lemma (`sum_smul_eq_zero_of_neg`) is not carried over as such: its `Finsupp`
form (`equivMapDomain`, `Finsupp.sum_neg`) has no object in a lake without `Finsupp` —
its **substance** (an even weight on a symmetric box has a vanishing moment) is proved
directly, by re-indexing `Finset.sum_map` along negation.

**Deferred, with a measured reason**: nothing. The oracle module is carried over **in
full**. `IsDist.push` (deferred by k2.3, k4.2c) remains the only unpaid vocabulary of
the transport, and it **still** has no consumer: k4.3 writes its components in the
clear rather than paying for it.

**Consumed by**: the rest of the campaign (assembly of the discrepancy theorem,
EPIC #17845).
-/

import Discrepancy.Komlos.Cube_en
import Discrepancy.Komlos.ShiftPush_en
import Discrepancy.Komlos.Transport_en

/-!
# Near-invariant distributions (brick k4.3, Lemma 1.5)

For every `N > 0` there exists a distribution `P` on the real grid `N⁻¹ • ℤ^d` —
positive, of mass `1`, supported in `[-6, 6]^d`, of **zero mean** — such that for
**every** `g : Fin d → ℤ` whose normalised shift has norm at most `1`
(`Σ k, ((g k)/N)² ≤ 1`), the shift distance between `P` and its translate by `g / N` is
at most `1/3`.

This is Lemma 1.5 of Karingula–Lovett, and it is the brick that **consumes the whole k4
campaign**: `cubeF d N ^ 2` (k4.2) is the product weight whose shift is quadratically
small, `gridEmb d N` (`g ↦ g / N`) is the embedding k4.2c transports, and
`shiftDistanceTV_push` reads the `Komlos.Cube` bound back on the real grid **without
recomputing it**.

The proof has three moves: (1) push `cubeF d N ^ 2` along `gridEmb d N` (`push`, k2.3);
(2) read the pushed weight's invariants off the already-delivered organs — positivity and
mass (`push_apply`, `push_mass`), support (`support_gridF_subset`), zero mean by
**symmetry** (the product weight is even, the box is symmetric); (3) bound the shift by
transporting `shiftDistance_cubeF_sq_le` (k4.2) onto the uniform box `nearBox`, then
through `shiftDistanceTV_push` (k4.2c). The oracle's `IsDist` is not paid for: the
conclusion writes it in the clear, as the lake does everywhere.
-/

namespace Discrepancy.Komlos_en

open Finset

/-- **Embedding of the integer grid into the real grid**: `gridEmb d N g` is the function
`k ↦ (g k : ℝ) / N`, that is, the point `g / N` of `N⁻¹ • ℤ^d`.

It is the embedding along which k4.3 pushes the product weight — in the oracle
(`Komlos/NearInvariant.lean` l.28-35) `gridEmb d N g k = (g k : ℝ) / N`. It is additive
coordinate by coordinate, and injective for `N > 0` (`gridEmb_injective`). It composes
`toReal` (k2.3) with the scaling `· / N`, as `Transport.lean` announced. -/
noncomputable def gridEmb (d N : ℕ) : (Fin d → ℤ) →+ (Fin d → ℝ) where
  toFun g k := (g k : ℝ) / N
  map_zero' := by ext k; simp
  map_add' g g' := by
    ext k
    simp only [Pi.add_apply, Int.cast_add, add_div]

/-- Coordinatewise reading of the embedding: `gridEmb d N g k = (g k : ℝ) / N`. -/
@[simp] lemma gridEmb_apply (d N : ℕ) (g : Fin d → ℤ) (k : Fin d) :
    gridEmb d N g k = (g k : ℝ) / N := rfl

/-- **The embedding is injective** for `N > 0`: equality of the images gives equality of
the quotients `(g k)/N`, hence — the denominator being nonzero — equality of the integer
coordinates. (In the oracle: `gridEmb_injective`, l.31-33.) -/
lemma gridEmb_injective {d N : ℕ} (hN : 0 < N) : Function.Injective (gridEmb d N) := by
  intro g g' h
  funext k
  have hk := congrFun h k
  simp only [gridEmb_apply] at hk
  exact Int.cast_injective
    ((div_left_inj' (by exact_mod_cast hN.ne' : (N : ℝ) ≠ 0)).mp hk)

/-- The one-dimensional weight is **even**: `gridF N (-j) = gridF N j`. It is the parity
of the tent (`tent_neg`, k3.1) as the grid reads it. -/
lemma gridF_neg (N : ℕ) (j : ℤ) : gridF N (-j) = gridF N j := by
  simp [gridF]

/-- The product weight is **even**: `cubeF d N (-g) = cubeF d N g` — a product of even
factors. (In the oracle: `cubeP_neg`.) -/
lemma cubeF_neg {d N : ℕ} (g : Fin d → ℤ) : cubeF d N (-g) = cubeF d N g := by
  simp only [cubeF]
  exact Finset.prod_congr rfl fun k _ => by rw [Pi.neg_apply, gridF_neg]

/-- **k4.3's uniform working box**: `[-7N, 7N]^d`, that is,
`(Icc (-(gridM N + N)) (gridM N + N))^d`.

It is the box that makes `exists_nearInvariant`'s support **independent of the shift**: it
contains `shiftBox N h` for every `h` whose coordinates satisfy `|h k| ≤ N` — the case of
every `h` admissible in the sense of the hypothesis `Σ k, ((h k)/N)² ≤ 1`. Where
`shiftBox N h` follows the shift, `nearBox` dominates it once and for all.
`noncomputable` like `shiftBox` (k4.2a): an `Icc` of `ℤ` is not a computation, it is an
interval of the noncomputable order. -/
noncomputable def nearBox (d N : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ : Fin d ↦ Icc (-(((gridM N + N : ℕ) : ℤ))) ((gridM N + N : ℕ) : ℤ)

/-- **The uniform box is symmetric**: `nearBox d N` is stable under negation — which is
what the zero mean consumes. Each coordinate lives in an `Icc` centred at `0`, so
membership there **is** a bound on the absolute value (`abs_le`); the absolute value is
invariant under negation (`abs_neg`), and stability follows coordinate by coordinate. -/
lemma nearBox_neg {d N : ℕ} :
    (nearBox d N).map ⟨Neg.neg, neg_injective⟩ = nearBox d N := by
  have hB : ∀ x : Fin d → ℤ,
      (x ∈ nearBox d N ↔ ∀ k, |x k| ≤ (((gridM N + N : ℕ) : ℤ))) := by
    intro x
    rw [nearBox, Fintype.mem_piFinset]
    constructor
    · intro h k
      have hk := h k
      rw [Finset.mem_Icc] at hk
      exact abs_le.mpr hk
    · intro h k
      rw [Finset.mem_Icc]
      exact abs_le.mp (h k)
  ext x
  rw [Finset.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show (-y) ∈ nearBox d N
    exact (hB (-y)).mpr (by
      intro k
      show |(-y) k| ≤ (((gridM N + N : ℕ) : ℤ))
      rw [Pi.neg_apply, abs_neg]
      exact (hB y).mp hy k)
  · intro hx
    exact ⟨-x, (hB (-x)).mpr (by
      intro k
      show |(-x) k| ≤ (((gridM N + N : ℕ) : ℤ))
      rw [Pi.neg_apply, abs_neg]
      exact (hB x).mp hx k), neg_neg x⟩

/-- **The shift-distance sum over the uniform box is the one over k4.2's box**, as soon as
the shift is admissible (`|h k| ≤ N`): both boxes contain the support of `cubeF d N ^ 2`
**and** the support of its translate, and k1.1's contract ("`S` may be larger than
needed") makes the extra contributions vanish.

This is the piece that makes `exists_nearInvariant`'s support uniform: `nearBox` dominates
`shiftBox N h` for **every** admissible `h`, and the value of the distance is unchanged by
it. The sum over `shiftBox` is k4.2's bound; the one over `nearBox` is what the transport
reads. -/
lemma shiftDistance_nearBox_eq_shiftBox {d N : ℕ} (h : Fin d → ℤ)
    (hh : ∀ k, |h k| ≤ (N : ℤ)) :
    shiftDistance (nearBox d N) (fun g ↦ cubeF d N g ^ 2) (-h)
      = shiftDistance (Fintype.piFinset fun _ : Fin d ↦ shiftBox N h)
          (fun g ↦ cubeF d N g ^ 2) (-h) := by
  have hcast : (((gridM N + N : ℕ) : ℤ)) = (gridM N : ℤ) + (N : ℤ) := by
    push_cast
    ring
  have hsub : (Fintype.piFinset fun _ : Fin d ↦ shiftBox N h) ⊆ nearBox d N := by
    intro x hx
    rw [Fintype.mem_piFinset] at hx
    rw [nearBox, Fintype.mem_piFinset]
    intro k
    have hk := hx k
    rw [shiftBox] at hk
    rw [Finset.mem_union] at hk
    rw [hcast, Finset.mem_Icc, ← abs_le]
    rcases hk with hk | hk
    · rw [Finset.mem_Icc] at hk
      calc |x k| ≤ (gridM N : ℤ) := abs_le.mpr hk
        _ ≤ (gridM N : ℤ) + (N : ℤ) := le_add_of_nonneg_right (Int.natCast_nonneg N)
    · rw [Finset.mem_biUnion] at hk
      obtain ⟨k', -, hk'⟩ := hk
      rw [Finset.mem_map] at hk'
      obtain ⟨a, ha, hax⟩ := hk'
      rw [Finset.mem_Icc] at ha
      have hax' : a + h k' = x k := by simpa using hax
      rw [← hax']
      calc |a + h k'| ≤ |a| + |h k'| := abs_add_le _ _
        _ ≤ (gridM N : ℤ) + (N : ℤ) :=
            add_le_add (abs_le.mpr ha) (hh k')
  have hzero : ∀ x ∈ nearBox d N,
      x ∉ Fintype.piFinset (fun _ : Fin d ↦ shiftBox N h) →
      |(fun g ↦ cubeF d N g ^ 2) (x + -h) - (fun g ↦ cubeF d N g ^ 2) x| = 0 := by
    intro x _ hxnot
    obtain ⟨k, hk⟩ : ∃ k, x k ∉ shiftBox N h := by
      by_contra hcon
      have hcon' : ∀ k, x k ∈ shiftBox N h := fun k => by
        by_contra hk
        exact hcon ⟨k, hk⟩
      exact hxnot (by rw [Fintype.mem_piFinset]; exact hcon')
    have hlt : (gridM N : ℤ) < |x k| := by
      by_contra hle
      have hle' : |x k| ≤ (gridM N : ℤ) := not_lt.mp hle
      exact hk (by
        rw [shiftBox]
        exact Finset.mem_union.mpr
          (Or.inl (by rw [Finset.mem_Icc]; exact abs_le.mp hle')))
    have hFx : cubeF d N x = 0 := by
      rw [cubeF]
      refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
      by_contra hne
      have hmem := support_gridF_subset N hne
      have hcoord : -(gridM N : ℤ) ≤ x k ∧ x k ≤ (gridM N : ℤ) := by
        simpa only [Finset.mem_coe, Finset.mem_Icc] using hmem
      exact absurd (abs_le.mpr hcoord) (not_le.mpr hlt)
    have hFx' : cubeF d N (x + -h) = 0 := by
      rw [cubeF]
      refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
      have harg : (x + -h) k = x k - h k := by
        rw [Pi.add_apply, Pi.neg_apply]
        ring
      rw [harg]
      by_contra hne
      have hmem := support_gridF_subset N hne
      exact hk (by
        rw [shiftBox]
        refine Finset.mem_union.mpr (Or.inr ?_)
        rw [Finset.mem_biUnion]
        exact ⟨k, Finset.mem_univ k, by
          rw [Finset.mem_map]
          exact ⟨x k - h k, by simpa only [Finset.mem_coe] using hmem, by simp⟩⟩)
    simp [hFx, hFx']
  have hsum : (∑ x ∈ Fintype.piFinset (fun _ : Fin d ↦ shiftBox N h),
      |(fun g ↦ cubeF d N g ^ 2) (x + -h) - (fun g ↦ cubeF d N g ^ 2) x|)
      = ∑ x ∈ nearBox d N,
          |(fun g ↦ cubeF d N g ^ 2) (x + -h) - (fun g ↦ cubeF d N g ^ 2) x| :=
    Finset.sum_subset hsub hzero
  unfold shiftDistance
  rw [hsum]

/-- **k4.2's quadratic bound, on the uniform box**: for every admissible shift
`|h k| ≤ N`, the square of the product weight's shift distance is bounded by
`(Σ k, ((h k)/N)²) / 12` over `nearBox d N` — the box that does not depend on `h`.

This is the form k4.3's transport consumes: `shiftDistance_cubeF_sq_le` (k4.2) over
`shiftBox N h`, read back on `nearBox` through `shiftDistance_nearBox_eq_shiftBox`. -/
lemma shiftDistance_cubeF_sq_le_nearBox {d N : ℕ} (hN : 0 < N) {h : Fin d → ℤ}
    (hh : ∀ k, |h k| ≤ (N : ℤ)) :
    shiftDistance (nearBox d N) (fun g ↦ cubeF d N g ^ 2) (-h) ^ 2
      ≤ (∑ k, ((h k : ℝ) / N) ^ 2) / 12 := by
  rw [shiftDistance_nearBox_eq_shiftBox h hh]
  exact shiftDistance_cubeF_sq_le hN h

/-- **Lemma 1.5 (Karingula–Lovett), the lake's form**: for `N > 0` there exist a `Finset`
`S` of the real grid and a weight `P` on it — positive, of mass `1`, supported in
`[-6, 6]^d` (`∀ x, P x ≠ 0 → ‖x‖ ≤ 6`), of **zero mean**
(`∀ i, coordMomentReal P S i = 0`) — such that for every `g : Fin d → ℤ` whose normalised
shift has norm at most `1`, the shift distance between `P` and its translate by `g / N` is
at most `1/3`.

The weight is `cubeF d N ^ 2` pushed along `gridEmb d N` (`g ↦ g / N`), the support is
the image of `nearBox d N`: the first four components are read off the k2.3 organs
(`push_apply`, `push_mass`, the support of `Komlos.Grid`) and off symmetry (`nearBox_neg`,
`cubeF_neg`), the fifth off `shiftDistanceTV_push` (k4.2c) and k4.2's bound read back on
`nearBox`.

In the oracle the first component is `IsDist P` — a vocabulary this lake does not have
(convention k1.1): it is written here in the clear (pointwise positivity and mass), as the
mean is, coordinate by coordinate. -/
theorem exists_nearInvariant {d N : ℕ} (hN : 0 < N) :
    ∃ (S : Finset (Fin d → ℝ)) (P : (Fin d → ℝ) → ℝ),
      (∀ x ∈ S, 0 ≤ P x) ∧
      (∑ x ∈ S, P x) = 1 ∧
      (∀ x, P x ≠ 0 → ‖x‖ ≤ 6) ∧
      (∀ i, coordMomentReal P S i = 0) ∧
      ∀ g : Fin d → ℤ, (∑ k, ((g k : ℝ) / N) ^ 2) ≤ 1 →
        shiftDistanceTV S P (gridEmb d N g) ≤ 3⁻¹ := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set F : (Fin d → ℤ) → ℝ := fun g ↦ cubeF d N g ^ 2 with hF_def
  have he : Function.Injective (gridEmb d N) := gridEmb_injective hN
  refine ⟨(nearBox d N).map ⟨⇑(gridEmb d N), he⟩, push (gridEmb d N) F,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨g, -, rfl⟩ := hx
    show 0 ≤ push (gridEmb d N) F (gridEmb d N g)
    rw [push_apply (gridEmb d N) he F g, hF_def]
    exact sq_nonneg _
  · have hK : Function.support (gridF N) ⊆
        Icc (-(((gridM N + N : ℕ) : ℤ))) ((gridM N + N : ℕ) : ℤ) := by
      intro j hj
      have h1 : -(gridM N : ℤ) ≤ j ∧ j ≤ (gridM N : ℤ) := by
        simpa only [Finset.mem_coe, Finset.mem_Icc] using support_gridF_subset N hj
      have hcast : (((gridM N + N : ℕ) : ℤ)) = (gridM N : ℤ) + (N : ℤ) := by
        push_cast
        ring
      refine Finset.mem_coe.mpr ?_
      rw [Finset.mem_Icc, hcast]
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
    rw [push_mass (gridEmb d N) he F (nearBox d N), hF_def]
    rw [nearBox]
    exact sum_cubeF_sq hN hK
  · intro x hx
    have hrange : ∃ g, gridEmb d N g = x := by
      by_contra hcon
      have hcon' : ∀ g, gridEmb d N g ≠ x := fun g hg => hcon ⟨g, hg⟩
      exact hx (push_eq_zero (gridEmb d N) F hcon')
    obtain ⟨g, rfl⟩ := hrange
    rw [push_apply (gridEmb d N) he F g] at hx
    have hgne : cubeF d N g ≠ 0 := by
      intro h0
      apply hx
      rw [hF_def]
      simp [h0]
    have hcoord : ∀ k, |g k| ≤ (gridM N : ℤ) := by
      intro k
      have hk : gridF N (g k) ≠ 0 := by
        intro h0
        exact hgne (by rw [cubeF]; exact Finset.prod_eq_zero (Finset.mem_univ k) h0)
      have hmem := support_gridF_subset N hk
      have hmem' : -(gridM N : ℤ) ≤ g k ∧ g k ≤ (gridM N : ℤ) := by
        simpa only [Finset.mem_coe, Finset.mem_Icc] using hmem
      exact abs_le.mpr hmem'
    refine (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)).mpr ?_
    intro k
    have h1 : |(g k : ℝ)| ≤ (gridM N : ℝ) := by
      rw [← Int.cast_abs]
      exact_mod_cast hcoord k
    rw [Real.norm_eq_abs, gridEmb_apply, abs_div, abs_of_nonneg hNpos.le,
      div_le_iff₀ hNpos]
    calc |(g k : ℝ)| ≤ (gridM N : ℝ) := h1
      _ = 6 * (N : ℝ) := cast_gridM N
  · intro i
    rw [coordMomentReal_push (gridEmb d N) he F (nearBox d N) i]
    have h1 : (∑ g ∈ nearBox d N, F g * gridEmb d N g i)
        = ∑ g ∈ nearBox d N, F (-g) * gridEmb d N (-g) i := by
      conv_lhs => rw [← nearBox_neg]
      rw [Finset.sum_map]
      exact Finset.sum_congr rfl fun g _ => rfl
    have h2 : (∑ g ∈ nearBox d N, F (-g) * gridEmb d N (-g) i)
        = -∑ g ∈ nearBox d N, F g * gridEmb d N g i := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun g _ => by
        have hFg : F (-g) = F g := by
          rw [hF_def]
          simp only [cubeF_neg]
        rw [hFg, map_neg, Pi.neg_apply]
        ring
    have h3 : (∑ g ∈ nearBox d N, F g * gridEmb d N g i)
        = -∑ g ∈ nearBox d N, F g * gridEmb d N g i := h1.trans h2
    linarith
  · intro g hg
    have hhk : ∀ k, |g k| ≤ (N : ℤ) := by
      intro k
      have h1 : ((g k : ℝ) / N) ^ 2 ≤ 1 :=
        le_trans (Finset.single_le_sum (f := fun k ↦ ((g k : ℝ) / N) ^ 2)
          (fun i _ ↦ sq_nonneg _) (Finset.mem_univ k)) hg
      have h1' : ((g k : ℝ) / N) ^ 2 ≤ (1 : ℝ) ^ 2 := by simpa using h1
      have h2 : |(g k : ℝ) / N| ≤ 1 := by simpa using sq_le_sq.mp h1'
      have h3 : |(g k : ℝ)| / (N : ℝ) ≤ 1 := by
        simpa [abs_div, abs_of_pos hNpos] using h2
      have h4 : |(g k : ℝ)| ≤ (N : ℝ) := by
        simpa using (div_le_iff₀ hNpos).mp h3
      have h5 : ((|g k| : ℤ) : ℝ) ≤ ((N : ℕ) : ℝ) := by
        rw [Int.cast_abs]
        exact h4
      exact_mod_cast h5
    have hb := shiftDistance_cubeF_sq_le_nearBox (d := d) (N := N) hN (h := -g)
      (fun k => by simpa using hhk k)
    rw [neg_neg] at hb
    have hsum : (∑ k, (((-g) k : ℝ) / N) ^ 2) = ∑ k, ((g k : ℝ) / N) ^ 2 := by
      refine Finset.sum_congr rfl fun k _ => by
        rw [Pi.neg_apply, Int.cast_neg]
        ring
    have hbound : (∑ k, ((g k : ℝ) / N) ^ 2) / 12 ≤ (3⁻¹ : ℝ) ^ 2 := by
      have hdiv : (∑ k, ((g k : ℝ) / N) ^ 2) / 12 ≤ 1 / 12 :=
        div_le_div_of_nonneg_right hg (by norm_num)
      have hc : (1 : ℝ) / 12 ≤ (3⁻¹ : ℝ) ^ 2 := by norm_num
      linarith
    have hsq : shiftDistance (nearBox d N) F g ^ 2 ≤ (3⁻¹ : ℝ) ^ 2 := by
      refine hb.trans ?_
      rw [hsum]
      exact hbound
    have hfin : shiftDistance (nearBox d N) F g ≤ 3⁻¹ := by
      have hnn : (0 : ℝ) ≤ shiftDistance (nearBox d N) F g :=
        shiftDistance_nonneg (nearBox d N) F g
      have := sq_le_sq.mp hsq
      rwa [abs_of_nonneg hnn, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3⁻¹)] at this
    rw [shiftDistanceTV_push (gridEmb d N) he (nearBox d N) F g,
      ← shiftDistance_eq_shiftDistanceTV (nearBox d N) F g]
    exact hfin

/-! ## Adaptation note (brick k4.3)

**Status**: 17 bricks closed — the oracle's `Komlos/NearInvariant.lean` is carried over
**in full**, and Lemma 1.5 is now a theorem of the lake. The k4 campaign is complete: the
product weight (k4.2a), its distance bound (k4.2b), the transport of the shift (k4.2c) and
the near-invariant distribution (k4.3) form a closed chain, `exists_nearInvariant`
consuming **only** closed bricks.

**What changed relative to the oracle**:

1. **The support is uniform, not canonical.** The oracle lets the support follow the
   `Finsupp`; the lake makes it existential, hence **independent of the shift**: that is
   `nearBox d N` (`[-7N, 7N]^d`), which dominates `shiftBox N h` for every admissible `h`
   and over which the shift distance **is** the one of `shiftBox`
   (`shiftDistance_nearBox_eq_shiftBox`). The price of uniformity is a `+N` on the box —
   visible in the module's statement, invisible in its conclusions.
2. **`IsDist` is written in the clear** (pointwise positivity, mass 1) — the vocabulary
   stays outside the lake since k1.1, as k2.5 arbitrated for `mean_mem_convexHull`.
3. **`sum_smul_eq_zero_of_neg` (the oracle's generic `Finsupp` lemma) is not carried over
   as such**: its substance — an even weight on a symmetric box has a vanishing
   coordinate moment — is proved directly by re-indexing `Finset.sum_map` along negation
   (`nearBox_neg`, `cubeF_neg`), without `equivMapDomain` or `Finsupp.sum_neg`, which have
   no object here.
4. **The mean is read coordinate by coordinate** (`coordMomentReal`, k2.3) — the real grid
   has no vector `mean` in this lake, it has moments.

**What the lemma does not do**: it does not compute the shift distance, it **bounds** it —
`≤ 3⁻¹` comes from k4.2's bound (`≤ (Σ k, ((g k)/N)²)/12 ≤ 1/12`) through the square root;
and it does not choose the point `g`: the statement quantifies over **every** admissible
`g`, which is exactly the strength the assembly will consume.

**Verification**: `lake build Discrepancy.Komlos.NearInvariant` (module + twin),
0 `sorry`, `distinct_code_sorry = 0` on the lake. -/

end Discrepancy.Komlos_en