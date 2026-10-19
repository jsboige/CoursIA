/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted to `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, i18n convention #4980.

The original Dahia source lives in the `gdahia/Komlos` repository (module
`Komlos/Cube.lean`, toolchain v4.34.0, `Finsupp` framework over `E → ₀ ℝ`).
The adaptation follows the lake convention (explicit `Finset` support,
established by the k1.1 tranche `ShiftDistance.lean`): the product weight
`cubeF d N` is a **function** `(Fin d → ℤ) → ℝ` — as `gridF` is in one
dimension —, its support is a **box** described by `Fintype.piFinset`, and the
mass is computed on any `Finset` containing the translated support.

**Scope of this commit** (k4.2a tranche, `lake build SUCCESS` required, 0 `sorry`):

Closed bricks: `cubeF`, `support_cubeF_sub_subset`, `support_cubeF_subset`,
`sum_cubeF_sub_mul_cubeF_sub` (the correlation of two translates is the
product of their coordinate correlations),
`sum_cubeF_sub_sq` (mass `1` of the product weight, translated or not),
`sum_cubeF_sq`, `shiftBox`, `support_gridF_subset_shiftBox`,
`support_gridF_sub_subset_shiftBox`.

**Delivered by k4.2b**: the oracle's bound `shiftDist_cubeP_sq_le`
(`shiftDist (cubeP d N) h ^ 2 ≤ (∑ k, (h k / N) ^ 2) / 12`), under the name
`shiftDistance_cubeF_sq_le`. It consumes the "distribution" version of the
Hellinger inequality (`tvDist_sq_le` in Dahia) — deferred by `Hellinger.lean`
until this module fixed its call — now delivered by `Komlos/TvDistance.lean`
(k4.2b, same commit). Remains the chain `Cube` → `NearInvariant` (Lemma 1.5,
k4.3 tranche: the transport from the integer lattice to the grid
`N⁻¹ • ℤ^d`), which awaits `shiftDist_push` (k2.3's only deferral).

The detailed state lives in `FORMAL_STATUS.md` (« Distillation
Karingula–Lovett, briques k1..k5 »).
-/

import Discrepancy.Komlos.Grid_en
import Discrepancy.Komlos.TvDistance_en

/-!
# A product weight on the integer lattice (Lemma 1.5, Karingula–Lovett)

`cubeF d N g = ∏ k, gridF N (g k)` is the product of `d` copies of the
normalised one-dimensional weight `gridF N` (k3.2 tranche). Its square is a
probability on `ℤ^d` — total mass `1`, computed on any `Finset` containing the
translated support — and its support is contained in the box
`[-6N, 6N]^d`.

This is the object Lemma 1.5 transports to the grid `N⁻¹ • ℤ^d` through the
coordinatewise map `g ↦ g / N`.
-/

namespace Discrepancy.Komlos_en

open Finset

/-- The `d`-dimensional product weight on the integer lattice: the product of
the `d` coordinates of the normalised one-dimensional weight `gridF N`. -/
noncomputable def cubeF (d N : ℕ) (g : Fin d → ℤ) : ℝ := ∏ k, gridF N (g k)

/-- The support of a **translate** of `cubeF` is contained in the box `K^d`,
as soon as `K` contains the support of every `gridF N (· - a k)`. -/
lemma support_cubeF_sub_subset {d N : ℕ} {a : Fin d → ℤ} {K : Finset ℤ}
    (hK : ∀ k, Function.support (fun j ↦ gridF N (j - a k)) ⊆ K) :
    Function.support (fun g ↦ cubeF d N (g - a)) ⊆
      (Fintype.piFinset fun _ : Fin d ↦ K : Set (Fin d → ℤ)) := by
  intro g hg
  rw [mem_coe, Fintype.mem_piFinset]
  intro k
  exact hK k (prod_ne_zero_iff.1 hg k (mem_univ k))

/-- The support of `cubeF` is contained in the box `K^d`, as soon as `K`
contains the support of `gridF N`. -/
lemma support_cubeF_subset {d N : ℕ} {K : Finset ℤ} (hK : Function.support (gridF N) ⊆ K) :
    Function.support (cubeF d N) ⊆
      (Fintype.piFinset fun _ : Fin d ↦ K : Set (Fin d → ℤ)) := by
  intro g hg
  refine support_cubeF_sub_subset (N := N) (a := 0) ?_ ?_
  · intro k
    simpa only [Pi.zero_apply, sub_zero] using hK
  · simpa only [sub_zero] using hg

/-- The correlation of two translates of `cubeF` — an unnormalised scalar
product — is the product of their coordinatewise correlations. This is the
factorisation the `L²` bound of the k4.2b tranche will rely on: each
coordinate is handled independently. -/
lemma sum_cubeF_sub_mul_cubeF_sub (d N : ℕ) (K : Finset ℤ) (a b : Fin d → ℤ) :
    ∑ g ∈ Fintype.piFinset (fun _ : Fin d ↦ K),
        cubeF d N (g - a) * cubeF d N (g - b)
      = ∏ k, ∑ j ∈ K, gridF N (j - a k) * gridF N (j - b k) := by
  simp [Finset.prod_univ_sum, cubeF, Finset.prod_mul_distrib]

/-- The square of the translate of `cubeF` by `a` has total mass `1` — the
product measure is a probability. The sum is computed on any `Finset`
containing the support of the translate. -/
lemma sum_cubeF_sub_sq {d N : ℕ} (hN : 0 < N) (a : Fin d → ℤ) {K : Finset ℤ}
    (hK : ∀ k, Function.support (fun j ↦ gridF N (j - a k)) ⊆ K) :
    ∑ g ∈ Fintype.piFinset (fun _ : Fin d ↦ K), cubeF d N (g - a) ^ 2 = 1 := by
  simp_rw [sq, sum_cubeF_sub_mul_cubeF_sub, ← sq, sum_gridF_sub_sq hN _ (hK _),
    prod_const_one]

/-- The square of `cubeF` has total mass `1`, without a translation. -/
lemma sum_cubeF_sq {d N : ℕ} (hN : 0 < N) {K : Finset ℤ}
    (hK : Function.support (gridF N) ⊆ K) :
    ∑ g ∈ Fintype.piFinset (fun _ : Fin d ↦ K), cubeF d N g ^ 2 = 1 := by
  simpa only [sub_zero] using
    sum_cubeF_sub_sq (d := d) (N := N) hN (0 : Fin d → ℤ) (K := K)
      (fun _ ↦ by simpa only [Pi.zero_apply, sub_zero] using hK)

/-- A `Finset` containing the support of `gridF N` **and** that of all its
translates by the `h k` — the working box of the k4.2b tranche. -/
noncomputable def shiftBox {d : ℕ} (N : ℕ) (h : Fin d → ℤ) : Finset ℤ :=
  Icc (-(gridM N : ℤ)) (gridM N) ∪
    univ.biUnion fun k ↦
      (Icc (-(gridM N : ℤ)) (gridM N)).map (Equiv.addRight (h k)).toEmbedding

/-- The support of `gridF N` is contained in the working box `shiftBox`. -/
lemma support_gridF_subset_shiftBox {d : ℕ} (N : ℕ) (h : Fin d → ℤ) :
    Function.support (gridF N) ⊆ shiftBox N h :=
  (support_gridF_subset N).trans (by simp [shiftBox])

/-- The support of every translate `gridF N (· - h k)` is contained in the
working box `shiftBox`. -/
lemma support_gridF_sub_subset_shiftBox {d : ℕ} (N : ℕ) (h : Fin d → ℤ) (k : Fin d) :
    Function.support (fun j ↦ gridF N (j - h k)) ⊆ shiftBox N h := by
  intro j hj
  simp only [shiftBox, coe_union, coe_biUnion, coe_map, Set.mem_union, Set.mem_iUnion]
  right
  exact ⟨k, mem_coe.2 (mem_univ k), j - h k, support_gridF_subset N hj, by simp⟩

/-- The squared shift of the product weight `cubeF d N ^ 2` is at most
`(∑ k, ((h k) / N) ^ 2) / 12`.

This is the oracle's `shiftDist_cubeP_sq_le` — the **last** brick of boute
k4.2: the total variation between the product distribution and its translate is
quadratically small, which is exactly the form Lemma 1.5 (k4.3) then
transports to the grid `N⁻¹ • ℤ^d`.

`h` is the shift of the **weight** (the translate being `cubeF d N (· - h)`),
so the corresponding `shiftDistance` shift is `-h` (the
`½ · Σ |P (x + u) − P x|` convention of k1.1). The zero shift is the case
`h = 0`.

The `Finset` over which `shiftDistance` sums is the **box**
`(shiftBox N h)^d` (`Fintype.piFinset`): it is the explicit analogue of the
support the oracle leaves implicit — `shiftDist` sums over the support of
`cubeP - tr h cubeP`, which is contained in that box
(`support_cubeF_sub_subset`, k4.2a).

Proof: `tvDistance_sq_le` (k4.2b) reduces the total variation to the `L²`
distance between the weights, `sum_cubeF_sub_mul_cubeF_sub` (k4.2a) factors the
correlation over the coordinates, `one_sub_sum_le_prod` (k4.1, Weierstrass)
turns the additive bound into a bound on the product, and
`sum_gridF_sub_sq_le` (k3.2) supplies the one-dimensional bound. -/
lemma shiftDistance_cubeF_sq_le {d N : ℕ} (hN : 0 < N) (h : Fin d → ℤ) :
    shiftDistance (Fintype.piFinset fun _ : Fin d ↦ shiftBox N h)
      (fun g ↦ cubeF d N g ^ 2) (-h) ^ 2
      ≤ (∑ k, ((h k : ℝ) / N) ^ 2) / 12 := by
  set K := shiftBox N h
  set A : Fin d → ℝ := fun k ↦ ∑ j ∈ K, gridF N j * gridF N (j - h k)
  have hp : ∑ g ∈ Fintype.piFinset (fun _ ↦ K), cubeF d N (g - 0) ^ 2 = 1 :=
    sum_cubeF_sub_sq hN 0 (fun k ↦ by
      simpa only [Pi.zero_apply, sub_zero] using support_gridF_subset_shiftBox N h)
  have hq : ∑ g ∈ Fintype.piFinset (fun _ ↦ K), cubeF d N (g - h) ^ 2 = 1 :=
    sum_cubeF_sub_sq hN h (support_gridF_sub_subset_shiftBox N h)
  rw [shiftDistance_eq_tvDistance, tvDistance_comm]
  refine (tvDistance_sq_le (s := Fintype.piFinset (fun _ ↦ K))
    (p := fun g ↦ cubeF d N (g - 0)) (q := fun g ↦ cubeF d N (g - h))
    ?_ ?_ hp hq).trans ?_
  · intro g _
    simp only [sub_zero]
  · intro g _
    simp only [sub_eq_add_neg]
  · rw [sum_sub_sq_eq hp hq, sum_cubeF_sub_mul_cubeF_sub]
    simp only [Pi.zero_apply, sub_zero]
    refine le_trans (b := ∑ k, 2 * (1 - A k)) ?_ ?_
    · suffices 1 - ∏ k, A k ≤ ∑ k, (1 - A k) by
        simpa only [Finset.mul_sum, mul_sub, mul_one] using
          mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 2)
      rw [sub_le_comm]
      refine (one_sub_sum_le_prod univ (fun k ↦ 1 - A k) ?_ ?_).trans_eq ?_
      · intro k _
        apply sub_nonneg.mpr
        apply (Real.sum_mul_le_sqrt_mul_sqrt K (gridF N) (fun j ↦ gridF N (j - h k))).trans
        rw [sum_gridF_sq hN (support_gridF_subset_shiftBox N h),
          sum_gridF_sub_sq hN (h k) (support_gridF_sub_subset_shiftBox N h k),
          Real.sqrt_one, mul_one]
      · intro k _
        exact sub_le_self _ (sum_nonneg fun j _ ↦
          mul_nonneg (gridF_nonneg N j) (gridF_nonneg N (j - h k)))
      · simp only [sub_sub_cancel]
    · rw [sum_div]
      refine sum_le_sum ?_
      intro k _
      rw [mul_sub, mul_one, ← sum_sub_sq_eq
        (sum_gridF_sq hN (support_gridF_subset_shiftBox N h))
        (sum_gridF_sub_sq hN (h k) (support_gridF_sub_subset_shiftBox N h k))]
      simpa only [div_pow, div_div, mul_comm (12 : ℝ)] using
        sum_gridF_sub_sq_le hN (h k) K

/-! ## Adaptation note (k4.2 tranche)

**Status**: 10 bricks closed — the oracle's `Komlos/Cube.lean` is ported **in
full**. The `d`-dimensional product weight exists, its support is a box, its
correlation factors over the coordinates, its mass is `1`, and its shift is
quadratically small (`shiftDistance_cubeF_sq_le`, the second half of the boute,
delivered by k4.2b).

**Encoding barrier, crossed by the lake convention.** The oracle states
`cubeP d N : (Fin d → ℤ) →₀ ℝ` (a `Finsupp` supported on
`Fintype.piFinset (fun _ ↦ Icc (-(gridM N)) (gridM N))`) and writes its mass
through `IsDist`/`mass_eq_sum`. This lake has neither `IsDist` nor `Finsupp`
in its Komlos chain: the weight is a **function** and the support is
**passed** (the `shiftDistance S P u` convention of k1.1). Nothing is lost —
`sum_cubeF_sub_sq` is the exact mass statement, on any `Finset` containing the
support — and the gain is that k4.2b consumes `shiftDistance` as it stands,
without a `Finsupp → Finset` bridge.

**v4.34 → v4.33.0 port, proof by proof**:

- v4.34 module syntax (`module`, `public import`, `@[expose] public section`)
  is dropped — plain Lean 4 imports.
- `support_cubeF_sub_subset`, `support_cubeF_subset`,
  `sum_cubeF_sub_mul_cubeF_sub`, `sum_cubeF_sub_sq`: verbatim port of the
  oracle (`prod_ne_zero_iff`, `Fintype.mem_piFinset`, `Finset.prod_univ_sum`,
  `Finset.prod_mul_distrib`, `prod_const_one`), the only systematic
  substitution being `Finsupp.onFinset` → explicit `Finset`.
- `shiftBox`: the oracle's `noncomputable` is kept (the indexed union goes
  through `Fintype`/`DecidableEq` on `Fin d`).
- `sum_cubeF_sq` has no counterpart in the oracle: it is the
  "no translation" form of `sum_cubeF_sub_sq`, written here because k4.2b
  uses it (`a = 0`, the untranslated copy).
- `shiftDistance_cubeF_sq_le` (k4.2b): port of `shiftDist_cubeP_sq_le`. Two
  deviations only, both **by disappearance** — the oracle passes six arguments
  to `tvDist_sq_le` (the two support hypotheses `hPs`/`hQs`, then `hP`, `hQ`,
  `hp`, `hq`), this module four (the support hypotheses are absorbed by the
  explicit sum over `Fintype.piFinset K`); and the shift is written `-h` where
  `shiftDist (cubeP d N) h` carries `h` in its argument, the
  `P (· + u) − P` orientation of `shiftDistance` (k1.1) being the reverse of
  that of `tr h P`. The proof body is verbatim.

The detailed state lives in `FORMAL_STATUS.md` (« Distillation Karingula–Lovett »).
-/

end Discrepancy.Komlos_en