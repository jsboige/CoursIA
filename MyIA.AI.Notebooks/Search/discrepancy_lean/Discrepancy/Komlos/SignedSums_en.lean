/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted for `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979): toolchain v4.33.0, Mathlib `db584cd6`, i18n convention #4980.

The original Dahia source lives in the `gdahia/Komlos` repository (module
`Komlos/SignedSums.lean`, toolchain v4.34.0, `Finsupp` framework over
`E →₀ ℝ`). The final assembly — the `induction n with` iteration of
Lemma 1.4 — reads there at l.37-58. This lake module carries the whole
distillation: the first brick `sum_smul_inl` ships here in generic form
(k2.6, the consumption map of the organs measured at the top of the module,
the framework decision — option (c) — arbitrated in k2.6a), then the final
assembly itself (k2.6c): the real square `snocReal`, the hull transport
`mem_convexHull_map_snocReal`, the two-set inductive gate
`exists_colouring_aux` (closure `S` + exact support `E` — the `Finset`
price of the oracle's canonical `Finsupp` support) and the public statement
`exists_isColouring_mean_add_sum_mem_convexHull`.

Scope caveat lifted (measurement k5.2, #21417 step 2): the form delivered on
10-06 was only instantiable for an identically zero family `v` — its
contention hypotheses on a stable `Finset` forced `v i = 0`
(`contention_stability_forces_zero`, further down in this file, with the
measured argument). The public statement and the inductive gate now carry a
clause set `B` (bounded signed sums of the generators, satisfiable by a large
box, no stability required): k2 is closed as a proof **and** as an
instantiable statement. See the k2.6c and k5.2 rows of `FORMAL_STATUS.md`.
-/

import Discrepancy.Basic_en
import Discrepancy.Komlos.Containment_en
import Discrepancy.Komlos.Distribution_en
import Discrepancy.Komlos.Lift_en
import Discrepancy.Komlos.LiftSplit_en
import Discrepancy.Komlos.Pullback_en
import Discrepancy.Komlos.Split_en

/-!
# Signed sums — assembly of Lemma 1.4 (brick k2.6)

The goal of this module is the final assembly of the elementary route
(Karingula–Lovett): the `induction n with` iteration of the
`gdahia/Komlos` oracle (`SignedSums.lean` l.37-58), which consumes
`mean_mem_convexHull` in the base case (l.42), `mean_split` +
`sum_smul_inl` in the step (l.53), and `pullback` in the closing (l.55).

## Genericity map (measured on 2026-10-06, k2.5 tip 87b4f35871)

The oracle's induction re-instantiates its organs at every level on a
growing ambient `E → E × ℝ → (E × ℝ) × ℝ → …` — it is the generality of
`E` that absorbs the growth. The lake's k2.0–k2.5 organs are monomorphic
(`Fin d → ℤ`, height `Bool`):

| Oracle organ | Our lake | Status |
|---|---|---|
| `split : (E →₀ ℝ) → (E × ℝ →₀ ℝ)` | `Split.split` (`Fin d → ℤ`, `× Bool`) | monomorphic |
| `mean_split` (barycenter preserved) | `MeanSplit.mean_split_of_support` | monomorphic |
| `shiftDist_split_le` | acquired k1.6 | monomorphic |
| `splitBit_eq` | `SplitBit` | monomorphic |
| `pullback` (generic) | `Pullback.pullback` (`toReal`/`toRealProd`) | monomorphic |
| `mean_mem_convexHull` | `Distribution.mean_mem_convexHull` (k2.5) | monomorphic |
| `sum_smul_inl` | **missing — shipped below, generic** | ✓ k2.6 |
| convexHull (`add_smul`/`sum_smul`/`mem_convexHull'`) | `Pullback` l.150/189/213 | ✓ generic |

The architectural gap is **arbitrated in k2.6a** (option (c): the growing
space is realized as `Fin (d + k) → ℤ` via the `liftUp` embedding,
without re-generalizing the organs — route α is set aside, route β
(two-space ping-pong) is closed by measurement). `sum_smul_inl` remains
the generic ℝ-modular organ, **complementary to `sum_smul_snoc`**
(k2.6a, lake form on the grid side): consumable on the transport/hull
side, where the moments live in `ℝ`.
-/

namespace Discrepancy.Komlos_en

/-- The left component of a sum of vectors `ε i • (v i, 0)` is the sum
of the left components — the `Finset` counterpart of the oracle's
`sum_smul_inl` (`split.lean` l.50), used by the rewrite `rw [mean_split,
sum_smul_inl, …]` of the inductive step. Generic in `E`: it is the only
organ of the step the lake did not have, and it does not depend on the
grid. -/
lemma sum_smul_inl {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (ε : Fin n → ℝ) (v : Fin n → E) :
    (∑ i, ε i • (v i, (0 : ℝ))) = (∑ i, ε i • v i, (0 : ℝ)) := by
  refine Prod.ext ?_ ?_ <;> simp [Prod.smul_mk, Prod.fst_sum, Prod.snd_sum]

/-! ### Brick k2.6c: the final assembly — the Lemma 1.4 induction -/

/-- **The real-side `snoc` isomorphism**: `(Fin d → ℝ) × ℝ → (Fin (d+1) → ℝ)`,
`(z, t) ↦ snoc z t`. It is the real form of the level bridge: the square
`toReal ∘ liftUp = snoc ∘ toRealProd` (cf `toReal_liftUp`, k2.6a) says that
transporting the pushed support into the grown dimension amounts to
`snoc`-ing the transported product support — and that is how the induction
conclusion at dimension `d+1` feeds the k2.4 `pullback`, stated in
`(Fin d → ℝ) × ℝ`. -/
def snocReal {d : ℕ} : ((Fin d → ℝ) × ℝ) → (Fin (d + 1) → ℝ) :=
  fun p => Fin.snoc p.1 p.2

lemma snocReal_apply_castSucc {d : ℕ} (p : (Fin d → ℝ) × ℝ) (j : Fin d) :
    snocReal p j.castSucc = p.1 j := by simp [snocReal]

lemma snocReal_apply_last {d : ℕ} (p : (Fin d → ℝ) × ℝ) :
    snocReal p (Fin.last d) = p.2 := by simp [snocReal]

/-- **The real square**: `snocReal (toRealProd y) = toReal (liftUp y)` —
the combined reading of `toReal_liftUp` (k2.6a) and of the definition
`toRealProd` (k2.4). It is the only equation missing from the hull
transport between the two readings of the grown dimension. -/
lemma snocReal_toRealProd {d : ℕ} (y : (Fin d → ℤ) × Bool) :
    snocReal (toRealProd y) = toReal (liftUp y) := by
  rw [toReal_liftUp]
  funext j
  simp [snocReal, toRealProd]

lemma snocReal_injective {d : ℕ} : Function.Injective (snocReal (d := d)) := by
  rintro ⟨z₁, t₁⟩ ⟨z₂, t₂⟩ h
  have h1 : z₁ = z₂ := by
    funext j
    have := congrFun h j.castSucc
    simpa [snocReal] using this
  have h2 : t₁ = t₂ := by
    have := congrFun h (Fin.last d)
    simpa [snocReal] using this
  exact Prod.ext h1 h2

/-- The `Finset.Embedding` version of `snocReal`, for the `Finset.map`s of
the transported supports. -/
def snocRealEmb {d : ℕ} : ((Fin d → ℝ) × ℝ) ↪ (Fin (d + 1) → ℝ) :=
  ⟨snocReal, snocReal_injective⟩

lemma snocRealEmb_apply {d : ℕ} (p : (Fin d → ℝ) × ℝ) : snocRealEmb p = snocReal p := rfl

/-- `snocReal` as an `ℝ`-linear map. This is the structure that transports
convex hulls: `LinearMap.image_convexHull` identifies the hull of the image
with the image of the hull, and injectivity restores the point — the
transport lemma below follows immediately. -/
def snocLM {d : ℕ} : ((Fin d → ℝ) × ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ) where
  toFun p := snocReal p
  map_add' p q := by
    funext j
    induction j using Fin.lastCases with
    | last => simp [snocReal, Fin.snoc_last, Pi.add_apply]
    | cast i => simp [snocReal, Fin.snoc_castSucc, Pi.add_apply]
  map_smul' c p := by
    funext j
    induction j using Fin.lastCases with
    | last => simp [snocReal, Fin.snoc_last, Pi.smul_apply, smul_eq_mul]
    | cast i => simp [snocReal, Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul]

/-- **Hull transport through `snoc`**: belonging to the hull of a
`snoc`-ed finite set is belonging to the hull of the source set.

This is the organ that closes the diagram square for the k2.6c assembly:
the induction hypothesis concludes in `Fin (d+1) → ℝ` (hull of the
transported pushed support), the k2.4 `pullback` consumes
`(Fin d → ℝ) × ℝ` (hull of the transported product support) — the
correspondence is exactly this transport. Proof: `snocReal` is linear
(`snocLM`) and injective, and `LinearMap.image_convexHull` commutes the
hull and the image. -/
lemma mem_convexHull_map_snocReal {d : ℕ} {E : Finset ((Fin d → ℝ) × ℝ)}
    {p : (Fin d → ℝ) × ℝ} :
    snocReal p ∈ convexHull ℝ
      (↑(E.map snocRealEmb) : Set ((Fin (d + 1) → ℝ))) ↔
      p ∈ convexHull ℝ (↑E : Set ((Fin d → ℝ) × ℝ)) := by
  have hset : (↑(E.map snocRealEmb) : Set ((Fin (d + 1) → ℝ)))
      = (⇑snocLM) '' (↑E : Set ((Fin d → ℝ) × ℝ)) := by
    rw [Finset.coe_map]
    rfl
  rw [hset, ← LinearMap.image_convexHull]
  constructor
  · rintro ⟨q, hq, hfq⟩
    rwa [snocReal_injective hfq] at hq
  · exact fun h => ⟨p, h, rfl⟩

/-! ### The inductive gate: two sets, `S` the closure and `E` the support -/

/-- **Lemma 1.4 (Karingula–Lovett), lake form — the inductive gate**.

At the oracle (`gdahia/Komlos`, `SignedSums.lean` l.37-58), the induction
lives on `Finsupp`s: the exact support is canonical at every level, and the
induction-hypothesis conclusion is consumed as-is by `pullback`. The lake's
explicit `Finset` framework must pay for that transport: the containment
`SupportContained` (k1.7) demands a support **closed under shifts of `A`**
(the displaced mass points land there), whereas the `pullback` (k2.4)
demands a hull carried by the **exact support** of the split
(`hSQ : ∀ y ∈ SQ, split v P y ≠ 0`). Those two roles are incompatible on a
single `Finset`: the gate therefore carries two — `S` (closure: mass,
moments, containment) and `E` (exact support: hull of the conclusion,
`E ⊆ S`).

At the next level, `S'` is the lifted image of the full product (containment
is transferred there by `supportContained_pushUp_split_enlarged`, the
transmission organ of overhaul #21417) and `E'` the pushed exact support
(`SQ.map liftUpEmb`, `SQ` the filter of non-zero splits). The bridge between
the two readings is the square `snocReal ∘ toRealProd = toReal ∘ liftUp`
plus the hull transport `mem_convexHull_map_snocReal` (above).

**Overhaul #21417 (fixing the k5.2 defect)**: the gate no longer carries a
set `A` stable under `± 3 • v i` — an orbit class, unsatisfiable on a
`Finset` for `v ≠ 0` (the witness `contention_stability_forces_zero` below
proves those hypotheses force `v = 0`). It carries a **clause set**: a
`Finset B` containing the signed sums with coefficients bounded by 2 in the
generators `3 • v i` (5ⁿ points, satisfiable by a large box — no stability
whatsoever is required of `B`), together with the containment
`SupportContained S P B`. The transmission equation is checked level by
level: every level-`d + 1` clause (bounded sum of the first `n` generators,
snoc'ed at height zero) lives in the shadow `(B + w) ∩ (B − w)` because its
base `z` satisfies `z ± w ∈ B` — the last generator's coefficient moves
from `0` to `± 1`, bounded by 2. -/
theorem exists_colouring_aux (n : ℕ) :
    ∀ (d : ℕ) (S E : Finset (Fin d → ℤ)) (P : (Fin d → ℤ) → ℝ),
      (∀ x, 0 ≤ P x) → (∑ x ∈ S, P x = 1) →
      (∀ x, P x ≠ 0 → x ∈ E) → E ⊆ S →
      ∀ B : Finset (Fin d → ℤ),
      ∀ v : Fin n → (Fin d → ℤ),
      (∀ f : Fin n → ℤ, (∀ i, |f i| ≤ 2) → ∑ i, f i • (3 • v i) ∈ B) →
      SupportContained S P B →
      (∀ i, shiftDistance S P (6 • v i) ≤ 3⁻¹) →
      ∃ ε : Fin n → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
        (fun j => coordMoment P S j + ∑ i, (ε i : ℝ) * (v i j : ℝ)) ∈
          convexHull ℝ
            ↑(E.map (⟨⇑toReal, toReal_injective⟩ : (Fin d → ℤ) ↪ (Fin d → ℝ))) := by
  induction n with
  | zero =>
      intro d S E P hP0 hmass hE hES B v hclauses hC hv
      have hzero : ∀ x ∈ S, x ∉ E → P x = 0 := by
        intro x _ hx
        by_contra hp
        exact hx (hE x hp)
      have hmassE : ∑ x ∈ E, P x = 1 := by
        rw [← hmass]
        exact Finset.sum_subset hES hzero
      have hmean := mean_mem_convexHull hP0 hmassE
      refine ⟨fun _ => 1, fun i => i.elim0, ?_⟩
      have hfun : (fun j => coordMoment P S j
          + ∑ i : Fin 0, ((fun _ => 1 : Fin 0 → ℤ) i : ℝ) * (v i j : ℝ))
          = (fun j => coordMoment P E j) := by
        funext j
        have hvan : ∀ x ∈ S, x ∉ E → P x * (x j : ℝ) = 0 := by
          intro x _ hxE
          by_contra hp
          exact hxE (hE x (fun h0 => hp (by rw [h0]; ring)))
        simp only [coordMoment]
        rw [Finset.sum_subset hES hvan]
        simp
      rw [hfun]
      exact hmean
  | succ n ih =>
      intro d S E P hP0 hmass hE hES B v hclauses hC hv
      classical
      -- The splitting vector
      set w : Fin d → ℤ := 3 • v (Fin.last n) with hw
      -- Evaluating the signed sums of the clause family
      have hsum1 : ∀ (a : Fin (n + 1)) (x : ℤ),
          ∑ i, (if i = a then x else 0) • (3 • v i) = x • (3 • v a) := by
        intro a x
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hb; simp [hb]
        · simp
      have hsum2 : ∀ (a b : Fin (n + 1)) (hab : a ≠ b) (x y : ℤ),
          ∑ i, (if i = a then x else if i = b then y else 0) • (3 • v i)
            = x • (3 • v a) + y • (3 • v b) := by
        intro a b hab x y
        have hsplit : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))),
            (if i = a then x else if i = b then y else 0) • (3 • v i)
              = (if i = a then x • (3 • v i) else 0)
                + (if i = b then y • (3 • v i) else 0) := by
          intro i _
          by_cases h1 : i = a
          · subst h1
            simp [hab]
          · by_cases h2 : i = b
            · subst h2
              simp [h1]
            · simp [h1, h2]
        rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
          Finset.sum_ite_eq' Finset.univ a (fun i => x • (3 • v i)),
          Finset.sum_ite_eq' Finset.univ b (fun i => y • (3 • v i))]
        simp
      -- Base memberships through the clause family (no stability)
      have hm0 : (0 : Fin d → ℤ) ∈ B := by
        have h := hclauses (fun _ => 0) (by intro i; simp)
        simpa using h
      have hmw : w ∈ B := by
        have h := hclauses (fun i => if i = Fin.last n then (1 : ℤ) else 0)
          (by intro i; by_cases h : i = Fin.last n <;> simp [h])
        rw [hsum1 (Fin.last n) 1] at h
        simpa [hw] using h
      have hmnw : -w ∈ B := by
        have h := hclauses (fun i => if i = Fin.last n then (-1 : ℤ) else 0)
          (by intro i; by_cases h : i = Fin.last n <;> simp [h, abs_neg])
        rw [hsum1 (Fin.last n) (-1)] at h
        simpa [hw] using h
      have mono3 : SupportContained S P ({0, w, -w} : Finset (Fin d → ℤ)) :=
        hC.mono (by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
          rcases ht with rfl | rfl | rfl
          · exact hm0
          · exact hmw
          · exact hmnw)
      -- The level-(d + 1) data
      set SQ : Finset ((Fin d → ℤ) × Bool) :=
        (S ×ˢ (Finset.univ : Finset Bool)).filter (fun y => split w P y ≠ 0)
        with hSQ
      set S' : Finset (Fin (d + 1) → ℤ) :=
        (S ×ˢ (Finset.univ : Finset Bool)).map liftUpEmb with hS'
      set E' : Finset (Fin (d + 1) → ℤ) := SQ.map liftUpEmb with hE'
      set B' : Finset (Fin (d + 1) → ℤ) :=
        (B.image (fun b => b + w) ∩ B.image (fun b => b - w)).image
          (fun a => Fin.snoc a 0) with hB'
      -- The arguments of the next level
      have hP0' : ∀ z, 0 ≤ pushUp (split w P) z :=
        fun z => pushUp_nonneg (split_nonneg hP0 w) z
      have hmass' : ∑ z ∈ S', pushUp (split w P) z = 1 := by
        rw [hS', pushUp_mass, split_mass_of_support w mono3]
        exact hmass
      have hsupp' : ∀ z, pushUp (split w P) z ≠ 0 → z ∈ E' := by
        intro z hz
        by_cases hy : ∃ y : (Fin d → ℤ) × Bool, liftUp y = z
        · obtain ⟨y, rfl⟩ := hy
          have hy' : split w P y ≠ 0 := by
            rw [← pushUp_apply (split w P) y]
            exact hz
          -- the antecedent lives in S ×ˢ univ
          have hy1 : y.1 ∈ S := by
            obtain ⟨x, b⟩ := y
            have hne : P (x + w) ≠ 0 ∨ P (x - w) ≠ 0 := by
              cases b with
              | false =>
                  rw [split_apply_zero] at hy'
                  rcases le_total (P (x + w)) (P (x - w)) with h | h
                  · rw [max_eq_right h] at hy'
                    exact Or.inr (by intro h0; rw [h0, mul_zero] at hy'; exact hy' rfl)
                  · rw [max_eq_left h] at hy'
                    exact Or.inl (by intro h0; rw [h0, mul_zero] at hy'; exact hy' rfl)
              | true =>
                  rw [split_apply_one] at hy'
                  rcases le_total (P (x + w)) (P (x - w)) with h | h
                  · rw [min_eq_left h] at hy'
                    exact Or.inl (by intro h0; rw [h0, mul_zero] at hy'; exact hy' rfl)
                  · rw [min_eq_right h] at hy'
                    exact Or.inr (by intro h0; rw [h0, mul_zero] at hy'; exact hy' rfl)
            rcases hne with h | h
            · have hx := hC (x + w) h (-w) hmnw
              simpa using hx
            · have hx := hC (x - w) h w hmw
              simpa using hx
          refine Finset.mem_map.2 ⟨y, Finset.mem_filter.2 ⟨?_, hy'⟩, rfl⟩
          exact Finset.mem_product.2 ⟨hy1, Finset.mem_univ _⟩
        · exact absurd (pushUp_eq_zero (split w P)
            (fun y hy' => hy ⟨y, hy'⟩)) hz
      have hES' : E' ⊆ S' := by
        intro z hz
        obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hz
        exact Finset.mem_map.2 ⟨y, Finset.filter_subset _ _ hy, rfl⟩
      have hC' : SupportContained S' (pushUp (split w P)) B' :=
        supportContained_pushUp_split_enlarged w hC
      -- The clauses of the next level: every bounded signed sum, snoc'ed,
      -- lives in the shadow (B + w) ∩ (B − w), because its base z has z ± w ∈ B
      have hclauses' : ∀ g : Fin n → ℤ, (∀ i, |g i| ≤ 2) →
          ∑ i, g i • (3 • (liftUp (v i.castSucc, false) : Fin (d + 1) → ℤ)) ∈ B' := by
        intro g hg
        have hlift : ∀ i : Fin n,
            3 • (liftUp (v i.castSucc, false) : Fin (d + 1) → ℤ)
              = Fin.snoc (3 • v i.castSucc) 0 := by
          intro i
          funext j
          induction j using Fin.lastCases with
          | last => simp [liftUp]
          | cast k => simp [liftUp, Pi.smul_apply]
        set z : Fin d → ℤ := ∑ i, g i • (3 • v i.castSucc) with hzdef
        have hsum' : ∑ i, g i • (3 • (liftUp (v i.castSucc, false) : Fin (d + 1) → ℤ))
            = Fin.snoc z 0 := by
          funext j
          induction j using Fin.lastCases with
          | last => simp
          | cast k =>
              rw [Finset.sum_apply]
              simp only [hlift, Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul,
                hzdef]
              rw [Finset.sum_apply]
              simp
        have hzw : z - w ∈ B := by
          have h := hclauses (Fin.snoc g (-1 : ℤ))
            (by
              intro i
              induction i using Fin.lastCases with
              | last => simp [abs_neg]
              | cast k => simpa using hg k)
          rw [Fin.sum_univ_castSucc] at h
          simp only [Fin.snoc_castSucc, Fin.snoc_last, neg_one_smul] at h
          rw [← hzdef] at h
          rw [sub_eq_add_neg, hw]
          exact h
        have hzpw : z + w ∈ B := by
          have h := hclauses (Fin.snoc g (1 : ℤ))
            (by
              intro i
              induction i using Fin.lastCases with
              | last => simp
              | cast k => simpa using hg k)
          rw [Fin.sum_univ_castSucc] at h
          simp only [Fin.snoc_castSucc, Fin.snoc_last, one_smul] at h
          rw [← hzdef] at h
          rw [hw]
          exact h
        rw [hsum']
        refine Finset.mem_image.mpr ⟨z, ?_, rfl⟩
        simp only [Finset.mem_inter, Finset.mem_image]
        refine ⟨⟨z - w, hzw, ?_⟩, z + w, hzpw, ?_⟩
        · funext j; simp only [Pi.add_apply, Pi.sub_apply]; omega
        · funext j; simp only [Pi.add_apply, Pi.sub_apply]; omega
      have hv' : ∀ i : Fin n,
          shiftDistance S' (pushUp (split w P)) (6 • liftUp (v i.castSucc, false))
            ≤ 3⁻¹ := by
        intro i
        have h6 : 6 • liftUp (v i.castSucc, false)
            = Fin.snoc (6 • v i.castSucc) 0 := by
          funext j
          induction j using Fin.lastCases with
          | last => simp [liftUp]
          | cast k => simp [liftUp, Pi.smul_apply]
        -- the six-shift contention, through the clause family
        have hmn6 : -(6 • v i.castSucc) ∈ B := by
          have h := hclauses (fun j => if j = i.castSucc then (-2 : ℤ) else 0)
            (by intro j; by_cases h : j = i.castSucc <;> simp [h, abs_neg])
          have hid : ((-2 : ℤ) • (3 • v i.castSucc) : Fin d → ℤ)
              = -(6 • v i.castSucc) := by
            funext j
            simp only [Pi.smul_apply, Pi.neg_apply]
            ring
          rw [hsum1 i.castSucc (-2), hid] at h
          exact h
        have hwu : w - 6 • v i.castSucc ∈ B := by
          have h := hclauses
            (fun j => if j = Fin.last n then (1 : ℤ) else
              if j = i.castSucc then (-2 : ℤ) else 0)
            (by intro j
                by_cases h1 : j = Fin.last n
                · simp [h1]
                · by_cases h2 : j = i.castSucc <;> simp [h1, h2, abs_neg])
          have hid : (((1 : ℤ) • (3 • v (Fin.last n))
              + (-2 : ℤ) • (3 • v i.castSucc) : Fin d → ℤ))
              = w - 6 • v i.castSucc := by
            funext j
            simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, hw]
            ring
          rw [hsum2 (Fin.last n) i.castSucc
            (by
              intro h
              have h2 := congrArg Fin.val h
              simp only [Fin.val_last, Fin.val_castSucc] at h2
              omega) 1 (-2), hid] at h
          exact h
        have hnwu : -w - 6 • v i.castSucc ∈ B := by
          have h := hclauses
            (fun j => if j = Fin.last n then (-1 : ℤ) else
              if j = i.castSucc then (-2 : ℤ) else 0)
            (by intro j
                by_cases h1 : j = Fin.last n
                · simp [h1, abs_neg]
                · by_cases h2 : j = i.castSucc <;> simp [h1, h2, abs_neg])
          have hid : (((-1 : ℤ) • (3 • v (Fin.last n))
              + (-2 : ℤ) • (3 • v i.castSucc) : Fin d → ℤ))
              = -w - 6 • v i.castSucc := by
            funext j
            simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, hw]
            ring
          rw [hsum2 (Fin.last n) i.castSucc
            (by
              intro h
              have h2 := congrArg Fin.val h
              simp only [Fin.val_last, Fin.val_castSucc] at h2
              omega) (-1) (-2), hid] at h
          exact h
        have h6set : SupportContained S P
            ({0, w, -w, -(6 • v i.castSucc), w - 6 • v i.castSucc,
              -w - 6 • v i.castSucc} : Finset (Fin d → ℤ)) :=
          hC.mono (by
            intro t ht
            simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
            rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
            · exact hm0
            · exact hmw
            · exact hmnw
            · exact hmn6
            · exact hwu
            · exact hnwu)
        rw [h6, hS', shiftDistance_pushUp]
        exact (shiftDistanceProd_split_le_of_support w (6 • v i.castSucc)
          hP0 hmass h6set).trans (hv i.castSucc)
      obtain ⟨ε', hε', hmem'⟩ := ih (d + 1) S' E' (pushUp (split w P))
        hP0' hmass' hsupp' hES' B' (fun i => liftUp (v i.castSucc, false))
        hclauses' hC' hv'
      -- The level-(d + 1) point, read coordinate by coordinate
      set z : Fin d → ℝ := fun k =>
        coordMoment P S k + ∑ i : Fin n, (ε' i : ℝ) * (v i.castSucc k : ℝ)
        with hz
      set β : ℝ := splitBit w P S with hb
      have hpt : (fun j => coordMoment (pushUp (split w P)) S' j
            + ∑ i : Fin n, (ε' i : ℝ) * ((liftUp (v i.castSucc, false)) j : ℝ))
          = Fin.snoc z β := by
        funext j
        induction j using Fin.lastCases with
        | last =>
            show coordMoment (pushUp (split w P)) S' (Fin.last d)
              + ∑ i : Fin n, (ε' i : ℝ)
                  * ((liftUp (v i.castSucc, false)) (Fin.last d) : ℝ)
              = (Fin.snoc z β : Fin (d + 1) → ℝ) (Fin.last d)
            rw [hS', coordMoment_pushUp_split_last w P S, hb]
            simp
        | cast k =>
            show coordMoment (pushUp (split w P)) S' k.castSucc
              + ∑ i : Fin n, (ε' i : ℝ)
                  * ((liftUp (v i.castSucc, false)) k.castSucc : ℝ)
              = (Fin.snoc z β : Fin (d + 1) → ℝ) k.castSucc
            rw [hS', coordMoment_pushUp_split_of_support w mono3 k, hz]
            simp
      have hmem2 : (fun j => coordMoment (pushUp (split w P)) S' j
            + ∑ i : Fin n, (ε' i : ℝ) * ((liftUp (v i.castSucc, false)) j : ℝ))
          ∈ convexHull ℝ
            ↑(E'.map (⟨⇑toReal, toReal_injective⟩ :
              (Fin (d + 1) → ℤ) ↪ (Fin (d + 1) → ℝ))) := hmem'
      rw [hpt] at hmem2
      -- the square: the transported pushed support is the snocReal image
      have hmapE : E'.map
            (⟨⇑toReal, toReal_injective⟩ : (Fin (d + 1) → ℤ) ↪ (Fin (d + 1) → ℝ))
          = (SQ.map toRealProdEmb).map snocRealEmb := by
        apply Finset.ext
        intro t
        simp only [Finset.mem_map]
        constructor
        · rintro ⟨q, hq, rfl⟩
          obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hq
          exact ⟨toRealProd y, ⟨y, hy, rfl⟩, snocReal_toRealProd y⟩
        · rintro ⟨r, hr, rfl⟩
          obtain ⟨y, hy, rfl⟩ := hr
          exact ⟨liftUp y, Finset.mem_map.2 ⟨y, hy, rfl⟩,
            (snocReal_toRealProd y).symm⟩
      rw [hmapE] at hmem2
      have h1 : Fin.snoc z β = snocReal (z, β) := rfl
      rw [h1] at hmem2
      obtain hmempb := (mem_convexHull_map_snocReal
        (E := SQ.map toRealProdEmb) (p := (z, β))).mp hmem2
      -- the height key: splitBit ≥ 1/3
      have hw2 : w + w = 6 • v (Fin.last n) := by
        funext j
        simp only [Pi.add_apply, Pi.smul_apply, hw]
        ring
      have hidww : -(w + w) = -w - w := by
        funext j
        simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, hw]
        ring
      have hmww : -w - w ∈ B := by
        have h := hclauses (fun j => if j = Fin.last n then (-2 : ℤ) else 0)
          (by intro j; by_cases h : j = Fin.last n <;> simp [h, abs_neg])
        have hid : (-2 : ℤ) • (3 • v (Fin.last n)) = -w - w := by
          funext j
          simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul, hw]
          ring
        rw [hsum1 (Fin.last n) (-2), hid] at h
        exact h
      have hP5 : SupportContained S P
          ({0, w, -w, -w - w, -(w + w)} : Finset (Fin d → ℤ)) :=
        hC.mono (by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
          rcases ht with rfl | rfl | rfl | rfl | rfl
          · exact hm0
          · exact hmw
          · exact hmnw
          · exact hmww
          · rw [hidww]
            exact hmww)
      have hβ : 3⁻¹ ≤ β := by
        rw [hb, splitBit_eq_of_support w hP0 hmass hP5, hw2]
        linarith [hv (Fin.last n)]
      -- the recall: z + e • toReal (v last) ∈ hull of the support of P
      obtain ⟨e, he, hfin⟩ := pullback (v := w) (w := v (Fin.last n)) hP0 hE
        (fun i => by rw [hw]; simp)
        (fun y hy => (Finset.mem_filter.1 hy).2)
        hβ hmempb
      -- the final assembly
      have hēe : ((if e = 1 then 1 else -1 : ℤ) : ℝ) = e := by
        rcases he with h | h
        · rw [if_pos h, h]
          norm_num
        · rw [if_neg (by rw [h]; norm_num), h]
          norm_num
      refine ⟨Fin.snoc ε' (if e = 1 then 1 else -1), ?_, ?_⟩
      · intro i
        induction i using Fin.lastCases with
        | last =>
            simp only [Fin.snoc_last]
            rcases he with h | h
            · exact Or.inl (by rw [if_pos h])
            · exact Or.inr (by rw [if_neg (by rw [h]; norm_num)])
        | cast j => simpa using hε' j
      · have hfe : (fun j => coordMoment P S j
            + ∑ i : Fin (n + 1),
                ((Fin.snoc ε' (if e = 1 then 1 else -1) : Fin (n + 1) → ℤ) i : ℝ)
                  * (v i j : ℝ))
          = z + e • toReal (v (Fin.last n)) := by
          funext j
          rw [Fin.sum_univ_castSucc, Fin.snoc_last, hēe]
          simp only [Fin.snoc_castSucc, Pi.add_apply, Pi.smul_apply, toReal_apply, hz]
          ring
        rw [hfe]
        exact hfin

/-- **Lemma 1.4 (Karingula–Lovett) — public statement**: if `S` contains
the support of `P` shifted by every signed sum with coefficients bounded
by 2 in the generators `3 • v i`, and if every `6 • v i` has shift
distance `≤ 1/3`, then there exists a coloring `ε` such that the
barycenter of `P` augmented by the signed sums belongs to the convex hull
of the transported support of `P`.

The clause set `B` is provided by the caller — typically the image of the
bounded coefficients (5ⁿ points, a satisfiable "large box", **no stability
required**): this is the #21417 fix of the k2.6c defect (the former shape
carried an `A` stable under `± 3 • v i`, an orbit class that forces
`v = 0` — see the witness `contention_stability_forces_zero` below).
Requiring `B` explicitly keeps the hypothesis checkable by the caller
without locking the inductive gate into a frozen instantiation.

The gate form (`exists_colouring_aux`) concludes on the exact support `E`;
the public statement consumes it with `E := S.filter (P · ≠ 0)` and climbs
back to the hull of `S` by monotonicity — this is the lake reading of the
oracle `gdahia/Komlos` (`SignedSums.lean` l.32-36), where the `Finsupp`
carries its canonical support. -/
theorem exists_isColouring_mean_add_sum_mem_convexHull (n d : ℕ)
    (S B : Finset (Fin d → ℤ)) (P : (Fin d → ℤ) → ℝ) (hP0 : ∀ x, 0 ≤ P x)
    (hmass : ∑ x ∈ S, P x = 1) (hPsupp : ∀ x, P x ≠ 0 → x ∈ S)
    (v : Fin n → (Fin d → ℤ))
    (hclauses : ∀ f : Fin n → ℤ, (∀ i, |f i| ≤ 2) → ∑ i, f i • (3 • v i) ∈ B)
    (hB : SupportContained S P B)
    (hv : ∀ i, shiftDistance S P (6 • v i) ≤ 3⁻¹) :
    ∃ ε : Fin n → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (fun j => coordMoment P S j + ∑ i, (ε i : ℝ) * (v i j : ℝ)) ∈
        convexHull ℝ
          ↑(S.map (⟨⇑toReal, toReal_injective⟩ : (Fin d → ℤ) ↪ (Fin d → ℝ))) := by
  obtain ⟨ε, hε, hmem⟩ := exists_colouring_aux n d S (S.filter (fun x => P x ≠ 0)) P
    hP0 hmass (fun x hx => Finset.mem_filter.2 ⟨hPsupp x hx, hx⟩)
    (Finset.filter_subset _ _) B v hclauses hB hv
  refine ⟨ε, hε, ?_⟩
  have hsub : (S.filter (fun x => P x ≠ 0)).map
      (⟨⇑toReal, toReal_injective⟩ : (Fin d → ℤ) ↪ (Fin d → ℝ))
    ⊆ S.map (⟨⇑toReal, toReal_injective⟩ : (Fin d → ℤ) ↪ (Fin d → ℝ)) :=
    Finset.map_subset_map.mpr (Finset.filter_subset _ _)
  exact convexHull_mono (Finset.coe_subset.2 hsub) hmem


/-- **Defect of the public statement of Lemma 1.4, proved** (measurement
k5.2): the containment hypotheses `hA0 : 0 ∈ A` and
`hAstab : ∀ a ∈ A, ∀ i, a + 3 • v i ∈ A ∧ a - 3 • v i ∈ A` on a `Finset`
force `v i = 0` for every `i`. The argument is the orbit of
`eq_zero_of_image_add_eq_self` (k1.7) transposed from `S` to `A`: stability
of `A` under `+ 3 • v i` says `A.image (fun x => x + 3 • v i) ⊆ A`, the
image of a translation has the same cardinal, hence equality, and image
invariance of a nonempty set forces the shift to vanish in the torsion-free
group `ℤ^d`.

Measured consequence: `exists_isColouring_mean_add_sum_mem_convexHull` is
only instantiable at an identically zero family `v` — the regime where
`shiftDistance S P (6 • v i) ≤ 3⁻¹` is trivial and the conclusion carries no
sum. This is the same defect class as the one measured in k1.7 on the
invariance of `S` (stability under a nonzero translation on a finite set),
reintroduced at the k2.6 summit on `A`. **Fix delivered (chantier
#21417)**: the inductive gate no longer carries a stable set — containment
is reified on a clause family `B` (signed sums with coefficients bounded
by 2 in the `3 • v i`, satisfiable by a large box), transmitted by
`supportContained_pushUp_split_enlarged` (intersection of translates);
`shiftDistance` keeps its k1.1 shape, and the gateway
`shiftDistance_eq_shiftDistanceTV` (k4.2c) remains available as an
alternative reading. The k5.2 (GridCase) assembly depends on it. -/
theorem contention_stability_forces_zero {d n : ℕ} (v : Fin n → (Fin d → ℤ))
    {A : Finset (Fin d → ℤ)} (hA0 : 0 ∈ A)
    (hAstab : ∀ a ∈ A, ∀ i, a + 3 • v i ∈ A ∧ a - 3 • v i ∈ A) :
    ∀ i, v i = 0 := by
  intro i
  have hsub : A.image (fun x => x + 3 • v i) ⊆ A := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    exact (hAstab a ha i).1
  have hcard : (A.image (fun x => x + 3 • v i)).card = A.card :=
    Finset.card_image_of_injective _ (fun x y h => add_right_cancel h)
  have hEq : A.image (fun x => x + 3 • v i) = A :=
    Finset.eq_of_subset_of_card_le hsub (hcard ▸ Nat.le_refl _)
  have h3 : 3 • v i = 0 :=
    eq_zero_of_image_add_eq_self hEq ⟨0, hA0⟩
  funext j
  have hcoord : (3 • v i) j = 0 := congrFun h3 j
  simpa [Pi.smul_apply] using hcoord

/-! ### k5.2 positive control (overhaul #21417, step P4)

The corrected public statement is not merely non-vacuous by construction:
it instantiates **explicitly** on a nonzero family `v`. The witness lives
in dimension `d = 1` with a single generator `v 0 = 1`: the support of `P`
is the grid `{0, 6, 12, 18}` (four points of step 6, mass `1/4` each), the
clause set `B` is `{−6, −3, 0, 3, 6}` — exactly the five signed sums with
coefficients bounded by 2 along `3 • v 0` —, and the frame `S` is the
step-3 stretch from −6 to 24: the support enlarged by each of its
translates by `B`, as `SupportContained` requires. On this instance,
`shiftDistance S P (6 • v 0) = 1/4` (two boundary edges over eleven
points, interior contributions cancelling by translation of the support),
strictly below the threshold `3⁻¹`.

The theorem pair below is the complete positive control: the corrected
form applies (`exists_isColouring_grid_nonzero_v`, with `gridV 0 ≠ 0` by
`gridV_nonzero`), while the **historical** form — containment by a set `A`
stable under `± 3 • v i` — is proven unsatisfiable for that very same `v`
(`old_form_unsatisfiable_for_gridV`, via
`contention_stability_forces_zero`). This is the k5.2 measurement turned
around: the defect was not in the conclusion of Lemma 1.4 but in a
hypothesis no nontrivial instance could satisfy. -/

/-- Point of the `d = 1` line, seen in `Fin 1 → ℤ`: the constant function. -/
def gridPoint (t : ℤ) : Fin 1 → ℤ := fun _ => t

/-- Witness support: the grid `{0, 6, 12, 18}` (step 6, four points). -/
noncomputable def gridSupport : Finset (Fin 1 → ℤ) :=
  (Finset.Ico (0 : ℤ) 4).image (fun k => gridPoint (6 * k))

/-- Witness clause set: the five signed sums bounded by 2 along
`3 • v 0`, namely `{−6, −3, 0, 3, 6}`. -/
noncomputable def gridClauses : Finset (Fin 1 → ℤ) :=
  (Finset.Ico (-2 : ℤ) 3).image (fun j => gridPoint (3 * j))

/-- Witness frame: the step-3 stretch from −6 to 24 — `gridSupport`
enlarged by each of its translates by `gridClauses` (the
`SupportContained` requirement). -/
noncomputable def gridBox : Finset (Fin 1 → ℤ) :=
  (Finset.Ico (-2 : ℤ) 9).image (fun m => gridPoint (3 * m))

/-- The uniform distribution on `gridSupport`: mass `1/4` per support
point. -/
noncomputable def gridP (x : Fin 1 → ℤ) : ℝ := if x ∈ gridSupport then 1 / 4 else 0

/-- The witness generator family: `v 0 = 1`, **nonzero**. -/
def gridV : Fin 1 → (Fin 1 → ℤ) := fun _ _ => 1

theorem gridPoint_injective : Function.Injective gridPoint := fun _ _ h => congrFun h 0

/-- The support abscissae: `6 · {0, 1, 2, 3}`. -/
noncomputable def gridTs : Finset ℤ := (Finset.Ico (0 : ℤ) 4).image (fun k => 6 * k)

theorem mem_gridSupport_iff {t : ℤ} :
    gridPoint t ∈ gridSupport ↔ t ∈ gridTs := by
  constructor
  · intro h
    obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp h
    exact Finset.mem_image.mpr ⟨k, hk, congrFun heq 0⟩
  · intro h
    obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp h
    exact Finset.mem_image.mpr ⟨k, hk, congrArg gridPoint heq⟩

/-- The abscissa clause: `3 · m ∈ gridTs` exactly for `m` even in
`{0, 2, 4, 6}` — the four support points. -/
theorem mem_gridTs_iff {m : ℤ} :
    3 * m ∈ gridTs ↔ m ∈ ({0, 2, 4, 6} : Finset ℤ) := by
  simp only [gridTs, Finset.mem_image, Finset.mem_Ico,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨k, ⟨hk0, hk4⟩, hkm⟩
    omega
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, by omega, by ring⟩
    · exact ⟨1, by omega, by ring⟩
    · exact ⟨2, by omega, by ring⟩
    · exact ⟨3, by omega, by ring⟩

theorem gridSupport_subset_gridBox : gridSupport ⊆ gridBox := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
  refine Finset.mem_image.mpr ⟨2 * k, ?_, ?_⟩
  · simp only [Finset.mem_Ico]; omega
  · exact congrArg gridPoint (by ring)

theorem gridP_nonneg : ∀ x, 0 ≤ gridP x := by
  intro x
  unfold gridP
  split <;> norm_num

theorem gridP_mass : ∑ x ∈ gridBox, gridP x = 1 := by
  have hzero : ∀ x ∈ gridBox, x ∉ gridSupport → gridP x = 0 := by
    intro x _ hx
    unfold gridP
    rw [if_neg hx]
  rw [← Finset.sum_subset gridSupport_subset_gridBox hzero]
  have hpos : ∀ x ∈ gridSupport, gridP x = 1 / 4 := by
    intro x hx
    unfold gridP
    rw [if_pos hx]
  rw [Finset.sum_congr rfl hpos, Finset.sum_const]
  have hcard : gridSupport.card = 4 := by
    have hinj : Function.Injective (fun k : ℤ => gridPoint (6 * k)) := by
      intro a b h
      have h6 : (6 : ℤ) * a = 6 * b := gridPoint_injective h
      omega
    rw [gridSupport, Finset.card_image_of_injective _ hinj]
    simp
  rw [hcard]
  norm_num

theorem gridP_support : ∀ x, gridP x ≠ 0 → x ∈ gridBox := by
  intro x hx
  have hmem : x ∈ gridSupport := by
    by_contra h
    unfold gridP at hx
    rw [if_neg h] at hx
    norm_num at hx
  exact gridSupport_subset_gridBox hmem

theorem gridClauses_clauses :
    ∀ f : Fin 1 → ℤ, (∀ i, |f i| ≤ 2) → ∑ i, f i • (3 • gridV i) ∈ gridClauses := by
  intro f hf
  obtain ⟨h1, h2⟩ := abs_le.mp (hf 0)
  rw [Fin.sum_univ_one]
  have hval : f 0 • (3 • gridV 0) = gridPoint (3 * f 0) := by
    funext j
    simp only [gridV, gridPoint, Pi.smul_apply]
    ring
  rw [hval]
  refine Finset.mem_image.mpr ⟨f 0, ?_, congrArg gridPoint rfl⟩
  simp only [Finset.mem_Ico]
  omega

theorem grid_contained : SupportContained gridBox gridP gridClauses := by
  intro z hz w hw
  have hz' : z ∈ gridSupport := by
    by_contra h
    unfold gridP at hz
    rw [if_neg h] at hz
    norm_num at hz
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz'
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
  obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
  refine Finset.mem_image.mpr ⟨2 * k + j, ?_, ?_⟩
  · simp only [Finset.mem_Ico]; omega
  · funext q
    simp only [gridPoint, Pi.add_apply]
    ring

/-- The key measurement of the witness: the shift `6 • v 0` cuts the
support along exactly two boundary edges, hence `Δ = 1/4` — strictly
below the `3⁻¹` threshold of the `hv` hypothesis of Lemma 1.4. -/
theorem grid_shiftDistance : shiftDistance gridBox gridP (6 • gridV 0) = 1 / 4 := by
  unfold shiftDistance
  have hshift : (6 • gridV 0 : Fin 1 → ℤ) = gridPoint 6 := by
    funext j
    simp only [gridV, gridPoint, Pi.smul_apply]
    ring
  have hreindex : ∑ x ∈ gridBox, |gridP (x + 6 • gridV 0) - gridP x|
      = ∑ m ∈ Finset.Ico (-2 : ℤ) 9,
          |gridP (gridPoint (3 * m) + gridPoint 6) - gridP (gridPoint (3 * m))| := by
    rw [hshift]
    simp only [gridBox]
    exact Finset.sum_image (fun a _ b _ h => by
      have h3 : (3 : ℤ) * a = 3 * b := gridPoint_injective h
      omega)
  rw [hreindex]
  have hval : ∀ m ∈ Finset.Ico (-2 : ℤ) 9,
      |gridP (gridPoint (3 * m) + gridPoint 6) - gridP (gridPoint (3 * m))|
        = if m = -2 ∨ m = 6 then 1 / 4 else 0 := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.mp hm
    have hshiftm : gridPoint (3 * m) + gridPoint 6 = gridPoint (3 * (m + 2)) := by
      funext q
      simp only [gridPoint, Pi.add_apply]
      ring
    have hgg : ∀ t : ℤ, gridP (gridPoint t) = if t ∈ gridTs then 1 / 4 else 0 := by
      intro t
      unfold gridP
      simp only [mem_gridSupport_iff]
    rw [hshiftm, hgg (3 * (m + 2)), hgg (3 * m)]
    simp only [mem_gridTs_iff, Finset.mem_insert, Finset.mem_singleton]
    interval_cases m <;> simp
  rw [Finset.sum_congr rfl hval]
  have hsum2 : ∑ m ∈ Finset.Ico (-2 : ℤ) 9,
      (if m = -2 ∨ m = 6 then (1 / 4 : ℝ) else 0) = 1 / 2 := by
    have hsub : ({-2, 6} : Finset ℤ) ⊆ Finset.Ico (-2 : ℤ) 9 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_Ico]
      omega
    have hzero : ∀ m ∈ Finset.Ico (-2 : ℤ) 9,
        m ∉ ({-2, 6} : Finset ℤ) →
          (if m = -2 ∨ m = 6 then (1 / 4 : ℝ) else 0) = 0 := by
      intro m _ hm'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm'
      rw [if_neg hm']
    have hbig : ∑ m ∈ Finset.Ico (-2 : ℤ) 9,
        (if m = -2 ∨ m = 6 then (1 / 4 : ℝ) else 0)
        = ∑ m ∈ ({-2, 6} : Finset ℤ),
            (if m = -2 ∨ m = 6 then (1 / 4 : ℝ) else 0) := by
      first
        | exact Finset.sum_subset hsub hzero
        | exact (Finset.sum_subset hsub hzero).symm
    rw [hbig]
    simp
    norm_num
  rw [hsum2]
  norm_num

theorem grid_shiftDistance_le : shiftDistance gridBox gridP (6 • gridV 0) ≤ 3⁻¹ := by
  rw [grid_shiftDistance]
  norm_num

theorem gridV_nonzero : gridV 0 ≠ 0 := by
  intro h
  have h0 : (gridV 0 : Fin 1 → ℤ) 0 = 1 := rfl
  rw [h] at h0
  simp at h0

/-- **The positive control**: the corrected public statement of Lemma 1.4
applies to the witness — a **nonzero** family `v` (`gridV 0 = 1`) with
every hypothesis satisfied (`hmass`, `hclauses`, `hB`, `hv` with
`Δ = 1/4 < 3⁻¹`). -/
theorem exists_isColouring_grid_nonzero_v :
    ∃ ε : Fin 1 → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (fun j => coordMoment gridP gridBox j + ∑ i, (ε i : ℝ) * (gridV i j : ℝ)) ∈
        convexHull ℝ
          ↑(gridBox.map (⟨⇑toReal, toReal_injective⟩ : (Fin 1 → ℤ) ↪ (Fin 1 → ℝ))) := by
  refine exists_isColouring_mean_add_sum_mem_convexHull 1 1 gridBox gridClauses gridP
    gridP_nonneg gridP_mass gridP_support gridV gridClauses_clauses grid_contained ?_
  intro i
  fin_cases i
  exact grid_shiftDistance_le

/-- **The contrast**: for this very `gridV`, the historical form of the
containment (a finite set `A` containing `0` and stable under
`± 3 • v i`) is **unsatisfiable** — an immediate consequence of the
witness `contention_stability_forces_zero`. This is the formal proof that
the #21417 fix unlocked an instance the old statement forbade. -/
theorem old_form_unsatisfiable_for_gridV :
    ¬ ∃ A : Finset (Fin 1 → ℤ), (0 : Fin 1 → ℤ) ∈ A ∧
      ∀ a ∈ A, a + 3 • gridV 0 ∈ A ∧ a - 3 • gridV 0 ∈ A := by
  rintro ⟨A, hA0, hAstab⟩
  exact gridV_nonzero
    (contention_stability_forces_zero gridV hA0 (fun a ha _ => hAstab a ha) 0)

end Discrepancy.Komlos_en
