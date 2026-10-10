/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted for `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979): toolchain v4.33.0, Mathlib `db584cd6`, i18n convention #4980.

The original Dahia source lives in the `gdahia/Komlos` repository (toolchain
v4.34.0, `Finsupp` framework over `E →₀ ℝ`). This module has **no
name-for-name oracle counterpart**: the oracle needs no level bridge, and
that absence is precisely what this brick documents.

**Design-gate of the k2.6 assembly (recorded here, decision arbitrated).**
The oracle proves Lemma 1.4 (`Komlos/SignedSums.lean` l.37-64) by induction
on `n` with the statement **universally quantified over `E`** — so the
induction hypothesis applies, at the successor step, to the split
distribution in the **grown** space `E × ℝ` (l.52), with vectors embedded
at height zero `(v i.castSucc, 0)` (l.47, l.53). The lake's base `Fin d → ℤ`
is fixed, and none of the k1.x/k2.x bricks would apply to a distribution
on a genuinely different type. The options measured:

- (a) generalize `split`/`pullback` over an abstract space `X × Bool` —
  a second formalization of the whole chain;
- (b) iterated product space `(Fin d → ℤ) × (Fin n → Bool)` — same
  generalization cost, heavier notation;
- **(c) retained: the growing space is `Fin (d + k) → ℤ`.** The height
  `Bool` embeds as the integer `{0, 1}` at the `snoc` position: the
  embedding `liftUp : ((Fin d → ℤ) × Bool) → (Fin (d+1) → ℤ)` realizes
  the oracle's `incl b : E ↪ E × ℝ` (`Komlos/Split.lean` l.31) on the
  discrete side, and `toReal` (k2.3) transports to `Fin (d+1) → ℝ`, which
  is the oracle's `E × ℝ` read coordinate-wise. Every brick of the lake
  being generic in `d`, they all **apply as-is at the next dimension**:
  the induction mirror of the oracle is `induction n generalizing d`.

**Scope of this commit** (brick k2.6a, `lake build SUCCESS` required, 0
`sorry`) — the level bridge, all of it mechanical:

- `liftUp` + injectivity — the product-to-`snoc` embedding;
- `liftUp_add_snoc` — translations at height zero commute with the
  embedding: `liftUp y + snoc u 0 = liftUp (y.1 + u, y.2)` (the equation
  that makes the `shiftDistance` bridge work);
- `pushUp` — the push-forward along `liftUp`, the **same `Function.extend`
  pattern as the k2.3 organ `push`** (the lake's `Finsupp.embDomain`),
  with its `apply`/`eq_zero`/`nonneg`/`mass` reading; it is not the k2.3
  `push` itself because that one is typed on the dimension transport
  `(Fin d → ℤ) →+ (Fin d → ℝ)`, and the product side carries no additive
  structure (`Bool`);
- the **moment bridges**: the coordinate moment of the pushed
  distribution at a `castSucc` coordinate is the product moment of the
  source; at the `last` coordinate it is the height moment — the two
  components of `mean_split` (k2.0) read through the embedding;
- the **shift-distance bridge**: `Δ(pushUp Q, snoc u 0) = Δprod(Q, u)` —
  the Claim 3.2 of k1.5 transfers to the grown space verbatim;
- `sum_smul_snoc` — the lake form of the oracle's `sum_smul_inl`
  (`Komlos/Split.lean` l.50-53): a sum of scaled vectors embedded at
  height zero stays embedded at height zero. Its consumer is measured:
  `Komlos/SignedSums.lean` l.54 (`rw [mean_split, sum_smul_inl, ...]`);
- `toReal_liftUp` — the commutation `toReal ∘ liftUp = snoc ∘ (toReal ×
  height)`: the diagram square with k2.4's `toRealProd` closes, which is
  how the k2.6 assembly will feed `pullback` (k2.4) from the induction
  hypothesis stated at the grown dimension.

**Deferred with a measured consumer**: the moment conservation under
containment (`prodMoment_split_of_support`, the `_of_support` pendant of
k2.0's `mean_split` components) and the containment transfer through the
split (k2.6b); the induction itself (`SignedSums.lean` name for name,
k2.6c). The detailed state lives in `FORMAL_STATUS.md`.
-/

import Discrepancy.Komlos.MeanSplit_en
import Discrepancy.Komlos.SplitDistance_en
import Discrepancy.Komlos.Transport_en

/-!
# Level bridge: product space to grown dimension (k2.6a)

`Discrepancy.Komlos_en.liftUp` embeds `(Fin d → ℤ) × Bool` into
`Fin (d+1) → ℤ` — the spatial part by `Fin.snoc`, the height `Bool` as the
integer `{0, 1}` at the last coordinate. `pushUp` pushes a distribution
along it (the `Function.extend` pattern of the k2.3 organ `push`), and the
bridges of this module state that **every** structure the assembly
consumes — mass, coordinate moments, height moment, shift distance,
support — is read through the embedding without loss.

This is the discrete realization of the oracle's growing space: its
induction on the number of vectors applies the hypothesis in `E × ℝ` at
each split (`Komlos/SignedSums.lean` l.44-53); ours applies it at
`Fin (d+1) → ℤ`, where every brick of the lake (all generic in `d`)
already lives.
-/

namespace Discrepancy.Komlos_en

/-- **Level embedding**: the product grid `(Fin d → ℤ) × Bool` embeds into
the next-dimension grid `Fin (d+1) → ℤ` — the spatial part by `Fin.snoc`,
the `Bool` height as the integer `{0, 1}` at the last coordinate.

This is the discrete counterpart of the oracle's `incl b : E ↪ E × ℝ`
(`Komlos/Split.lean` l.31): where the oracle embeds `E` as the slice at
height `b` of `E × ℝ`, the lake embeds the pair `(x, b)` as a
dimension-`d+1` vector — the height becoming an integer coordinate valued
`0` or `1`. The transport `toReal` (k2.3) then reads it back as a real
coordinate, closing the square with `toRealProd` (k2.4, cf `toReal_liftUp`). -/
def liftUp {d : ℕ} : ((Fin d → ℤ) × Bool) → (Fin (d + 1) → ℤ) :=
  fun y => Fin.snoc y.1 (if y.2 then 1 else 0)

/-- Reading of the embedding on an inherited coordinate: the spatial part
is read unchanged. -/
@[simp] lemma liftUp_apply_castSucc {d : ℕ} (y : (Fin d → ℤ) × Bool)
    (i : Fin d) : liftUp y i.castSucc = y.1 i := by simp [liftUp]

/-- Reading of the embedding on the height coordinate: the `Bool` becomes
the integer `{0, 1}`. -/
@[simp] lemma liftUp_apply_last {d : ℕ} (y : (Fin d → ℤ) × Bool) :
    liftUp y (Fin.last d) = if y.2 then 1 else 0 := by simp [liftUp]

/-- The level embedding is **injective**: equal `snoc`s have equal tails
and equal bodies, and the height coordinate separates `false` from `true`
by `0 ≠ 1`. This is the glue of the `Finset.map`s of pushed supports. -/
lemma liftUp_injective {d : ℕ} : Function.Injective (liftUp (d := d)) := by
  rintro ⟨x₁, b₁⟩ ⟨x₂, b₂⟩ h
  simp only [liftUp, Fin.snoc_inj] at h
  obtain ⟨hxe, hqe⟩ := h
  cases b₁ <;> cases b₂ <;> simp_all

/-- The `Finset.Embedding` version of `liftUp`, for the `Finset.map`s of
pushed supports. -/
def liftUpEmb {d : ℕ} : ((Fin d → ℤ) × Bool) ↪ (Fin (d + 1) → ℤ) :=
  ⟨liftUp, liftUp_injective⟩

/-- Reading of the wrapper embedding: `liftUpEmb` applies `liftUp`. This
is the syntactic bridge consumed by the `pushUp_apply` / `liftUp_apply_*`
rewrites on `Finset.map` images. -/
lemma liftUpEmb_apply {d : ℕ} (y : (Fin d → ℤ) × Bool) :
    liftUpEmb y = liftUp y := rfl

/-- **Translations at height zero commute with the embedding**:
`liftUp y + snoc u 0 = liftUp (y.1 + u, y.2)`. This is the equation that
makes the shift-distance bridge (`shiftDistance_pushUp`) work: a base
translation `u`, embedded at height zero in the grown dimension, acts on
the image exactly as the product-space translation `(u, 0)`. -/
lemma liftUp_add_snoc {d : ℕ} (y : (Fin d → ℤ) × Bool) (u : Fin d → ℤ) :
    liftUp y + Fin.snoc u 0 = liftUp (y.1 + u, y.2) := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [liftUp]
  | cast i => simp [liftUp, Pi.add_apply]

/-- **Push-forward of a distribution along the level embedding**:
`pushUp Q (liftUp y) = Q y` (by `pushUp_apply`) and `pushUp Q z = 0`
off the image (by `pushUp_eq_zero`).

This is the **same `Function.extend` pattern as the k2.3 organ `push`**
(the oracle's `Finsupp.embDomain`, `Komlos/Transport.lean` l.27-28) — and
not that organ itself: the k2.3 `push` is typed on the dimension
transport `(Fin d → ℤ) →+ (Fin d → ℝ)`, an additive morphism, whereas the
product source `(Fin d → ℤ) × Bool` carries no additive structure (`Bool`
has no inverse). The extension along an injection is the Mathlib organ
common to both. -/
noncomputable def pushUp {d : ℕ} (Q : ((Fin d → ℤ) × Bool) → ℝ) :
    (Fin (d + 1) → ℤ) → ℝ :=
  Function.extend liftUp Q 0

/-- On the image of the embedding, the push-forward reads the source
distribution. (In the oracle, this is the role of
`Finsupp.embDomain_apply_self`.) -/
@[simp] lemma pushUp_apply {d : ℕ} (Q : ((Fin d → ℤ) × Bool) → ℝ)
    (y : (Fin d → ℤ) × Bool) : pushUp Q (liftUp y) = Q y :=
  Function.Injective.extend_apply liftUp_injective Q 0 y

/-- Off the image of the embedding, the push-forward is zero: points of
the dimension-`d+1` grid with no product preimage carry no mass. -/
lemma pushUp_eq_zero {d : ℕ} (Q : ((Fin d → ℤ) × Bool) → ℝ)
    {z : Fin (d + 1) → ℤ} (hz : ∀ y, liftUp y ≠ z) : pushUp Q z = 0 := by
  have hb : ¬∃ a, liftUp a = z := by
    rintro ⟨a, rfl⟩
    exact hz a rfl
  exact Function.extend_apply' Q (0 : (Fin (d + 1) → ℤ) → ℝ) z hb

/-- The push-forward of a nonnegative function is nonnegative: every
point is either a value of the source, or zero. -/
lemma pushUp_nonneg {d : ℕ} {Q : ((Fin d → ℤ) × Bool) → ℝ}
    (hQ : ∀ y, 0 ≤ Q y) (z : Fin (d + 1) → ℤ) : 0 ≤ pushUp Q z := by
  by_cases h : ∃ y, liftUp y = z
  · obtain ⟨y, rfl⟩ := h
    rw [pushUp_apply]
    exact hQ y
  · rw [pushUp_eq_zero Q (fun y hy => h ⟨y, hy⟩)]

/-- **Mass is preserved by the push-forward**: summing the push-forward
over the transported support is summing the source — the `pushUp`
counterpart of `push_mass` (k2.3). -/
lemma pushUp_mass {d : ℕ} (Q : ((Fin d → ℤ) × Bool) → ℝ)
    (SQ : Finset ((Fin d → ℤ) × Bool)) :
    ∑ z ∈ SQ.map liftUpEmb, pushUp Q z = ∑ y ∈ SQ, Q y := by
  simp only [Finset.sum_map, liftUpEmb_apply]
  exact Finset.sum_congr rfl fun y _ => pushUp_apply Q y

/-- **Exactness of the pushed support (forward direction)**: if every
point of `SQ` carries nonzero mass, so does every point of the
transported support. -/
lemma pushUp_ne_zero_of_mem {d : ℕ} {Q : ((Fin d → ℤ) × Bool) → ℝ}
    {SQ : Finset ((Fin d → ℤ) × Bool)} (hSQ : ∀ y ∈ SQ, Q y ≠ 0) :
    ∀ z ∈ SQ.map liftUpEmb, pushUp Q z ≠ 0 := by
  intro z hz
  rw [Finset.mem_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  simp only [liftUpEmb_apply]
  rw [pushUp_apply]
  exact hSQ y hy

/-- **Exactness of the pushed support (return direction)**: if `SQ`
contains the support of `Q`, the transported image contains the support
of the push-forward. -/
lemma pushUp_mem_map_of_ne_zero {d : ℕ} {Q : ((Fin d → ℤ) × Bool) → ℝ}
    {SQ : Finset ((Fin d → ℤ) × Bool)} (hSQ : ∀ y, Q y ≠ 0 → y ∈ SQ) :
    ∀ z, pushUp Q z ≠ 0 → z ∈ SQ.map liftUpEmb := by
  intro z hz
  by_cases hex : ∃ y, liftUp y = z
  · obtain ⟨y, rfl⟩ := hex
    rw [pushUp_apply] at hz
    exact Finset.mem_map.mpr ⟨y, hSQ y hz, liftUpEmb_apply y⟩
  · rw [pushUp_eq_zero Q (fun y hy => absurd ⟨y, hy⟩ hex)] at hz
    exact (hz rfl).elim

/-- **Moment bridge, inherited coordinate**: the coordinate moment of the
push-forward, read at a `castSucc` coordinate, is the base moment of the
source — the spatial component of the barycenter crosses the embedding
unchanged. This is the first component of `mean_split` (k2.0) read
through the level bridge. -/
lemma coordMoment_pushUp_castSucc {d : ℕ} (Q : ((Fin d → ℤ) × Bool) → ℝ)
    (SQ : Finset ((Fin d → ℤ) × Bool)) (i : Fin d) :
    coordMoment (pushUp Q) (SQ.map liftUpEmb) i.castSucc = prodMoment Q SQ i := by
  simp only [coordMoment, prodMoment, Finset.sum_map, liftUpEmb_apply]
  exact Finset.sum_congr rfl fun y _ => by rw [pushUp_apply, liftUp_apply_castSucc]

/-- **Moment bridge, height coordinate**: the coordinate moment of the
push-forward, read at the last coordinate, is the height moment of the
source — the `Bool` `{false, true}` read back as the real `{0, 1}`. This
is the second component of `mean_split` (k2.0): the split bit becomes the
height coordinate of the pushed barycenter. -/
lemma coordMoment_pushUp_last {d : ℕ} (Q : ((Fin d → ℤ) × Bool) → ℝ)
    (SQ : Finset ((Fin d → ℤ) × Bool)) :
    coordMoment (pushUp Q) (SQ.map liftUpEmb) (Fin.last d)
      = heightMoment Q SQ := by
  simp only [coordMoment, heightMoment, Finset.sum_map, liftUpEmb_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [pushUp_apply, liftUp_apply_last]
  cases y.2 <;> simp

/-- **Shift-distance bridge**: the shift distance of the push-forward, in
a direction embedded at height zero, is the product shift distance of the
source — `Δ(pushUp Q, snoc u 0) = Δprod(Q, u)`. This is what lets Claim
3.2 (k1.5, `shiftDistanceProd_split_le`) apply at the grown dimension:
the induction hypothesis on distances transports without loss. -/
lemma shiftDistance_pushUp {d : ℕ} (Q : ((Fin d → ℤ) × Bool) → ℝ)
    (SQ : Finset ((Fin d → ℤ) × Bool)) (u : Fin d → ℤ) :
    shiftDistance (SQ.map liftUpEmb) (pushUp Q) (Fin.snoc u 0)
      = shiftDistanceProd SQ Q u := by
  simp only [shiftDistance, shiftDistanceProd, Finset.sum_map, liftUpEmb_apply]
  refine congrArg _ (Finset.sum_congr rfl fun y _ => ?_)
  rw [liftUp_add_snoc, pushUp_apply, pushUp_apply]

/-- **Lake form of the oracle's `sum_smul_inl`** (`Komlos/Split.lean`
l.50-53): a sum of scaled vectors, each embedded at height zero by
`snoc · 0`, is itself a vector embedded at height zero — the weighted sum
of the spatial parts, with zero tail.

Measured consumer: `Komlos/SignedSums.lean` l.54, where this identity
separates the height coordinate of the point produced by the induction
hypothesis (`rw [mean_split, sum_smul_inl, ...] at hmem`). -/
lemma sum_smul_snoc {d : ℕ} {ι : Type*} (s : Finset ι)
    (ε : ι → ℝ) (r : ι → (Fin d → ℝ)) :
    ∑ i ∈ s, ε i • Fin.snoc (r i) (0 : ℝ)
      = Fin.snoc (∑ i ∈ s, ε i • r i) (0 : ℝ) := by
  funext j
  induction j using Fin.lastCases with
  | last =>
      simp only [Finset.sum_apply, Pi.smul_apply, Fin.snoc_last, smul_eq_mul,
        mul_zero, Finset.sum_const_zero]
  | cast i =>
      simp only [Fin.snoc_castSucc, Finset.sum_apply, Pi.smul_apply]

/-- **Commutation of the transport with the embedding**: `toReal ∘ liftUp
= snoc ∘ (toReal × height)` — the spatial part is transported by `toReal`
(k2.3), the `Bool` height becomes the real `{0, 1}`.

This closes the square with `toRealProd` (k2.4): the transported image of
the pushed support in `Fin (d+1) → ℝ` is the `(y.1, height y.2)` reading
of the product embedding — the exact place where the dimension-`d+1`
induction conclusion feeds k2.4's `pullback`, stated in
`(Fin d → ℝ) × ℝ`. -/
lemma toReal_liftUp {d : ℕ} (y : (Fin d → ℤ) × Bool) :
    toReal (liftUp y)
      = Fin.snoc (toReal y.1) (if y.2 then (1 : ℝ) else 0) := by
  funext j
  obtain ⟨x, b⟩ := y
  cases b <;> induction j using Fin.lastCases <;> simp [liftUp]

end Discrepancy.Komlos_en
