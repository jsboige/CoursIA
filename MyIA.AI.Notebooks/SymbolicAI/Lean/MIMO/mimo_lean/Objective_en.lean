import Mathlib

/-!
# MIMO objective function — Phase 2: Lemma 11.1 (flip cost), with Mathlib

This module instantiates the objective function of the MIMO flip detector
(Papailiopoulos, 2026 — issue #10984) and proves **Lemma 11.1**: the cost of
a coordinate flip admits the closed form

    f(1⁽ⁱ⁾) − f(1) = 4·(s·‖hᵢ‖² + √s·⟪hᵢ, w⟫)

where `s = ρ/N`, `hᵢ` is the i-th column of the channel (the image of the
i-th basis vector under the channel's linear map) and `w` the noise.

File architecture:

1. `norm_add_sq_two` — real Pythagoras: `‖x + y‖² = ‖x‖² + 2⟪x,y⟫ + ‖y‖²`
   (re-derived from Mathlib's basic lemmas for pedagogical self-containment);
2. `flip_cost` — the **generic** geometric core: in any real Hilbert space,
   `‖w + 2√s•h‖² − ‖w‖² = 4·(s·‖h‖² + √s·⟪h,w⟫)` — Lemma 11.1 stripped of
   the MIMO structure;
3. `mimoObj` / `flipAt` — the concrete objective on
   `EuclideanSpace ℝ (Fin N)` (channel = linear map) and a flip's deviation
   vector;
4. `mimo_flip_cost` — **Lemma 11.1** instantiated;
5. `flip_accepted_iff` — the algorithm's control loop: a flip is accepted
   iff the flip score `s·‖hᵢ‖² + √s·⟪hᵢ,w⟫` is strictly negative — exactly
   the `hstrict` hypothesis consumed by Proposition 9.1 of Phase 1
   (`Descent.lean`).

Lemma 5.1 (LMMSE error `E‖b − x*‖² = E tr(B_ρ)`) and the §11 converse land
with Phase 3 (external SLT lake, Gaussian concentration).
-/

namespace Mimo_en

open InnerProductSpace

section Geometrie

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Real Pythagoras**: `‖x + y‖² = ‖x‖² + 2·⟪x, y⟫_ℝ + ‖y‖²`. Re-derived from the fundamental lemmas (`inner_add_left/right`, `real_inner_comm`) rather than invoked — every step readable by a student. -/
theorem norm_add_sq_two (x y : E) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y⟫_ℝ + ‖y‖ ^ 2 := by
  have h : ∀ z : E, ‖z‖ ^ 2 = ⟪z, z⟫_ℝ := fun z => (real_inner_self_eq_norm_sq z).symm
  rw [h (x + y), h x, h y, inner_add_left, inner_add_right,
    inner_add_right, real_inner_comm y x]
  ring

/-- **Geometric core of Lemma 11.1 (generic form).** For a noise `w`, a column direction `h` and a per-antenna SNR `s ≥ 0`, the cost of flipping along `h` is

    ‖w + 2√s • h‖² − ‖w‖² = 4·(s·‖h‖² + √s·⟪h, w⟫_ℝ).

The quantity in parentheses is exactly the **flip score**: negative ⟺ the flip strictly decreases the objective function. -/
theorem flip_cost (w h : E) {s : ℝ} (hs : 0 ≤ s) :
    ‖w + (2 * √s) • h‖ ^ 2 - ‖w‖ ^ 2 = 4 * (s * ‖h‖ ^ 2 + √s * ⟪h, w⟫_ℝ) := by
  have key := norm_add_sq_two w ((2 * √s) • h)
  rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs] at key
  rw [key, mul_pow, sq_abs, mul_pow, Real.sq_sqrt hs]
  rw [real_inner_comm w h]
  ring

end Geometrie

section MIMO

variable {N M : ℕ}

/-- Detector objective function: `obj A w s u = ‖w + √s • A u‖²` where
`A` is the channel linear map (from signal space `(Fin N → ℝ)` to
measurement space `EuclideanSpace ℝ (Fin M)`), `w` the noise,
`s = ρ/N` the per-antenna SNR, and `u` the **deviation vector** from the
starting point (`u = 1 − x`: zero = starting point, `2eᵢ` = i-th
coordinate flipped). -/
noncomputable def mimoObj (A : (Fin N → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin M))
    (w : EuclideanSpace ℝ (Fin M)) (s : ℝ) (u : Fin N → ℝ) : ℝ :=
  ‖w + √s • A u‖ ^ 2

/-- Deviation vector of flipping the i-th coordinate: `2·eᵢ` in signal
space. -/
def flipAt (i : Fin N) : Fin N → ℝ :=
  (2 : ℝ) • Pi.single i 1

/-- **Lemma 11.1 (Papailiopoulos 2026) — cost of a flip.** Moving from the
starting configuration to the i-th flipped configuration changes the
objective by

    Δf = 4·(s·‖hᵢ‖² + √s·⟪hᵢ, w⟫_ℝ)

where `hᵢ = A eᵢ` is the i-th channel column. Exact closed form — the
proof instantiates the generic geometric lemma `flip_cost`. -/
theorem mimo_flip_cost (A : (Fin N → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin M))
    (w : EuclideanSpace ℝ (Fin M)) {s : ℝ} (hs : 0 ≤ s) (i : Fin N) :
    mimoObj A w s (flipAt i) - mimoObj A w s 0
      = 4 * (s * ‖A (Pi.single i 1)‖ ^ 2
             + √s * ⟪A (Pi.single i 1), w⟫_ℝ) := by
  have hA : A (flipAt i) = (2 : ℝ) • A (Pi.single i 1) :=
    LinearMap.map_smul A 2 _
  show ‖w + √s • A (flipAt i)‖ ^ 2 - ‖w + √s • A 0‖ ^ 2 = _
  rw [hA, smul_smul, LinearMap.map_zero, smul_zero, add_zero, mul_comm √s 2]
  exact flip_cost w (A (Pi.single i 1)) hs

/-- **Algorithm control loop.** A flip of the i-th coordinate is
**accepted** (strictly decreases the objective) if and only if the flip
score `s·‖hᵢ‖² + √s·⟪hᵢ,w⟫` is strictly negative. This is the `hstrict`
hypothesis consumed by the Phase 1 Proposition 9.1 (`Descent.lean`):
only negative-score flips are accepted, so the cost strictly decreases
along a run. -/
theorem flip_accepted_iff (A : (Fin N → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin M))
    (w : EuclideanSpace ℝ (Fin M)) {s : ℝ} (hs : 0 ≤ s) (i : Fin N) :
    mimoObj A w s (flipAt i) < mimoObj A w s 0 ↔
      s * ‖A (Pi.single i 1)‖ ^ 2
        + √s * ⟪A (Pi.single i 1), w⟫_ℝ < 0 := by
  constructor
  · intro hlt
    have h4 : mimoObj A w s (flipAt i) - mimoObj A w s 0 < 0 := sub_neg.mpr hlt
    rw [mimo_flip_cost A w hs i] at h4
    linarith
  · intro hlt
    have h4 : 4 * (s * ‖A (Pi.single i 1)‖ ^ 2
        + √s * ⟪A (Pi.single i 1), w⟫_ℝ) < 0 := by linarith
    rw [← mimo_flip_cost A w hs i] at h4
    exact sub_neg.mp h4

end MIMO

end Mimo_en
