import Mathlib

/-!
# DaysCircle — the days-of-the-week circle: an irreducible representation of C₇

English mirror of `DaysCircle.lean` (FR-first canonical), EPIC #4980 (i18n
Lean). Convention ratified 2026-07-04 (issue #4980): namespace `DaysCircle_en`.

Slice **R10** of the Tegmark corpus (EPIC #16741, claim #16752):
*Not All Language Model Features Are One-Dimensionally Linear*
(Engels, Michaud, Liao, Gurnee, Tegmark, arXiv:2405.14860).

The paper's central observation: the days-of-the-week feature is not a
one-dimensional direction of the latent space but a **circle** in a 2D
plane — each day is the rotation by angle `2π/7` of the previous one, and
the 7 days occupy 7 distinct positions on the unit circle.

This module formalizes the mathematical structure (Appendix C of the paper):

1. **The orbit of days** — `zeta = exp (2πi/7)` is a primitive 7th root of
   unity (`zeta_primitive`), so the 7 days `day k = zeta ^ k` are
   **distinct** (`day_distinct`) and all live on the **unit circle**
   (`days_on_circle`).
2. **The rotation of days** — `dayRep k : ℂ →ₗ[ℝ] ℂ` (multiplication by
   `zeta ^ k`, ℂ viewed as a 2-dimensional real plane) is the action of
   `C₇ = ZMod 7` on the plane; it sends each day to another day
   (`dayRep_day`): the circle is a homogeneous orbit under `C₇`.
3. **Irreducibility (Appendix C)** — the days-plane admits **no stable real
   line** (`zeta_smul_eq_real_smul_imp`: the rotation ζ has no real
   eigenvector), hence every real subspace stable under the action of `C₇`
   is zero or full (`stable_eq_bot_or_top`). This is exactly the
   irreducibility of the 2D real representation of `C₇`: the paper notes
   that reducibility would amount to a tensor-product decomposition into
   sub-representations — irreducible, the days circle is **genuinely
   two-dimensional**, impossible to split into two independent
   one-dimensional features.

The real plane is `ℂ` (its natural structure as a 2-dimensional ℝ-space);
the rotation by angle `2π/7` is multiplication by `zeta`.

Out of scope: the paper's other circles (months, seasons), the multi-head
construction, and the "tensor product" direction of Appendix C (discursive —
irreducibility is its mathematical content). -/

namespace DaysCircle_en

open Complex

/-- The elementary rotation of the days circle: primitive 7th root of unity.
Day `k+1` is obtained by multiplying by `zeta`. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I * (1 / 7))

/-- `zeta` is a **primitive** 7th root of unity: its orbit
`1, zeta, …, zeta ^ 6` runs through exactly the 7 days before looping. -/
theorem zeta_primitive : IsPrimitiveRoot zeta 7 := by
  simpa [zeta] using
    Complex.isPrimitiveRoot_exp_of_coprime 1 7 (by norm_num) (by norm_num)

/-- The days rotation loops: 7 consecutive rotations bring every day back to
itself. -/
theorem zeta_pow_seven : zeta ^ 7 = 1 :=
  zeta_primitive.pow_eq_one

private theorem two_pi_div_seven_pos : 0 < 2 * Real.pi / 7 :=
  div_pos Real.two_pi_pos (by norm_num)

private theorem two_pi_div_seven_lt_pi : 2 * Real.pi / 7 < Real.pi := by
  rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 7)]
  nlinarith [Real.pi_pos]

private theorem zeta_exp_form :
    zeta = Complex.exp (((2 * Real.pi / 7 : ℝ) : ℂ) * Complex.I) := by
  unfold zeta
  congr 1
  rw [Complex.ofReal_div, Complex.ofReal_mul]
  norm_num
  field_simp

/-- Imaginary part of the rotation: `sin (2π/7)`, strictly positive. -/
theorem zeta_im : zeta.im = Real.sin (2 * Real.pi / 7) := by
  rw [zeta_exp_form]
  simp only [Complex.exp_ofReal_mul_I, Complex.add_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_add, add_zero, mul_one]

/-- The rotation `zeta` is **not real**: no real number can embody it. A
rotation by a nonzero (and non-flat) angle does not project onto the real
axis — this is what will preclude any stable real line. -/
theorem zeta_not_real : ¬∃ r : ℝ, zeta = (r : ℂ) := by
  rintro ⟨r, hr⟩
  have h0 : zeta.im = 0 := by rw [hr]; simp
  rw [zeta_im] at h0
  exact absurd h0 (ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi two_pi_div_seven_pos two_pi_div_seven_lt_pi))

/-- Day `k`: position on the unit circle obtained by `k` elementary
rotations from day `0` (= `1`). -/
noncomputable def day (k : ZMod 7) : ℂ := zeta ^ k.val

/-- The 7 days are **distinct** points of the circle: primitivity
guarantees that no nontrivial rotation fixes a day. -/
theorem day_distinct : Function.Injective day := by
  intro k l h
  have hζ0 : zeta ≠ 0 := Complex.exp_ne_zero _
  have hk : k.val < 7 := ZMod.val_lt k
  have hl : l.val < 7 := ZMod.val_lt l
  unfold day at h
  rcases le_total k.val l.val with hle | hle
  · have hd : zeta ^ (l.val - k.val) = 1 := by
      have hkl : k.val + (l.val - k.val) = l.val := by omega
      refine mul_left_cancel₀ (pow_ne_zero k.val hζ0) ?_
      rw [← pow_add, hkl, h, mul_one]
    rcases Nat.eq_zero_or_pos (l.val - k.val) with h0 | hpos
    · exact ZMod.val_injective 7 (by omega)
    · obtain ⟨c, hc⟩ := zeta_primitive.dvd_of_pow_eq_one _ hd
      omega
  · have hd : zeta ^ (k.val - l.val) = 1 := by
      have hkl : l.val + (k.val - l.val) = k.val := by omega
      refine mul_left_cancel₀ (pow_ne_zero l.val hζ0) ?_
      rw [← pow_add, hkl, h, mul_one]
    rcases Nat.eq_zero_or_pos (k.val - l.val) with h0 | hpos
    · exact ZMod.val_injective 7 (by omega)
    · obtain ⟨c, hc⟩ := zeta_primitive.dvd_of_pow_eq_one _ hd
      omega

/-- All days live on the **unit circle**: the rotation preserves the norm. -/
theorem days_on_circle (k : ZMod 7) : ‖day k‖ = 1 := by
  have hz : ‖zeta‖ = 1 := by
    rw [zeta_exp_form, Complex.norm_exp]
    have h0 : (((2 * Real.pi / 7 : ℝ) : ℂ) * Complex.I).re = 0 := by
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
    rw [h0, Real.exp_zero]
  unfold day
  rw [Complex.norm_pow, hz, one_pow]

private theorem zeta_pow_mod_seven (m : ℕ) : zeta ^ (m % 7) = zeta ^ m := by
  conv_rhs =>
    rw [show m = 7 * (m / 7) + m % 7 from (Nat.div_add_mod m 7).symm]
  rw [pow_add, pow_mul, zeta_pow_seven, one_pow, one_mul]

/-- The days representation: the action of `C₇ = ZMod 7` on the real plane
`ℂ` — day `k` acts as the rotation `z ↦ zeta ^ k * z` (complex
multiplication, real-linear). -/
noncomputable def dayRep (k : ZMod 7) : ℂ →ₗ[ℝ] ℂ where
  toFun z := zeta ^ k.val * z
  map_add' _ _ := by ring
  map_smul' r z := by
    show zeta ^ k.val * (r • z) = r • (zeta ^ k.val * z)
    simp only [Complex.real_smul]
    ring

/-- Evaluation lemma: `dayRep` is multiplication by `zeta ^ k`. -/
theorem dayRep_apply (k : ZMod 7) (z : ℂ) :
    dayRep k z = zeta ^ k.val * z := rfl

/-- The representation rotates days into each other: acting by `k` on day
`l` yields day `k + l`. The circle is a homogeneous orbit under `C₇`. -/
theorem dayRep_day (k l : ZMod 7) : dayRep k (day l) = day (k + l) := by
  simp only [dayRep_apply, day]
  have hv : (k + l).val = (k.val + l.val) % 7 := ZMod.val_add k l
  rw [hv, ← pow_add]
  exact (zeta_pow_mod_seven _).symm

/-- **Irreducibility, key step (Appendix C)**: the rotation `zeta` has no
nonzero real eigenvector — every real line of the plane is spread out by the
rotation. This is the obstruction to a "one-dimensional" feature. -/
theorem zeta_smul_eq_real_smul_imp {v : ℂ} {r : ℝ} (h : zeta * v = r • v) :
    v = 0 := by
  by_contra hv
  have hz : zeta = (r : ℂ) := by
    have hmul : (zeta - (r : ℂ)) * v = 0 := by
      rw [sub_mul, ← Complex.real_smul]
      linear_combination h
    rcases mul_eq_zero.mp hmul with h1 | h2
    · exact sub_eq_zero.mp h1
    · exact absurd h2 hv
  exact zeta_not_real ⟨r, hz⟩

/-- **Irreducibility of the days representation (Appendix C)**: every real
subspace of the plane stable under the action of `C₇` (the days rotation)
is zero or full. The days plane is **genuinely two-dimensional**: no real
direction — no "one-dimensional feature" — carries the group action. -/
theorem stable_eq_bot_or_top {p : Submodule ℝ ℂ}
    (hstab : ∀ k : ZMod 7, Submodule.map (dayRep k) p ≤ p) :
    p = ⊥ ∨ p = ⊤ := by
  by_contra hcon
  have hbot : p ≠ ⊥ := fun hb => hcon (Or.inl hb)
  have htop : p ≠ ⊤ := fun ht => hcon (Or.inr ht)
  have hfact : Fact (1 < 7) := ⟨by norm_num⟩
  obtain ⟨v, hvmem, hv0⟩ := (Submodule.ne_bot_iff p).mp hbot
  -- the rotation maps p into p: zeta * v ∈ p
  have hζmem : zeta * v ∈ p := by
    refine (hstab 1) ((Submodule.mem_map).mpr ⟨v, hvmem, ?_⟩)
    rw [dayRep_apply, ZMod.val_one, pow_one]
  -- p is proper and nonzero in a plane: dimension exactly 1 (a line)
  have hlt : Module.finrank ℝ ↥p < Module.finrank ℝ ℂ :=
    Submodule.finrank_lt htop
  rw [Complex.finrank_real_complex] at hlt
  have hspanle : (ℝ ∙ v) ≤ p :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvmem)
  have hone : Module.finrank ℝ ↥(ℝ ∙ v) = 1 := finrank_span_singleton hv0
  have hge : 1 ≤ Module.finrank ℝ ↥p :=
    le_trans hone.symm.le (Submodule.finrank_mono hspanle)
  have hdim : Module.finrank ℝ ↥p = 1 := by omega
  -- hence p = ℝ ∙ v: a line
  have hpe : (ℝ ∙ v) = p :=
    Submodule.eq_of_le_of_finrank_eq hspanle
      (by rw [finrank_span_singleton hv0, hdim])
  -- and zeta * v, an element of p, would be collinear with v: real eigenvector
  rw [← hpe] at hζmem
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hζmem
  exact absurd (zeta_smul_eq_real_smul_imp hr.symm) hv0

end DaysCircle_en
