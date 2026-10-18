import Formalization.Analysis.TriadConservation
import Formalization.Analysis.RoPECoherence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Project DarkSnail: Skew-Symmetric Color-Occlusion Triad & 2D Axial RoPE Coherence

This module formalizes the core mathematical synthesis of **Project DarkSnail**
(System 2 Ultrametric & Continuous-Time Triad Reasoning on ARC-AGI):

1. **Skew-Symmetric Color-Occlusion Antisymmetry (`skew_triad_swap_neg`)**:
   For the skew-symmetrized color-occlusion interaction tensor
   $$S(W, i, c_1, c_2) = W(i, c_1, c_2) - W(i, c_2, c_1),$$
   swapping competing foreground colors $c_1 \leftrightarrow c_2$ strictly negates the interaction
   ($S(W, i, c_2, c_1) = -S(W, i, c_1, c_2)$) and self-interaction vanishes identically
   ($S(W, i, c, c) = 0$).

2. **Exact Tie-Breaking of Symmetric Readout Collisions (`occlusion_triad_breaks_symmetric_tie`)**:
   Whereas any additive or symmetric readout $\ell_{\mathrm{sym}}(c_1) = \ell_{\mathrm{sym}}(c_2)$
   cannot distinguish which of two colliding foreground colors $c_1, c_2$ occludes the other at a
   shared pixel, the DarkSnail bilinear triad readout shift
   $$\ell_{\mathrm{post}}(k) = \ell_{\mathrm{sym}}(k) + B_W(u, v)_k$$
   produces an exact antisymmetric margin
   $$\ell_{\mathrm{post}}(c_1) - \ell_{\mathrm{post}}(c_2)
     = 2 \beta \alpha \bigl(W(i_0, c_2, c_1) - W(i_0, c_1, c_2)\bigr),$$
   strictly breaking the 2-color occlusion tie whenever $W(i_0, c_2, c_1) > W(i_0, c_1, c_2)$.

3. **Zero-Energy-Explosion Orthogonality (`darksnail_readout_energy_conservation`)**:
   By `triad_pointwise_orthogonal`, the DarkSnail triad logit shift is strictly orthogonal to the
   active color probability state $v$ ($\langle v, B_W(u, v) \rangle = 0$), and the Slow-Fast
   ($z_H \to z_L$) recurrent triad pump $\dot{z}_L = B_{W_{\mathrm{rec}}}(z_H, z_L)$ has zero
   radial energy growth ($\langle z_L, \dot{z}_L \rangle = 0$).

4. **Step-0 System 1 Homotopy Equivalence (`darksnail_step0_system1_homotopy`)**:
   At the Step-0 initialization ($\Delta_{\mathrm{sym}} = 0$, $W = 0$), the full DarkSnail readout
   reduces identically to the pretrained System 1 baseline logit $\ell_{\mathrm{S1}}(k)$.

5. **2D Axial RoPE Medoid Invariance & Patch-Averaging Attenuation
   (`rope2d_medoid_relative_invariance`, `rope2d_arithmetic_norm_lt`)**:
   In 2D grid coordinates $(y, x)$, selecting a 2D medoid key preserves exact relative 2D
   rotational displacement $(y^* - y_q, x^* - x_q)$ across both vertical and horizontal axes,
   whereas arithmetic patch averaging across distinct 2D grid phases strictly attenuates the
   squared 2D key norm.
-/

namespace Ultrametric.Analysis.OcclusionTriad

open scoped BigOperators
open Real Finset

/-- Explicit-dimension wrapper around `Formalization.Analysis.triadOperator`:
$$B_W(u, v)_k = \sum_{i, j \in \mathrm{Fin}\,C} u_i v_j (W_{i,j,k} - W_{i,k,j}).$$ -/
def triadOperator (C : ℕ) (W : Fin C → Fin C → Fin C → ℝ)
    (u v : Fin C → ℝ) (k : Fin C) : ℝ :=
  Formalization.Analysis.triadOperator W u v k

/-- Skew-symmetrized color-occlusion interaction tensor
$$S(W, i, c_1, c_2) = W(i, c_1, c_2) - W(i, c_2, c_1)$$
representing the directed occlusion dominance of color $c_2$ over $c_1$ under structural mode $i$. -/
def skewTriad {C : ℕ} (W : Fin C → Fin C → Fin C → ℝ) (i c₁ c₂ : Fin C) : ℝ :=
  W i c₁ c₂ - W i c₂ c₁

/-! ### Theorem 1: Skew-Symmetric Color-Occlusion Antisymmetry -/

/-- **Theorem 1 (`skew_triad_swap_neg`)**:
For the skew-symmetrized color-occlusion interaction $S(W, i, c_1, c_2) = W(i, c_1, c_2) - W(i, c_2, c_1)$,
swapping $c_1 \leftrightarrow c_2$ negates the interaction:
$$S(W, i, c_2, c_1) = -S(W, i, c_1, c_2),$$
and self-interaction vanishes identically:
$$S(W, i, c_1, c_1) = 0.$$ -/
theorem skew_triad_swap_neg {C : ℕ} (W : Fin C → Fin C → Fin C → ℝ) (i c₁ c₂ : Fin C) :
    skewTriad W i c₂ c₁ = -skewTriad W i c₁ c₂ ∧ skewTriad W i c₁ c₁ = 0 := by
  unfold skewTriad
  constructor <;> ring

/-- Self-occlusion interaction vanishes for any color $c$. -/
theorem skew_triad_self_zero {C : ℕ} (W : Fin C → Fin C → Fin C → ℝ) (i c : Fin C) :
    skewTriad W i c c = 0 :=
  (skew_triad_swap_neg W i c c).2

/-! ### Theorem 2: Exact Tie-Breaking of Symmetric 2-Color Collisions -/

/-- DarkSnail post-readout logit combining a symmetric/additive baseline logit $\ell_{\mathrm{sym}}$
with the skew-symmetric bilinear triad shift $B_W(u, v)$. -/
def postLogit (C : ℕ) (ℓ_sym : Fin C → ℝ) (W : Fin C → Fin C → Fin C → ℝ)
    (u v : Fin C → ℝ) (k : Fin C) : ℝ :=
  ℓ_sym k + triadOperator C W u v k

/-- Helper lemma: evaluation of `triadOperator` under a single active structural mode $u(i_0) = \beta$
and a 2-color collision state $v(c_1) = v(c_2) = \alpha$ (with $c_1 \neq c_2$). -/
lemma triadOperator_two_color_eval {C : ℕ} (W : Fin C → Fin C → Fin C → ℝ)
    (u v : Fin C → ℝ) (i₀ c₁ c₂ k : Fin C) (α β : ℝ)
    (hc : c₁ ≠ c₂)
    (hu_i0 : u i₀ = β)
    (hu_other : ∀ i : Fin C, i ≠ i₀ → u i = 0)
    (hv_c1 : v c₁ = α)
    (hv_c2 : v c₂ = α)
    (hv_other : ∀ c : Fin C, c ≠ c₁ → c ≠ c₂ → v c = 0) :
    triadOperator C W u v k =
      β * α * (W i₀ c₁ k - W i₀ k c₁) + β * α * (W i₀ c₂ k - W i₀ k c₂) := by
  unfold triadOperator Formalization.Analysis.triadOperator
  rw [Finset.sum_eq_single i₀]
  · have h_mem1 : c₁ ∈ (Finset.univ : Finset (Fin C)) := Finset.mem_univ c₁
    rw [← Finset.add_sum_erase _ _ h_mem1]
    have h_mem2 : c₂ ∈ (Finset.univ : Finset (Fin C)).erase c₁ :=
      Finset.mem_erase.mpr ⟨Ne.symm hc, Finset.mem_univ c₂⟩
    rw [← Finset.add_sum_erase _ _ h_mem2]
    have h_rest :
        ∑ j ∈ ((Finset.univ : Finset (Fin C)).erase c₁).erase c₂,
          u i₀ * v j * (W i₀ j k - W i₀ k j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hj2 : j ≠ c₂ := (Finset.mem_erase.mp hj).1
      have hj1 : j ≠ c₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      rw [hv_other j hj1 hj2]
      ring
    rw [h_rest, add_zero, hu_i0, hv_c1, hv_c2]
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    rw [hu_other i hi]
    ring
  · intro h_absurd
    exact False.elim (h_absurd (Finset.mem_univ i₀))

/-- **Theorem 2 (`occlusion_triad_breaks_symmetric_tie`)**:
Let $\ell_{\mathrm{sym}} : \mathrm{Fin}\,C \to \mathbb{R}$ be any symmetric/additive readout logit vector
that ties on two competing foreground colors $c_1, c_2$ ($\ell_{\mathrm{sym}}(c_1) = \ell_{\mathrm{sym}}(c_2)$).
In a 2-color collision state $v(c_1) = v(c_2) = \alpha > 0$ (and $v(c) = 0$ for $c \notin \{c_1, c_2\}$)
under a single structural mode $u(i_0) = \beta > 0$ (and $u(i) = 0$ for $i \neq i_0$), the DarkSnail
post-readout logit $\ell_{\mathrm{post}}(k) = \ell_{\mathrm{sym}}(k) + \mathrm{triadOperator}\,C\,W\,u\,v\,k$
satisfies:
$$\ell_{\mathrm{post}}(c_1) - \ell_{\mathrm{post}}(c_2) = 2 \cdot \beta \cdot \alpha \cdot (W(i_0, c_2, c_1) - W(i_0, c_1, c_2)),$$
and whenever $W(i_0, c_2, c_1) > W(i_0, c_1, c_2)$, we strictly have
$$\ell_{\mathrm{post}}(c_1) > \ell_{\mathrm{post}}(c_2).$$ -/
theorem occlusion_triad_breaks_symmetric_tie {C : ℕ}
    (ℓ_sym : Fin C → ℝ) (W : Fin C → Fin C → Fin C → ℝ)
    (u v : Fin C → ℝ) (i₀ c₁ c₂ : Fin C) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (h_tie : ℓ_sym c₁ = ℓ_sym c₂)
    (hu_i0 : u i₀ = β)
    (hu_other : ∀ i : Fin C, i ≠ i₀ → u i = 0)
    (hv_c1 : v c₁ = α)
    (hv_c2 : v c₂ = α)
    (hv_other : ∀ c : Fin C, c ≠ c₁ → c ≠ c₂ → v c = 0) :
    (postLogit C ℓ_sym W u v c₁ - postLogit C ℓ_sym W u v c₂ =
      2 * β * α * (W i₀ c₂ c₁ - W i₀ c₁ c₂)) ∧
    (W i₀ c₂ c₁ > W i₀ c₁ c₂ →
      postLogit C ℓ_sym W u v c₁ > postLogit C ℓ_sym W u v c₂) := by
  have h_diff :
      postLogit C ℓ_sym W u v c₁ - postLogit C ℓ_sym W u v c₂ =
        2 * β * α * (W i₀ c₂ c₁ - W i₀ c₁ c₂) := by
    by_cases hc : c₁ = c₂
    · subst hc
      ring
    · unfold postLogit
      rw [triadOperator_two_color_eval W u v i₀ c₁ c₂ c₁ α β hc hu_i0 hu_other hv_c1 hv_c2 hv_other,
          triadOperator_two_color_eval W u v i₀ c₁ c₂ c₂ α β hc hu_i0 hu_other hv_c1 hv_c2 hv_other,
          h_tie]
      ring
  refine ⟨h_diff, fun hW => ?_⟩
  have h_pos : 0 < 2 * β * α * (W i₀ c₂ c₁ - W i₀ c₁ c₂) := by
    have h_sub : 0 < W i₀ c₂ c₁ - W i₀ c₁ c₂ := sub_pos.mpr hW
    positivity
  linarith

/-! ### Theorem 3: DarkSnail Readout & Recurrent Triad Energy Conservation -/

/-- **Theorem 3 (`darksnail_readout_energy_conservation`)**:
For any structural vector $u$, color state $v$, and triad tensor $W$, the inner product of $v$
with the DarkSnail triad logit shift vanishes identically:
$$\sum_{k \in \mathrm{Fin}\,C} v(k) \cdot (\mathrm{triadOperator}\,C\,W\,u\,v\,k) = 0,$$
and for the Slow-Fast ($z_H \to z_L$) recurrent terminal step
$\dot{z}_L = \mathrm{triadOperator}\,M\,W_{\mathrm{rec}}\,z_H\,z_L$, the radial energy growth rate
$\langle z_L, \dot{z}_L \rangle$ vanishes identically. -/
theorem darksnail_readout_energy_conservation {C M : ℕ}
    (W : Fin C → Fin C → Fin C → ℝ) (u v : Fin C → ℝ)
    (W_rec : Fin M → Fin M → Fin M → ℝ) (z_H z_L : Fin M → ℝ) :
    (∑ k : Fin C, v k * triadOperator C W u v k) = 0 ∧
    Formalization.Analysis.shellInner z_L (triadOperator M W_rec z_H z_L) = 0 := by
  constructor
  · exact Formalization.Analysis.triad_pointwise_orthogonal W u v
  · exact Formalization.Analysis.triad_pointwise_orthogonal W_rec z_H z_L

/-! ### Theorem 4: Step-0 System 1 Homotopy Equivalence -/

/-- Full DarkSnail readout combining pretrained System 1 logits $\ell_{\mathrm{S1}}$,
symmetric residual shift $\Delta_{\mathrm{sym}}$, and skew-symmetric triad readout shift. -/
def darksnailReadout (C : ℕ) (ℓ_S1 Δ_sym : Fin C → ℝ)
    (W : Fin C → Fin C → Fin C → ℝ) (u v : Fin C → ℝ) (k : Fin C) : ℝ :=
  ℓ_S1 k + Δ_sym k + triadOperator C W u v k

/-- **Theorem 4 (`darksnail_step0_system1_homotopy`)**:
At the Step-0 initialization $\Delta_{\mathrm{sym}} = 0$ and $W = 0$ (corresponding to $\delta z = 0$),
the DarkSnail readout equals the pretrained System 1 logit identically for all colors $k$:
$$\ell_{\mathrm{DS}}(\ell_{\mathrm{S1}}, 0, 0, u, v, k) = \ell_{\mathrm{S1}}(k).$$ -/
theorem darksnail_step0_system1_homotopy {C : ℕ}
    (ℓ_S1 u v : Fin C → ℝ) (k : Fin C) :
    darksnailReadout C ℓ_S1 0 0 u v k = ℓ_S1 k := by
  unfold darksnailReadout triadOperator Formalization.Analysis.triadOperator
  simp

/-! ### Theorem 5: 2D Axial RoPE Medoid Invariance & Patch-Averaging Attenuation -/

/-- 2D rotation on $\mathbb{R} \times \mathbb{R}$ by angle $\theta$. -/
noncomputable def rot2 (θ : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (Real.cos θ * v.1 - Real.sin θ * v.2, Real.sin θ * v.1 + Real.cos θ * v.2)

/-- Standard inner product on $\mathbb{R} \times \mathbb{R}$. -/
def inner2 (u v : ℝ × ℝ) : ℝ :=
  u.1 * v.1 + u.2 * v.2

/-- Squared Euclidean norm on $\mathbb{R} \times \mathbb{R}$. -/
def normSq2 (v : ℝ × ℝ) : ℝ :=
  inner2 v v

/-- 2D axial RoPE embedding on $(\mathbb{R} \times \mathbb{R}) \times (\mathbb{R} \times \mathbb{R})$
applying vertical rotation $\theta_y$ to the $y$-slice and horizontal rotation $\theta_x$ to the $x$-slice. -/
noncomputable def rope2d (θ_y θ_x : ℝ) (q_y q_x : ℝ × ℝ) : (ℝ × ℝ) × (ℝ × ℝ) :=
  (rot2 θ_y q_y, rot2 θ_x q_x)

/-- 2D axial inner product summing the vertical and horizontal slice inner products. -/
def inner2d (u v : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  inner2 u.1 v.1 + inner2 u.2 v.2

/-- Squared Euclidean norm on the 2D axial space $(\mathbb{R} \times \mathbb{R}) \times (\mathbb{R} \times \mathbb{R})$. -/
def normSq2d (v : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  normSq2 v.1 + normSq2 v.2

/-- Arithmetic midpoint of two 2D vectors. -/
noncomputable def avg2 (u v : ℝ × ℝ) : ℝ × ℝ :=
  ((u.1 + v.1) / 2, (u.2 + v.2) / 2)

/-- 2D arithmetic patch average of a key $(k_y, k_x)$ across two 2D grid phases $(\theta_{y,1}, \theta_{x,1})$
and $(\theta_{y,2}, \theta_{x,2})$. -/
noncomputable def rope2dPatchAvg (θ_y1 θ_x1 θ_y2 θ_x2 : ℝ) (k_y k_x : ℝ × ℝ) : (ℝ × ℝ) × (ℝ × ℝ) :=
  (avg2 (rot2 θ_y1 k_y) (rot2 θ_y2 k_y), avg2 (rot2 θ_x1 k_x) (rot2 θ_x2 k_x))

/-- Single-axis rotational shift invariance for `rot2` and `inner2`. -/
lemma inner2_rot2_shift (α β : ℝ) (u v : ℝ × ℝ) :
    inner2 (rot2 α u) (rot2 β v) = inner2 u (rot2 (β - α) v) := by
  unfold inner2 rot2
  rw [Real.cos_sub, Real.sin_sub]
  ring

/-- **Theorem 5a (`rope2d_medoid_relative_invariance`)**:
For any query at 2D angular coordinate $(y_q, x_q)$ and 2D medoid key at coordinate $(y^*, x^*)$,
the 2D axial rotary inner product is invariant under global grid translation and depends purely on
the relative 2D displacement $(y^* - y_q, x^* - x_q)$:
$$\langle \mathrm{rope2d}(y_q, x_q, q_y, q_x), \mathrm{rope2d}(y^*, x^*, k_y, k_x) \rangle
  = \langle q_y, \mathcal{R}_{y^* - y_q} k_y \rangle + \langle q_x, \mathcal{R}_{x^* - x_q} k_x \rangle.$$ -/
theorem rope2d_medoid_relative_invariance
    (y_q x_q y_star x_star : ℝ) (q_y q_x k_y k_x : ℝ × ℝ) :
    inner2d (rope2d y_q x_q q_y q_x) (rope2d y_star x_star k_y k_x) =
      inner2 q_y (rot2 (y_star - y_q) k_y) + inner2 q_x (rot2 (x_star - x_q) k_x) := by
  unfold inner2d rope2d
  rw [inner2_rot2_shift, inner2_rot2_shift]

/-- Exact squared norm identity for the 2-point arithmetic average of rotated 2D vectors:
$$\left\|\frac{\mathcal{R}_{\theta_1} k + \mathcal{R}_{\theta_2} k}{2}\right\|^2
  = \|k\|^2 \cdot \frac{1 + \cos(\theta_1 - \theta_2)}{2}.$$ -/
lemma normSq2_avg2_rot2 (θ₁ θ₂ : ℝ) (k : ℝ × ℝ) :
    normSq2 (avg2 (rot2 θ₁ k) (rot2 θ₂ k)) =
      normSq2 k * (1 + Real.cos (θ₁ - θ₂)) / 2 := by
  unfold normSq2 inner2 avg2 rot2
  rw [Real.cos_sub]
  linear_combination
    ((k.1 ^ 2 + k.2 ^ 2) / 4) * (Real.cos_sq_add_sin_sq θ₁) +
    ((k.1 ^ 2 + k.2 ^ 2) / 4) * (Real.cos_sq_add_sin_sq θ₂)

/-- Non-negativity of `normSq2`. -/
lemma normSq2_nonneg (k : ℝ × ℝ) : 0 ≤ normSq2 k := by
  unfold normSq2 inner2
  nlinarith [mul_self_nonneg k.1, mul_self_nonneg k.2]

/-- Non-expansion of single-axis arithmetic average squared norm. -/
lemma normSq2_avg2_rot2_le (θ₁ θ₂ : ℝ) (k : ℝ × ℝ) :
    normSq2 (avg2 (rot2 θ₁ k) (rot2 θ₂ k)) ≤ normSq2 k := by
  rw [normSq2_avg2_rot2]
  have hcos : Real.cos (θ₁ - θ₂) ≤ 1 := Real.cos_le_one (θ₁ - θ₂)
  have hk : 0 ≤ normSq2 k := normSq2_nonneg k
  nlinarith

/-- Strict attenuation of single-axis arithmetic average squared norm when $\cos(\theta_1 - \theta_2) < 1$
and $\|k\|^2 > 0$. -/
lemma normSq2_avg2_rot2_lt (θ₁ θ₂ : ℝ) (k : ℝ × ℝ)
    (hcos : Real.cos (θ₁ - θ₂) < 1) (hk : 0 < normSq2 k) :
    normSq2 (avg2 (rot2 θ₁ k) (rot2 θ₂ k)) < normSq2 k := by
  rw [normSq2_avg2_rot2]
  nlinarith

/-- **Theorem 5b (`rope2d_arithmetic_norm_lt`)**:
Whenever either the vertical phase difference satisfies $\cos(\theta_{y,1} - \theta_{y,2}) < 1$ with
$\|k_y\|^2 > 0$, or the horizontal phase difference satisfies $\cos(\theta_{x,1} - \theta_{x,2}) < 1$
with $\|k_x\|^2 > 0$, 2D arithmetic patch averaging strictly attenuates the squared 2D key norm:
$$\|\mathrm{rope2dPatchAvg}(\theta_{y,1}, \theta_{x,1}, \theta_{y,2}, \theta_{x,2}, k_y, k_x)\|^2
  < \|(k_y, k_x)\|^2.$$ -/
theorem rope2d_arithmetic_norm_lt
    (θ_y1 θ_x1 θ_y2 θ_x2 : ℝ) (k_y k_x : ℝ × ℝ)
    (h_att : (Real.cos (θ_y1 - θ_y2) < 1 ∧ 0 < normSq2 k_y) ∨
             (Real.cos (θ_x1 - θ_x2) < 1 ∧ 0 < normSq2 k_x)) :
    normSq2d (rope2dPatchAvg θ_y1 θ_x1 θ_y2 θ_x2 k_y k_x) < normSq2d (k_y, k_x) := by
  unfold normSq2d rope2dPatchAvg
  rcases h_att with ⟨hcy, hky⟩ | ⟨hcx, hkx⟩
  · have hy := normSq2_avg2_rot2_lt θ_y1 θ_y2 k_y hcy hky
    have hx := normSq2_avg2_rot2_le θ_x1 θ_x2 k_x
    linarith
  · have hy := normSq2_avg2_rot2_le θ_y1 θ_y2 k_y
    have hx := normSq2_avg2_rot2_lt θ_x1 θ_x2 k_x hcx hkx
    linarith

/-! ### Theorem 6: Multi-Step Unrolled Slow-Fast Spherical Invariance & Step-0 Homotopy -/

/-- Scaled tangent triad step $\delta v_k = \gamma \cdot B_{W_{\mathrm{rec}}}(u, v)_k$. -/
def tangentTriadStep (M : ℕ) (γ : ℝ) (W_rec : Fin M → Fin M → Fin M → ℝ)
    (u v : Fin M → ℝ) (k : Fin M) : ℝ :=
  γ * triadOperator M W_rec u v k

/-- Spherical norm retraction $\tilde{v}_k = \frac{\|v\|_2}{\|v_{\mathrm{upd}}\|_2} v_{\mathrm{upd}, k}$. -/
noncomputable def sphericalRetract {M : ℕ} (v v_upd : Fin M → ℝ) (k : Fin M) : ℝ :=
  (Real.sqrt (Formalization.Analysis.shellEnergy v) /
   Real.sqrt (Formalization.Analysis.shellEnergy v_upd)) * v_upd k

/-- Single-step tangent triad update followed by spherical norm retraction:
$$\tilde{v}_L = \frac{\|v_L\|_2}{\|v_L + \delta v_L\|_2} (v_L + \delta v_L), \qquad
  \delta v_L = \gamma B_{W_{\mathrm{rec}}}(u, v_L).$$ -/
noncomputable def sphericalTriadStep (M : ℕ) (γ : ℝ) (W_rec : Fin M → Fin M → Fin M → ℝ)
    (u v : Fin M → ℝ) : Fin M → ℝ :=
  let δv := tangentTriadStep M γ W_rec u v
  sphericalRetract v (fun k => v k + δv k)

/-- $T$-step unrolled Slow-Fast spherical triad trajectory $\tilde{v}_L^{(t)}$. -/
noncomputable def multistepSphericalTriad (M : ℕ) (γ : ℕ → ℝ)
    (W_rec : ℕ → Fin M → Fin M → Fin M → ℝ)
    (u : ℕ → Fin M → ℝ) (v₀ : Fin M → ℝ) : ℕ → (Fin M → ℝ)
  | 0 => v₀
  | t + 1 =>
      let v_t := multistepSphericalTriad M γ W_rec u v₀ t
      sphericalTriadStep M (γ t) (W_rec t) (u t) v_t

/-- Non-negativity of `shellEnergy`. -/
lemma shellEnergy_nonneg {M : ℕ} (x : Fin M → ℝ) :
    0 ≤ Formalization.Analysis.shellEnergy x := by
  unfold Formalization.Analysis.shellEnergy Formalization.Analysis.shellInner
  exact Finset.sum_nonneg (fun k _ => mul_self_nonneg (x k))

/-- `shellEnergy x = 0` if and only if $x$ vanishes pointwise. -/
lemma shellEnergy_eq_zero_iff {M : ℕ} (x : Fin M → ℝ) :
    Formalization.Analysis.shellEnergy x = 0 ↔ ∀ k : Fin M, x k = 0 := by
  unfold Formalization.Analysis.shellEnergy Formalization.Analysis.shellInner
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_self_nonneg (x k))]
  simp

/-- Pointwise orthogonality $\langle v, \delta v \rangle = 0$ for the scaled tangent triad step. -/
lemma tangentTriadStep_orthogonal {M : ℕ} (γ : ℝ) (W_rec : Fin M → Fin M → Fin M → ℝ)
    (u v : Fin M → ℝ) :
    Formalization.Analysis.shellInner v (tangentTriadStep M γ W_rec u v) = 0 := by
  have h_orth := Formalization.Analysis.triad_pointwise_orthogonal W_rec u v
  have h_scale :
      Formalization.Analysis.shellInner v (tangentTriadStep M γ W_rec u v) =
        γ * Formalization.Analysis.shellInner v (Formalization.Analysis.triadOperator W_rec u v) := by
    unfold Formalization.Analysis.shellInner tangentTriadStep triadOperator
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [h_scale, h_orth, mul_zero]

/-- Discrete-time Pythagorean identity under orthogonal tangent updates $\langle v, \delta v \rangle = 0$. -/
lemma shellEnergy_add_of_orthogonal {M : ℕ} (v δv : Fin M → ℝ)
    (h_orth : Formalization.Analysis.shellInner v δv = 0) :
    Formalization.Analysis.shellEnergy (fun k => v k + δv k) =
      Formalization.Analysis.shellEnergy v + Formalization.Analysis.shellEnergy δv := by
  have h_expand :
      Formalization.Analysis.shellEnergy (fun k => v k + δv k) =
        Formalization.Analysis.shellEnergy v +
        2 * Formalization.Analysis.shellInner v δv +
        Formalization.Analysis.shellEnergy δv := by
    unfold Formalization.Analysis.shellEnergy Formalization.Analysis.shellInner
    simp only [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  linarith

/-- Quadratic homogeneity of `shellEnergy` under scalar multiplication. -/
lemma shellEnergy_scale {M : ℕ} (c : ℝ) (x : Fin M → ℝ) :
    Formalization.Analysis.shellEnergy (fun k => c * x k) =
      c ^ 2 * Formalization.Analysis.shellEnergy x := by
  unfold Formalization.Analysis.shellEnergy Formalization.Analysis.shellInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Single-step spherical triad update preserves exact shell energy $\|\tilde{v}\|_2^2 = \|v\|_2^2$. -/
lemma sphericalTriadStep_preserves_energy {M : ℕ} (γ : ℝ)
    (W_rec : Fin M → Fin M → Fin M → ℝ) (u v : Fin M → ℝ) :
    Formalization.Analysis.shellEnergy (sphericalTriadStep M γ W_rec u v) =
      Formalization.Analysis.shellEnergy v := by
  unfold sphericalTriadStep sphericalRetract
  dsimp only
  rw [shellEnergy_scale]
  by_cases hv0 : Formalization.Analysis.shellEnergy v = 0
  · simp [hv0]
  · have hv_nonneg : 0 ≤ Formalization.Analysis.shellEnergy v := shellEnergy_nonneg v
    have hv_pos : 0 < Formalization.Analysis.shellEnergy v :=
      lt_of_le_of_ne hv_nonneg (Ne.symm hv0)
    have h_orth : Formalization.Analysis.shellInner v (tangentTriadStep M γ W_rec u v) = 0 :=
      tangentTriadStep_orthogonal γ W_rec u v
    have h_pyth := shellEnergy_add_of_orthogonal v (tangentTriadStep M γ W_rec u v) h_orth
    have hδ_nonneg : 0 ≤ Formalization.Analysis.shellEnergy (tangentTriadStep M γ W_rec u v) :=
      shellEnergy_nonneg _
    have h_upd_pos :
        0 < Formalization.Analysis.shellEnergy (fun k => v k + tangentTriadStep M γ W_rec u v k) := by
      linarith
    have h_upd_nonneg := le_of_lt h_upd_pos
    have h_upd_ne := ne_of_gt h_upd_pos
    rw [div_pow, Real.sq_sqrt hv_nonneg, Real.sq_sqrt h_upd_nonneg]
    exact div_mul_cancel₀ (Formalization.Analysis.shellEnergy v) h_upd_ne

/-- **Theorem 6a (`darksnail_multistep_spherical_invariance`)**:
Across any $T$-step unrolled Slow-Fast spherical triad cascade $(v_L^{(t)})_{t=0}^T$,
the terminal retracted state preserves the exact initial squared Euclidean norm
$\|\tilde{v}_L^{(T)}\|_2^2 = \|v_L^{(0)}\|_2^2$, and at every intermediate step $t$,
the tangent triad perturbation $\delta v_L^{(t)}$ is strictly orthogonal to $v_L^{(t)}$:
$\langle v_L^{(t)}, \delta v_L^{(t)} \rangle = 0$. -/
theorem darksnail_multistep_spherical_invariance {M : ℕ}
    (γ : ℕ → ℝ) (W_rec : ℕ → Fin M → Fin M → Fin M → ℝ)
    (u : ℕ → Fin M → ℝ) (v₀ : Fin M → ℝ) (T : ℕ) :
    Formalization.Analysis.shellEnergy (multistepSphericalTriad M γ W_rec u v₀ T) =
      Formalization.Analysis.shellEnergy v₀ ∧
    (∀ t : ℕ,
      let v_t := multistepSphericalTriad M γ W_rec u v₀ t
      let δv_t := tangentTriadStep M (γ t) (W_rec t) (u t) v_t
      Formalization.Analysis.shellInner v_t δv_t = 0) := by
  refine ⟨?_, fun t => tangentTriadStep_orthogonal (γ t) (W_rec t) (u t) _⟩
  induction T with
  | zero => rfl
  | succ t ih =>
    simp only [multistepSphericalTriad]
    rw [sphericalTriadStep_preserves_energy, ih]

/-- At $W_{\mathrm{rec}} = 0$, the single-step spherical triad update reduces to the identity. -/
lemma sphericalTriadStep_zero {M : ℕ} (γ : ℝ) (u v : Fin M → ℝ) :
    sphericalTriadStep M γ 0 u v = v := by
  funext k
  have h_tan : (fun i => v i + tangentTriadStep M γ 0 u v i) = v := by
    funext i
    unfold tangentTriadStep triadOperator Formalization.Analysis.triadOperator
    simp
  unfold sphericalTriadStep sphericalRetract
  dsimp only
  rw [h_tan, congr_fun h_tan k]
  by_cases hv0 : Formalization.Analysis.shellEnergy v = 0
  · have hvk : v k = 0 := (shellEnergy_eq_zero_iff v).mp hv0 k
    simp [hv0, hvk]
  · have hv_nonneg : 0 ≤ Formalization.Analysis.shellEnergy v := shellEnergy_nonneg v
    have hv_pos : 0 < Formalization.Analysis.shellEnergy v :=
      lt_of_le_of_ne hv_nonneg (Ne.symm hv0)
    have h_sqrt_ne : Real.sqrt (Formalization.Analysis.shellEnergy v) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hv_pos)
    rw [div_self h_sqrt_ne, one_mul]

/-- Unmodified System 1 recurrent carry trajectory $(z_H^{(t)}, z_L^{(t)})_{t=0}^T$. -/
def system1CarryTrajectory {M : ℕ}
    (step_S1 : ℕ → (Fin M → ℝ) × (Fin M → ℝ) → (Fin M → ℝ) × (Fin M → ℝ))
    (z₀ : (Fin M → ℝ) × (Fin M → ℝ)) : ℕ → (Fin M → ℝ) × (Fin M → ℝ)
  | 0 => z₀
  | t + 1 => step_S1 t (system1CarryTrajectory step_S1 z₀ t)

/-- DarkSnail $T$-step unrolled Slow-Fast recurrent carry trajectory coupling
$z_H^{(t)} \to z_L^{(t)}$ via `sphericalTriadStep` and latent perturbation $(\delta z_H^{(t)}, \delta z_L^{(t)})$. -/
noncomputable def darksnailCarryTrajectory {M : ℕ}
    (step_S1 : ℕ → (Fin M → ℝ) × (Fin M → ℝ) → (Fin M → ℝ) × (Fin M → ℝ))
    (γ : ℕ → ℝ) (W_rec : ℕ → Fin M → Fin M → Fin M → ℝ)
    (δz_H δz_L : ℕ → Fin M → ℝ)
    (z₀ : (Fin M → ℝ) × (Fin M → ℝ)) : ℕ → (Fin M → ℝ) × (Fin M → ℝ)
  | 0 => z₀
  | t + 1 =>
      let z_t := darksnailCarryTrajectory step_S1 γ W_rec δz_H δz_L z₀ t
      let v_tilde := sphericalTriadStep M (γ t) (W_rec t) z_t.1 z_t.2
      step_S1 t (fun k => z_t.1 k + δz_H t k, fun k => v_tilde k + δz_L t k)

/-- **Theorem 6b (`darksnail_multistep_step0_homotopy`)**:
At the Step-0 initialization $W_{\mathrm{rec}} = 0$ and $\delta z = (0, 0)$, the $T$-step unrolled
spherical shell trajectory remains stationary at $v_0$, and the full $T$-step unrolled DarkSnail
recurrent carry trajectory reduces identically to the unmodified System 1 recurrent carry
trajectory $(z_H^{(t)}, z_L^{(t)})_{t=0}^T$ for all $T \in \mathbb{N}$. -/
theorem darksnail_multistep_step0_homotopy {M : ℕ}
    (step_S1 : ℕ → (Fin M → ℝ) × (Fin M → ℝ) → (Fin M → ℝ) × (Fin M → ℝ))
    (γ : ℕ → ℝ) (u : ℕ → Fin M → ℝ) (v₀ : Fin M → ℝ)
    (z₀ : (Fin M → ℝ) × (Fin M → ℝ)) (T : ℕ) :
    multistepSphericalTriad M γ 0 u v₀ T = v₀ ∧
    darksnailCarryTrajectory step_S1 γ 0 0 0 z₀ T =
      system1CarryTrajectory step_S1 z₀ T := by
  constructor
  · induction T with
    | zero => rfl
    | succ t ih =>
      simp only [multistepSphericalTriad, Pi.zero_apply]
      rw [ih, sphericalTriadStep_zero]
  · induction T with
    | zero => rfl
    | succ t ih =>
      simp only [darksnailCarryTrajectory, system1CarryTrajectory, Pi.zero_apply, add_zero]
      rw [ih, sphericalTriadStep_zero]

end Ultrametric.Analysis.OcclusionTriad
