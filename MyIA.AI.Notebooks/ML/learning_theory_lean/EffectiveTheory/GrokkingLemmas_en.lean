import Mathlib
import EffectiveTheory.Grokking

/-!
# GrokkingLemmas — own contribution of the R02 grain (rescoping #16752)

English mirror of `GrokkingLemmas.lean` (FR-first canonical), EPIC #4980
(i18n Lean). Convention ratified 2026-07-04 (issue #4980): namespace
`LearningTheory.EffectiveTheory_en`. `EffectiveTheory.Grokking` has no
`_en` twin on `main` (deferred to #17481), so this mirror imports the FR
module and opens its namespace — statements and proofs below are
byte-identical to the FR canonical file.

Sibling module of `EffectiveTheory.Grokking` (ai-01 arbitration
c.5790650195, 2026-09-23): `Grokking.lean` on `main` already carries the
parallelograms (Def. 1, Props 1-2), the Appendix F identities, `Z₀`
conservation and the exact `C` dynamics along the effective flow
(`flow_deriv_sum_apply`). This module adds ONLY the own delta of the
original grain (branch `feature/16752-grokking-lean`), ported from the
`EuclideanSpace ℝ ι` frame to the `Fin p → ℝ` frame of `Grokking.lean` —
the transfer is a direct rewrite (finite sums vs pairing with the vector
`1`), no transfer lemma needed.

Contents:

1. **`C_conserved_l0`** — the sum `C = Σ E k` is conserved along the flow
   of `ℓ₀` (unnormalized): translation is a symmetry of `ℓ₀`, so
   `Σ_k ∂ℓ₀/∂E_k = 0` (`loss0_grad_sum_zero`, Appendix F identity 1)
   kills the constant direction. Distinct from the corollary
   `flow_sum_constant_of_zero_loss` (*effective* flow, zero-loss regime).
2. **`meanZero_invariant`** — the centered hyperplane `C = 0` is invariant
   along the effective flow: the derivative of `C ∘ γ` is proportional to
   `C` (`dC/dt = κ · C`, `flow_deriv_sum_apply`), and the integrating
   factor `exp(−∫κ)` shows a solution starting at zero stays there. This
   is the exact form of the paper's "conservation of C" in the normalized
   regime (centered embeddings).
3. **Generic differential-calculus lemmas** (frame: arbitrary normed or
   inner-product space, no dependence on `Fin p → ℝ`): `hasDerivAt_line`
   (derivative of the line `t ↦ a + t • b`), `euler_zero_homogeneous`
   (Euler for 0-homogeneous functions), `fderiv_of_translateInvariant`
   (translation invariance ⟹ killed direction), `eq_of_hasDerivAt_zero`
   (zero derivative ⟹ constant) and `Z0_conserved` (norm conservation
   along the `−∇f` flow of a 0-homogeneous function).

Sources: *Liu, Michaud, Tegmark — Towards Understanding Grokking: An
Effective Theory of Representation Learning* (arXiv:2205.10343, 2022;
GDrive PDF sha8 `88CE88DB`), Appendix F and section 4.2.
-/

namespace LearningTheory.EffectiveTheory_en

open Finset

open scoped InnerProductSpace Topology

open LearningTheory.EffectiveTheory

/-! ### Generic differential-calculus lemmas -/

section GeneralCalculus

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The line `t ↦ a + t • b` is differentiable with velocity `b`. -/
theorem hasDerivAt_line (a b : X) : HasDerivAt (fun t : ℝ => a + t • b) b (0 : ℝ) := by
  simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
    (ContinuousLinearMap.hasDerivAt
      (ContinuousLinearMap.toSpanSingleton ℝ b) (x := (0 : ℝ))).const_add a

/-- **Euler for 0-homogeneous functions.** If `f` is differentiable at `a`
and 0-homogeneous along the radial line (`f (c • a) = f a` for all `c ≠ 0`),
then the radial directional derivative vanishes: `f' a a = 0`. -/
theorem euler_zero_homogeneous {f : X → ℝ} {a : X}
    (ha : HasFDerivAt f (fderiv ℝ f a) a)
    (hhom : ∀ c : ℝ, c ≠ 0 → f (c • a) = f a) : fderiv ℝ f a a = 0 := by
  have ha0 : HasFDerivAt f (fderiv ℝ f a) ((fun t : ℝ => a + t • a) 0) := by simpa using ha
  have hcomp : HasDerivAt (fun t : ℝ => f (a + t • a)) (fderiv ℝ f a a) (0 : ℝ) :=
    ha0.comp_hasDerivAt (0 : ℝ) (hasDerivAt_line a a)
  have heq : (fun t : ℝ => f (a + t • a)) =ᶠ[𝓝 (0 : ℝ)] fun _ : ℝ => f a := by
    filter_upwards [(isOpen_Ioo (a := (-1 : ℝ)) (b := (1 : ℝ))).mem_nhds (by norm_num)]
      with t ht
    have h1t : (1 + t) • a = a + t • a := by rw [add_smul, one_smul]
    have hne : (1 + t) ≠ 0 := by linarith [ht.1, ht.2]
    rw [← h1t]
    exact hhom (1 + t) hne
  have hconst : HasDerivAt (fun _ : ℝ => f a) (0 : ℝ) (0 : ℝ) := hasDerivAt_const _ _
  have hcomp' : HasDerivAt (fun _ : ℝ => f a) (fderiv ℝ f a a) (0 : ℝ) :=
    HasDerivAt.congr_of_eventuallyEq hcomp heq.symm
  exact hcomp'.unique hconst

/-- **Translation invariance ⟹ killed direction.** If `f` is differentiable
at `x` and invariant under translation in direction `b` (`f (y + c • b) = f y`
for all `c`), then `f' x b = 0`. -/
theorem fderiv_of_translateInvariant {f : X → ℝ} {x b : X}
    (hx : HasFDerivAt f (fderiv ℝ f x) x)
    (hinv : ∀ (c : ℝ) (y : X), f (y + c • b) = f y) : fderiv ℝ f x b = 0 := by
  have hx0 : HasFDerivAt f (fderiv ℝ f x) ((fun t : ℝ => x + t • b) 0) := by simpa using hx
  have hcomp : HasDerivAt (fun t : ℝ => f (x + t • b)) (fderiv ℝ f x b) (0 : ℝ) :=
    hx0.comp_hasDerivAt (0 : ℝ) (hasDerivAt_line x b)
  have hfun : (fun t : ℝ => f (x + t • b)) = fun _ : ℝ => f x := funext fun t => hinv t x
  rw [hfun] at hcomp
  have hconst : HasDerivAt (fun _ : ℝ => f x) (0 : ℝ) (0 : ℝ) := hasDerivAt_const _ _
  exact hcomp.unique hconst

/-- **Zero derivative everywhere ⟹ constant.** A real curve whose derivative
vanishes at every point is constant. -/
theorem eq_of_hasDerivAt_zero {g : ℝ → ℝ} (h : ∀ t, HasDerivAt g 0 t) (s t : ℝ) :
    g s = g t :=
  is_const_of_deriv_eq_zero (fun u => (h u).differentiableAt)
    (fun u => (h u).deriv) s t

end GeneralCalculus

/-! ### Generic norm conservation (flow of a 0-homogeneous function) -/

section NormConservation

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- **Norm conservation along the `−∇f` flow of a 0-homogeneous function.**
If `γ` follows `−∇f` (`⟪γ', u⟫ = −f' (γ) u`) and `f (c • x) = f x` for
`c ≠ 0`, then `‖γ‖` is constant: the velocity is orthogonal to the radius
(Euler). Generic inner-product-space version of `flow_sumsq0_constant`
(`Grokking.lean`, Eq. 26), for an arbitrary `f`. -/
theorem Z0_conserved {f : X → ℝ} {γ : ℝ → X} {γ' : ℝ → X}
    (hγ : ∀ t, HasDerivAt γ (γ' t) t)
    (hflow : ∀ t u, ⟪γ' t, u⟫_ℝ = -fderiv ℝ f (γ t) u)
    (hfdiff : ∀ t, HasFDerivAt f (fderiv ℝ f (γ t)) (γ t))
    (hhom : ∀ (c : ℝ) (x : X), c ≠ 0 → f (c • x) = f x)
    (s t : ℝ) : ‖γ s‖ ^ 2 = ‖γ t‖ ^ 2 := by
  have hrad' : ∀ r, ⟪γ' r, γ r⟫_ℝ = 0 := by
    intro r
    have h := (hflow r (γ r)).symm
    rw [euler_zero_homogeneous (hfdiff r) (fun c hc => hhom c (γ r) hc), neg_zero] at h
    exact h.symm
  have key : ∀ r, HasDerivAt (fun u => ‖γ u‖ ^ 2) 0 r := by
    intro r
    have h := HasDerivAt.inner ℝ (hγ r) (hγ r)
    rw [real_inner_comm (γ' r) (γ r), hrad' r, add_zero] at h
    have hfun : (fun u => ⟪γ u, γ u⟫_ℝ) = fun u => ‖γ u‖ ^ 2 :=
      funext fun u => real_inner_self_eq_norm_sq (γ u)
    rwa [hfun] at h
  exact eq_of_hasDerivAt_zero key s t

end NormConservation

/-! ### C along the ℓ₀ flow: unconditional conservation -/

section L0Flow

variable {p : ℕ}

/-- Component of a differentiable curve valued in `Fin p → ℝ`: if `γ` has
velocity `v` at `t`, each component `s ↦ γ s k` has velocity `v k`. -/
private theorem hasDerivAt_component' (γ : ℝ → (Fin p → ℝ)) (k : Fin p) (t : ℝ)
    {v : Fin p → ℝ} (h : HasDerivAt γ v t) : HasDerivAt (fun s => γ s k) (v k) t := by
  have hc := ((ContinuousLinearMap.proj k : (Fin p → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp t h).hasDerivAt
  have h₁ : Filter.EventuallyEq (nhds t) (fun s => γ s k)
      (↑(ContinuousLinearMap.proj k : (Fin p → ℝ) →L[ℝ] ℝ) ∘ γ) :=
    Filter.Eventually.of_forall fun s => rfl
  exact (hc.congr_of_eventuallyEq h₁).congr_deriv (by simp)

/-- Sum of components: if `γ` has velocity `v` at `t`, the sum
`s ↦ Σ_k γ s k` has velocity `Σ_k v k`. -/
private theorem hasDerivAt_sumC' {γ : ℝ → (Fin p → ℝ)} (t : ℝ) {v : Fin p → ℝ}
    (hv : HasDerivAt γ v t) : HasDerivAt (fun s => ∑ k, γ s k) (∑ k, v k) t := by
  have h := HasDerivAt.sum (u := (Finset.univ : Finset (Fin p)))
    fun k _ => hasDerivAt_component' γ k t hv
  have heq : (∑ k : Fin p, fun s => γ s k) = (fun s => ∑ k, γ s k) :=
    funext fun s_ => Finset.sum_apply s_ Finset.univ fun k => fun s => γ s k
  rw [heq] at h
  exact h

/-- **Flow of `ℓ₀` (unnormalized)**: a curve `γ` follows gradient descent
of `ℓ₀` when its velocity at `t` is `−∇ℓ₀ (γ t)` (compare `IsEffectiveFlow`,
the normalized `ℓ₀/Z₀` flow of `Grokking.lean`). -/
def IsL0Flow (P : Finset ((Fin p × Fin p) × (Fin p × Fin p)))
    (γ : ℝ → (Fin p → ℝ)) : Prop :=
  ∀ t, HasDerivAt γ (-(gradLoss0 P (γ t))) t

/-- **`C = Σ E k` is conserved along the `ℓ₀` flow**, unconditionally.
The translation `E ↦ E + c • 1` is a symmetry of `ℓ₀` (each parallelogram
constraint contributes `δ_ik + δ_jk − δ_mk − δ_nk`, summing to zero — this
is Appendix F identity 1, `loss0_grad_sum_zero`), so the differential kills
the constant direction and `dC/dt = −Σ_k ∂ℓ₀/∂E_k = 0`.

Distinct from the corollary `flow_sum_constant_of_zero_loss` of
`Grokking.lean`: that one concerns the *effective* (normalized) flow and
requires the zero-loss regime; here the `ℓ₀` flow alone conserves `C`
with no assumption. -/
theorem C_conserved_l0 (P : Finset ((Fin p × Fin p) × (Fin p × Fin p)))
    {γ : ℝ → (Fin p → ℝ)} (hγ : IsL0Flow P γ) (s t : ℝ) :
    ∑ k, γ s k = ∑ k, γ t k := by
  have hsum0 : ∀ u, ∑ k, gradLoss0 P (γ u) k = 0 := by
    intro u
    simpa only [gradLoss0] using loss0_grad_sum_zero P (γ u)
  have key : ∀ u, HasDerivAt (fun r => ∑ k, γ r k) 0 u := by
    intro u
    have h := hasDerivAt_sumC' u (hγ u)
    have hzero : (∑ k, (-(gradLoss0 P (γ u))) k) = 0 := by
      simp [Pi.neg_apply, hsum0 u]
    rwa [hzero] at h
  exact eq_of_hasDerivAt_zero key s t

end L0Flow

/-! ### Invariance of the centered hyperplane along the effective flow -/

section MeanZero

variable {p : ℕ}

/-- **The centered hyperplane is invariant.** If the representation is
centered at time `0` (`C = 0`) and follows the effective flow, it stays
centered for all time. This is the exact form of the paper's "conservation
of C": true as stated for the `ℓ₀` flow alone (`C_conserved_l0`), and for
the effective flow in the normalized regime (centered embeddings) where
`C` vanishes by construction. The derivative of `C ∘ γ` being proportional
to `C` itself (`dC/dt = κ · C`, `flow_deriv_sum_apply`), the integrating
factor `exp(−∫κ)` shows the solution starting at zero stays there. -/
theorem meanZero_invariant (P : Finset ((Fin p × Fin p) × (Fin p × Fin p)))
    {γ : ℝ → (Fin p → ℝ)} (hγ : IsEffectiveFlow P γ)
    (hZ0 : ∀ t, sumsq0 (γ t) ≠ 0)
    (hκcont : Continuous (fun s => 2 * loss0 P (γ s) / (sumsq0 (γ s)) ^ 2))
    (h0 : ∑ k, γ 0 k = 0) (t : ℝ) : ∑ k, γ t k = 0 := by
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ → ℝ, ∀ s, κ s = 2 * loss0 P (γ s) / (sumsq0 (γ s)) ^ 2 :=
    ⟨_, fun _ => rfl⟩
  have hκc : Continuous κ := by
    rw [show κ = fun s => 2 * loss0 P (γ s) / (sumsq0 (γ s)) ^ 2 from funext hκdef]
    exact hκcont
  have hη : ∀ s, HasDerivAt (fun r => ∑ k, γ r k) (κ s * ∑ k, γ s k) s := by
    intro s
    have hvel := hasDerivAt_sumC' s (hγ s)
    rw [hκdef s]
    refine hvel.congr_deriv ?_
    rw [← hvel.deriv]
    exact flow_deriv_sum_apply P hγ s
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ → ℝ, ∀ u, K u = ∫ r in 0..u, κ r := ⟨_, fun _ => rfl⟩
  have hKd : ∀ u, HasDerivAt K (κ u) u := by
    intro u
    rw [show K = fun u => ∫ r in 0..u, κ r from funext hKdef]
    exact intervalIntegral.integral_hasDerivAt_right (hκc.intervalIntegrable (0 : ℝ) u)
      (hκc.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 u)) hκc.continuousAt
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ → ℝ, ∀ s, F s = (∑ k, γ s k) * Real.exp (- K s) :=
    ⟨_, fun _ => rfl⟩
  have hFd : ∀ s, HasDerivAt F 0 s := by
    intro s
    have h := HasDerivAt.mul (hη s) ((hKd s).neg.exp)
    simp only [Pi.neg_apply] at h
    have hval : (κ s * ∑ k, γ s k) * Real.exp (- K s)
        + (∑ k, γ s k) * (Real.exp (- K s) * -(κ s)) = 0 := by ring
    rw [hval] at h
    rw [show F = fun r => (∑ k, γ r k) * Real.exp (- K r) from funext hFdef]
    exact h
  have hF0 : F 0 = 0 := by
    have hK0 : K 0 = 0 := by rw [hKdef 0, intervalIntegral.integral_same]
    rw [hFdef 0, hK0, h0, zero_mul]
  have hFt : F t = 0 := by
    rw [eq_of_hasDerivAt_zero hFd t 0, hF0]
  have hlast : (∑ k, γ t k) * Real.exp (- K t) = 0 := by
    rw [← hFdef t]
    exact hFt
  rcases mul_eq_zero.mp hlast with h | h
  · exact h
  · exact absurd h (Real.exp_ne_zero _)

end MeanZero

end LearningTheory.EffectiveTheory_en
