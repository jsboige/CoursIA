import Mathlib

/-!
# Grokking — effective theory R02: parallelograms and conservation laws

Tranche **R02** of the "effective theory" arc (#16741, issue #16752):
*Liu et al., Towards Understanding Grokking — An Effective Theory of
Representation Learning* (arXiv:2205.10343, 2022; GDrive PDF sha8 `88CE88DB`).

Formalized content (short statements, constructive proofs — the cleanest
ground of the corpus according to the issue):

1. **Definition 1 (δ-parallelogram)** — `IsDeltaParallelogram`: a quadruple
   of embeddings `(i, j, m, n)` forms a parallelogram up to δ when
   `‖E i + E j − (E m + E n)‖ ≤ δ`. The paper's derivations take δ = 0
   (the equality version `parallelogram`).
2. **Proposition 1** — `prop1_zeroLoss`: at zero training loss with distinct
   labels, every parallelogram `(i,j,m,n)` satisfies `i + j = m + n`. Proof
   by contradiction exactly as in the paper:
   `Y_{i+j} = Dec(E i + E j) = Dec(E m + E n) = Y_{m+n}`, then injectivity
   of the labels concludes.
3. **Proposition 2** — `prop2_injectiveDecoder`: at zero loss with an
   injective decoder, two training samples with the same sum force the
   parallelogram `E i + E j = E m + E n` — the *formation* mechanism of
   parallelograms.
4. **Appendix F, conservation laws** — the computational core of Eq. (26)-(27)
   of the paper, for scalar embeddings `E : Fin p → ℝ` (the paper works at
   `din = 1` without loss of generality):
   - `loss0_grad_sum_zero`: the sum of the components of the gradient of `ℓ₀`
     is zero (each parallelogram constraint contributes
     `δ_ik + δ_jk − δ_mk − δ_nk`, of zero sum) — this is the identity that
     makes `C = Σ E k` constant along the flow (Eq. 27);
   - `loss0_grad_dot_self`: Euler's identity `Σ_k (∂ℓ₀/∂E_k) · E k = 2 ℓ₀`
     (a homogeneous quadratic function of degree 2) — this is what makes
     `Z₀ = Σ E k²` constant along the normalized flow (Eq. 26).

5. **Effective flow and conservation laws (full App F)** — the chain rule
   along an integral curve `γ` of the flow `dE/dt = −∂(ℓ₀/Z₀)/∂E`
   (Eq. 23, expanded form Eq. 25):
   - `flow_deriv_sumsq0_eq_zero` / `flow_sumsq0_constant`: **`Z₀` is
     conserved unconditionally** (Eq. 26) — the `∇ℓ₀` term closes by
     Euler's identity, the `∇Z₀` term by `Σ E k² = Z₀`;
   - `flow_deriv_sum_apply`: **audit of Eq. 27** — the complete chain rule
     gives `dC/dt = (2 ℓ₀/Z₀²) · C`: the term
     `(ℓ₀/Z₀²) · Σ ∂Z₀/∂E_k` omitted by the paper's printed derivation
     vanishes only in the zero-loss regime;
   - `flow_sum_constant_of_zero_loss`: in that regime (the post-grokking
     state, where the effective analysis lives), `C = Σ E k` is
     conserved exactly.

Dependencies: Mathlib only (`HasFDerivAt`, `ContinuousLinearMap.proj`,
`HasFDerivAt.sum`, `hasDerivAt_pow.comp_hasFDerivAt`). No coupling to the
sibling modules of the lake.
-/

namespace LearningTheory.EffectiveTheory_en

section Parallelograms

variable {p : ℕ} {V : Type*} [NormedAddCommGroup V] {Y : Type*}

/-- **Definition 1 (R02)**: the quadruple of pairs `(q, r)` (pairs
of training indices) forms a δ-parallelogram in the representation
`E` if `‖E q.1 + E q.2 − (E r.1 + E r.2)‖ ≤ δ`. -/
def IsDeltaParallelogram (E : Fin p → V) (δ : ℝ) (q r : Fin p × Fin p) : Prop :=
  ‖E q.1 + E q.2 - (E r.1 + E r.2)‖ ≤ δ

/-- The δ = 0 version used in the paper's derivations: the
exact parallelogram `E i + E j = E m + E n`. -/
theorem parallelogram_iff_eq (E : Fin p → V) (q r : Fin p × Fin p) :
    IsDeltaParallelogram E 0 q r ↔ E q.1 + E q.2 = E r.1 + E r.2 := by
  simp [IsDeltaParallelogram, sub_eq_zero]

/-- **Proposition 1 (R02)**: at zero training loss (every training pair
`(i, j)` satisfies `Dec (E i + E j) = Y (i + j)`) with distinct labels
(`Y` injective), every parallelogram `(q, r)` of the training set
satisfies `q.1 + q.2 = r.1 + r.2`.

This is the pedagogical contrapositive of grokking: a representation that
generalizes (many parallelograms) must respect the underlying arithmetic. -/
theorem prop1_zeroLoss (E : Fin p → V) (dec : V → Y) (label : ℕ → Y)
    (hLabel : Function.Injective label)
    (D : Finset (Fin p × Fin p))
    (hZeroLoss : ∀ q ∈ D, dec (E q.1 + E q.2) = label ((q.1 : ℕ) + q.2))
    {q r : Fin p × Fin p} (hq : q ∈ D) (hr : r ∈ D)
    (hPara : E q.1 + E q.2 = E r.1 + E r.2) :
    (q.1 : ℕ) + q.2 = (r.1 : ℕ) + r.2 := by
  refine hLabel ?_
  rw [← hZeroLoss q hq, ← hZeroLoss r hr, hPara]

/-- **Proposition 2 (R02)**: at zero loss with an injective decoder, two
training samples `(q, r)` with the same sum `q.1 + q.2 = r.1 + r.2`
force the exact parallelogram `E q.1 + E q.2 = E r.1 + E r.2`.

This is the *formation* mechanism: decoder injectivity prevents two
different representations from encoding the same label. -/
theorem prop2_injectiveDecoder (E : Fin p → V) (dec : V → Y) (label : ℕ → Y)
    (D : Finset (Fin p × Fin p))
    (hZeroLoss : ∀ q ∈ D, dec (E q.1 + E q.2) = label ((q.1 : ℕ) + q.2))
    (hDec : Function.Injective dec)
    {q r : Fin p × Fin p} (hq : q ∈ D) (hr : r ∈ D)
    (hSum : (q.1 : ℕ) + q.2 = (r.1 : ℕ) + r.2) :
    E q.1 + E q.2 = E r.1 + E r.2 := by
  refine hDec ?_
  rw [hZeroLoss q hq, hZeroLoss r hr, hSum]

end Parallelograms

section Conservation

variable {p : ℕ}

/-- Linear form of a parallelogram quadruple:
`linQ t E = E i + E j − (E m + E n)` for `t = ((i, j), (m, n))`. -/
private def linQ (t : (Fin p × Fin p) × (Fin p × Fin p)) :
    (Fin p → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj t.1.1 : (Fin p → ℝ) →L[ℝ] ℝ)
    + (ContinuousLinearMap.proj t.1.2 : (Fin p → ℝ) →L[ℝ] ℝ)
    - (ContinuousLinearMap.proj t.2.1 : (Fin p → ℝ) →L[ℝ] ℝ)
    - (ContinuousLinearMap.proj t.2.2 : (Fin p → ℝ) →L[ℝ] ℝ)

/-- Explicit evaluation of the linear form (avoids `map_sum`/`map_smul` on
the CLM, whose elaboration crosses a costly instance diamond). -/
private theorem linQ_apply (t : (Fin p × Fin p) × (Fin p × Fin p))
    (v : Fin p → ℝ) :
    linQ t v = v t.1.1 + v t.1.2 - (v t.2.1 + v t.2.2) := by
  simp only [linQ, add_apply, sub_apply, ContinuousLinearMap.proj_apply]
  ring

/-- Quadratic effective loss `ℓ₀` (Eq. 5 and 24 of the paper): the omitted
average of the squares of the parallelogram residuals over the set `P` of
admissible quadruples (positive multiplicative constants change neither the
sign of the gradient nor the conservation identities). -/
noncomputable def loss0 (P : Finset ((Fin p × Fin p) × (Fin p × Fin p)))
    (E : Fin p → ℝ) : ℝ :=
  ∑ t ∈ P, (linQ t E) ^ 2

/-- Energy norm `Z₀ = Σ_k (E k)²` (Eq. 5 and 24 of the paper): the second
conserved quantity, the one that forbids the representation from collapsing
to zero. -/
noncomputable def sumsq0 (E : Fin p → ℝ) : ℝ :=
  ∑ k, (E k) ^ 2

/-- Projection `E ↦ E k` wrapped in a def: fixes once and for all
the CLM instance profile (same pattern as `linQ`). -/
private def projCLM (k : Fin p) : (Fin p → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj k : (Fin p → ℝ) →L[ℝ] ℝ)

private theorem hasFDerivAt_loss0_term
    (t : (Fin p × Fin p) × (Fin p × Fin p)) (E : Fin p → ℝ) :
    HasFDerivAt (fun F : Fin p → ℝ => (linQ t F) ^ 2) ((2 * linQ t E) • linQ t) E := by
  simpa only [Function.comp_def, show (2 : ℕ) - 1 = 1 from rfl, pow_one,
    show ((2 : ℕ) : ℝ) = 2 from rfl] using
    HasDerivAt.comp_hasFDerivAt E (hasDerivAt_pow 2 (linQ t E)) (linQ t).hasFDerivAt

/-- Derivative of `ℓ₀`: `fderiv ℝ (loss0 P) E = Σ_t (2 · linQ t E) • linQ t`. -/
theorem hasFDerivAt_loss0 (P : Finset ((Fin p × Fin p) × (Fin p × Fin p)))
    (E : Fin p → ℝ) :
    HasFDerivAt (loss0 P) (∑ t ∈ P, (2 * linQ t E) • linQ t) E := by
  have h := HasFDerivAt.sum (u := P) (fun t _ => hasFDerivAt_loss0_term t E)
  have heq : (∑ t ∈ P, fun F : Fin p → ℝ => (linQ t F) ^ 2)
      = (fun F : Fin p → ℝ => ∑ t ∈ P, (linQ t F) ^ 2) :=
    funext fun F =>
      Finset.sum_apply F P fun t => (fun F : Fin p → ℝ => (linQ t F) ^ 2)
  rw [heq] at h
  exact h

private theorem hasFDerivAt_sumsq0_term (k : Fin p) (E : Fin p → ℝ) :
    HasFDerivAt (fun F : Fin p → ℝ => (projCLM k F) ^ 2)
      ((2 * projCLM k E) • projCLM k) E := by
  simpa only [Function.comp_def, show (2 : ℕ) - 1 = 1 from rfl, pow_one,
    show ((2 : ℕ) : ℝ) = 2 from rfl] using
    HasDerivAt.comp_hasFDerivAt E (hasDerivAt_pow 2 (projCLM k E))
      (projCLM k).hasFDerivAt

/-- Derivative of `Z₀`: `fderiv ℝ sumsq0 E = Σ_k (2 · E k) • proj k`. -/
theorem hasFDerivAt_sumsq0 (E : Fin p → ℝ) :
    HasFDerivAt sumsq0 (∑ k, (2 * E k) • projCLM k) E := by
  have h := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin p)))
    (fun k _ => hasFDerivAt_sumsq0_term k E)
  have heq : (∑ k : Fin p, fun F : Fin p → ℝ => (projCLM k F) ^ 2)
      = (fun F : Fin p → ℝ => ∑ k, (projCLM k F) ^ 2) :=
    funext fun F =>
      Finset.sum_apply F Finset.univ fun k => (fun F : Fin p → ℝ => (projCLM k F) ^ 2)
  rw [heq] at h
  exact h

/-- Reconstruction: the family of basis vectors `Pi.single k 1` decomposes
every `E` (identity used by Appendix F's Kronecker hunt). -/
private theorem sum_smul_piSingle_self (E : Fin p → ℝ) :
    ∑ k, E k • (Pi.single k (1 : ℝ) : Fin p → ℝ) = E := by
  funext i
  simp [Finset.sum_apply, Pi.single_apply, mul_ite]

/-- **Appendix F, Eq. (27) — identity 1**: the sum of the components of the
gradient of `ℓ₀` is zero:
`Σ_k (fderiv ℓ₀ E) (e_k) = 0`.

Each quadruple `t` contributes `δ_{t.1.1 k} + δ_{t.1.2 k} − δ_{t.2.1 k}
− δ_{t.2.2 k}` to component `k`, whose sum over `k` is exactly zero. This is
the algebraic core that makes `C = Σ_k E k` a conserved quantity along the
effective flow (Eq. 27: `dC/dt = −(1/Z₀) Σ_k ∂ℓ₀/∂E_k = 0`). -/
theorem loss0_grad_sum_zero (P : Finset ((Fin p × Fin p) × (Fin p × Fin p)))
    (E : Fin p → ℝ) :
    ∑ k, fderiv ℝ (loss0 P) E (Pi.single k (1 : ℝ)) = 0 := by
  rw [(hasFDerivAt_loss0 P E).fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  have hkey' : ∀ (i : Fin p), ∑ k, (Pi.single k (1 : ℝ) : Fin p → ℝ) i = 1 := by
    intro i
    simp [Pi.single_apply]
  have hsum : ∀ t : (Fin p × Fin p) × (Fin p × Fin p),
      ∑ k, linQ t (Pi.single k (1 : ℝ) : Fin p → ℝ) = 0 := by
    intro t
    simp only [linQ_apply]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [hkey']
    ring
  have hterm : ∀ t ∈ P,
      ∑ k, (2 * linQ t E) * linQ t (Pi.single k (1 : ℝ)) = 0 := by
    intro t _
    rw [← Finset.mul_sum, hsum t, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  exact Finset.sum_const_zero

/-- **Appendix F, Eq. (26) — identity 2 (Euler)**: the homogeneity identity
of the quadratic loss:
`Σ_k (fderiv ℓ₀ E) (e_k) * E k = 2 * ℓ₀ E`.

This is the algebraic core of the conservation of `Z₀ = Σ_k E k²` along the
normalized flow `dE/dt = −∂(ℓ₀/Z₀)/∂E` (Eq. 25-26 of the paper, which
substitutes exactly `Σ_k (∂ℓ₀/∂E_k) · E k = 2 ℓ₀` to conclude `dZ₀/dt = 0`). -/
theorem loss0_grad_dot_self (P : Finset ((Fin p × Fin p) × (Fin p × Fin p)))
    (E : Fin p → ℝ) :
    ∑ k, fderiv ℝ (loss0 P) E (Pi.single k (1 : ℝ)) * E k = 2 * loss0 P E := by
  rw [(hasFDerivAt_loss0 P E).fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  have hkey : ∀ (i : Fin p),
      ∑ k, (Pi.single k (1 : ℝ) : Fin p → ℝ) i * E k = E i := by
    intro i
    simp [Pi.single_apply]
  have hlin : ∀ t : (Fin p × Fin p) × (Fin p × Fin p),
      ∑ k, linQ t (Pi.single k (1 : ℝ) : Fin p → ℝ) * E k = linQ t E := by
    intro t
    have expand : ∀ k : Fin p,
        linQ t (Pi.single k (1 : ℝ) : Fin p → ℝ) * E k
          = (Pi.single k (1 : ℝ) : Fin p → ℝ) t.1.1 * E k
            + (Pi.single k (1 : ℝ) : Fin p → ℝ) t.1.2 * E k
            - ((Pi.single k (1 : ℝ) : Fin p → ℝ) t.2.1 * E k
              + (Pi.single k (1 : ℝ) : Fin p → ℝ) t.2.2 * E k) := by
      intro k
      rw [linQ_apply]
      ring
    rw [Finset.sum_congr rfl (fun k _ => expand k), Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [hkey, linQ_apply]
  have hterm : ∀ t ∈ P,
      ∑ k, 2 * (linQ t E * (linQ t (Pi.single k (1 : ℝ)) * E k))
        = 2 * (linQ t E) ^ 2 := by
    intro t _
    have h1 : ∑ k, linQ t E * (linQ t (Pi.single k (1 : ℝ)) * E k)
        = linQ t E * linQ t E := by
      calc ∑ k, linQ t E * (linQ t (Pi.single k (1 : ℝ)) * E k)
          = linQ t E * ∑ k, linQ t (Pi.single k (1 : ℝ)) * E k := by
            rw [Finset.mul_sum]
        _ = linQ t E * linQ t E := by rw [hlin t]
    calc ∑ k, 2 * (linQ t E * (linQ t (Pi.single k (1 : ℝ)) * E k))
        = 2 * ∑ k, linQ t E * (linQ t (Pi.single k (1 : ℝ)) * E k) := by
          rw [← Finset.mul_sum]
      _ = 2 * (linQ t E * linQ t E) := by rw [h1]
      _ = 2 * (linQ t E) ^ 2 := by ring
  rewrite [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  rfl

end Conservation

section Flow

variable {p : ℕ}

private theorem projCLM_apply (k : Fin p) (v : Fin p → ℝ) : projCLM k v = v k := by
  simp [projCLM]

/-- Component of a differentiable curve: if `γ` has velocity `v` at `t`,
each component `s ↦ γ s k` has velocity `v k`. -/
private theorem hasDerivAt_component (γ : ℝ → (Fin p → ℝ)) (k : Fin p) (t : ℝ)
    {v : Fin p → ℝ} (h : HasDerivAt γ v t) : HasDerivAt (fun s => γ s k) (v k) t := by
  have hc := ((projCLM k).hasFDerivAt.comp t h).hasDerivAt
  have h₁ : Filter.EventuallyEq (nhds t) (fun s => γ s k) (↑(projCLM k) ∘ γ) :=
    Filter.Eventually.of_forall fun s => (projCLM_apply k (γ s)).symm
  exact (hc.congr_of_eventuallyEq h₁).congr_deriv (by simp [projCLM_apply])

/-- Sum of the components: if `γ` has velocity `v` at `t`, the sum
`s ↦ Σ_k γ s k` has velocity `Σ_k v k`. -/
private theorem hasDerivAt_sumC {γ : ℝ → (Fin p → ℝ)} (t : ℝ) {v : Fin p → ℝ}
    (hv : HasDerivAt γ v t) : HasDerivAt (fun s => ∑ k, γ s k) (∑ k, v k) t := by
  have h := HasDerivAt.sum (u := (Finset.univ : Finset (Fin p)))
    fun k _ => hasDerivAt_component γ k t hv
  have heq : (∑ k : Fin p, fun s => γ s k) = (fun s => ∑ k, γ s k) :=
    funext fun s_ => Finset.sum_apply s_ Finset.univ fun k => fun s => γ s k
  rw [heq] at h
  exact h

/-- Energy: if `γ` has velocity `v` at `t`, the energy trajectory
`s ↦ Z₀ (γ s)` has velocity `Σ_k 2 E_k v_k`. -/
private theorem hasDerivAt_sumsq0_comp {γ : ℝ → (Fin p → ℝ)} (t : ℝ) {v : Fin p → ℝ}
    (hv : HasDerivAt γ v t) :
    HasDerivAt (fun s => sumsq0 (γ s)) (∑ k, 2 * (γ t k) * v k) t := by
  have hfun : (fun s => sumsq0 (γ s)) = fun s => ∑ k, (γ s k) ^ 2 := rfl
  rw [hfun]
  have h := HasDerivAt.sum (u := (Finset.univ : Finset (Fin p))) fun k _ =>
    (hasDerivAt_pow 2 (γ t k)).comp t (hasDerivAt_component γ k t hv)
  have heq : (∑ k : Fin p, (fun x => x ^ 2) ∘ fun s => γ s k)
      = (fun s => ∑ k, (γ s k) ^ 2) :=
    funext fun s_ => Finset.sum_apply s_ Finset.univ
      fun k => (fun x => x ^ 2) ∘ fun s => γ s k
  rw [heq] at h
  refine h.congr_deriv ?_
  simp [pow_one]

/-- **Gradient of `ℓ₀`** (Eq. 25 of the paper): component `k` of the gradient
vector is `∂ℓ₀/∂E_k := fderiv ℝ (loss0 P) E (e_k)`. -/
noncomputable def gradLoss0 (P : Finset ((Fin p × Fin p) × (Fin p × Fin p)))
    (E : Fin p → ℝ) : Fin p → ℝ :=
  fun k => fderiv ℝ (loss0 P) E (Pi.single k (1 : ℝ))

/-- **Gradient of `Z₀`**: component `k` = `∂Z₀/∂E_k`. -/
noncomputable def gradSumSq0 (E : Fin p → ℝ) : Fin p → ℝ :=
  fun k => fderiv ℝ sumsq0 E (Pi.single k (1 : ℝ))

/-- The gradient of `Z₀ = Σ E k²` is `2 • E`. -/
theorem gradSumSq0_apply (E : Fin p → ℝ) (k : Fin p) : gradSumSq0 E k = 2 * E k := by
  rw [gradSumSq0, (hasFDerivAt_sumsq0 E).fderiv]
  have h1 : ∀ x : Fin p, (2 * E x) * (projCLM x) (Pi.single k (1 : ℝ))
      = (if x = k then 2 * E x else 0) := by
    intro x
    rw [projCLM_apply, Pi.single_apply]
    rcases eq_or_ne x k with rfl | hne
    · simp
    · simp [hne]
  simp only [sum_apply, smul_apply, smul_eq_mul, h1]
  simp

/-- **Effective flow (Eq. 23, expanded form Eq. 25)**: a curve of
embeddings `γ` follows gradient descent of `ℓ_eff = ℓ₀/Z₀` when its
velocity at `t` equals `−(1/Z₀) • ∇ℓ₀ + (ℓ₀/Z₀²) • ∇Z₀`, gradients evaluated
at `γ t` (quotient rule applied to `∂(ℓ₀/Z₀)/∂E`). -/
def IsEffectiveFlow (P : Finset ((Fin p × Fin p) × (Fin p × Fin p)))
    (γ : ℝ → (Fin p → ℝ)) : Prop :=
  ∀ t, HasDerivAt γ
    (-(sumsq0 (γ t))⁻¹ • gradLoss0 P (γ t)
      + (loss0 P (γ t) / (sumsq0 (γ t)) ^ 2) • gradSumSq0 (γ t)) t

/-- Component of the flow velocity (Eq. 25):
`dE_k/dt = −(1/Z₀) ∂ℓ₀/∂E_k + (ℓ₀/Z₀²) · 2 E_k`. -/
theorem isEffectiveFlow_vel_apply (P : Finset ((Fin p × Fin p) × (Fin p × Fin p)))
    {γ : ℝ → (Fin p → ℝ)} (hγ : IsEffectiveFlow P γ) (t : ℝ) (k : Fin p) :
    deriv γ t k = -(sumsq0 (γ t))⁻¹ * gradLoss0 P (γ t) k
      + (loss0 P (γ t) / (sumsq0 (γ t)) ^ 2) * (2 * γ t k) := by
  rw [(hγ t).deriv]
  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, gradSumSq0_apply]

private theorem vel_apply (P : Finset ((Fin p × Fin p) × (Fin p × Fin p)))
    {γ : ℝ → (Fin p → ℝ)} (hγ : IsEffectiveFlow P γ) (t : ℝ) (k : Fin p) :
    (-(sumsq0 (γ t))⁻¹ • gradLoss0 P (γ t)
      + (loss0 P (γ t) / (sumsq0 (γ t)) ^ 2) • gradSumSq0 (γ t)) k
      = -(sumsq0 (γ t))⁻¹ * gradLoss0 P (γ t) k
        + (loss0 P (γ t) / (sumsq0 (γ t)) ^ 2) * (2 * γ t k) := by
  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, gradSumSq0_apply]

/-- **Eq. 26 — `Z₀` is conserved along the effective flow**:
`d/dt (Σ_k E_k(t)²) = 0`, unconditionally. The chain rule gives
`dZ₀/dt = Σ_k 2 E_k · Ė_k`; substituting the velocity (Eq. 25) brings out
exactly the two gradient identities: the `∇ℓ₀` term closes by Euler's
identity (`loss0_grad_dot_self`), the `∇Z₀` term by `Σ E k² = Z₀`. This is
the conservation that forbids the representation from collapsing to zero. -/
theorem flow_deriv_sumsq0_eq_zero (P : Finset ((Fin p × Fin p) × (Fin p × Fin p)))
    {γ : ℝ → (Fin p → ℝ)} (hγ : IsEffectiveFlow P γ) (t : ℝ) :
    deriv (fun s => sumsq0 (γ s)) t = 0 := by
  have hv := hγ t
  rw [(hasDerivAt_sumsq0_comp t hv).deriv]
  simp only [vel_apply P hγ t]
  have hEuler : ∑ k, 2 * (γ t k) * gradLoss0 P (γ t) k = 2 * (2 * loss0 P (γ t)) := by
    have h2 : ∑ k, (γ t k) * gradLoss0 P (γ t) k = 2 * loss0 P (γ t) := by
      rw [Finset.sum_congr rfl fun k _ => mul_comm (γ t k) (gradLoss0 P (γ t) k)]
      simpa only [gradLoss0] using loss0_grad_dot_self P (γ t)
    have h4 : ∑ k, 2 * (γ t k) * gradLoss0 P (γ t) k
        = 2 * ∑ k, (γ t k) * gradLoss0 P (γ t) k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h4, h2]
  have hZZ : ∑ k, 2 * (γ t k) * (2 * γ t k) = 2 * (2 * sumsq0 (γ t)) := by
    have h3 : ∑ k, 2 * (γ t k) * (2 * γ t k) = ∑ k, 2 * (2 * ((γ t k) * (γ t k))) :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [h3, ← Finset.mul_sum, ← Finset.mul_sum]
    have hsq : ∑ i, γ t i * γ t i = sumsq0 (γ t) := by
      simp [sumsq0, pow_two, sq]
    rw [hsq]
  have hsplit : ∑ k, 2 * (γ t k) * (-(sumsq0 (γ t))⁻¹ * gradLoss0 P (γ t) k
        + (loss0 P (γ t) / (sumsq0 (γ t)) ^ 2) * (2 * γ t k))
      = -(sumsq0 (γ t))⁻¹ * (2 * (2 * loss0 P (γ t)))
        + (loss0 P (γ t) / (sumsq0 (γ t)) ^ 2) * (2 * (2 * sumsq0 (γ t))) := by
    have h1 : ∑ k, 2 * (γ t k) * (-(sumsq0 (γ t))⁻¹ * gradLoss0 P (γ t) k
          + (loss0 P (γ t) / (sumsq0 (γ t)) ^ 2) * (2 * γ t k))
        = ∑ k, (-(sumsq0 (γ t))⁻¹ * (2 * (γ t k) * gradLoss0 P (γ t) k))
          + ∑ k, ((loss0 P (γ t) / (sumsq0 (γ t)) ^ 2) * (2 * (γ t k) * (2 * γ t k))) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h1, ← Finset.mul_sum, ← Finset.mul_sum, hEuler, hZZ]
  rw [hsplit]
  rcases eq_or_ne (sumsq0 (γ t)) 0 with h0 | h0
  · simp [h0]
  · have hZ2 : (sumsq0 (γ t)) ^ 2 ≠ 0 := pow_ne_zero 2 h0
    field_simp
    ring

/-- **Eq. 27 audited — the sum `C = Σ E_k` is conserved only in the
zero-loss regime.** The chain rule applied to the full velocity (Eq. 25)
gives `dC/dt = −(1/Z₀) Σ_k ∂ℓ₀/∂E_k + (ℓ₀/Z₀²) · 2 C`. The derivation
printed as Eq. 27 of the paper keeps only the first term and concludes
`dC/dt = 0` via `Σ_k ∂ℓ₀/∂E_k = 0` — the second term
`(2 ℓ₀/Z₀²) · C` vanishes only if `ℓ₀ = 0` along the trajectory
(the post-grokking state, where the effective analysis lives) or if `C = 0`
(translated frame). The theorem below formalizes the exact dynamics;
unconditional conservation of `C` is NOT a theorem of the flow. -/
theorem flow_deriv_sum_apply (P : Finset ((Fin p × Fin p) × (Fin p × Fin p)))
    {γ : ℝ → (Fin p → ℝ)} (hγ : IsEffectiveFlow P γ) (t : ℝ) :
    deriv (fun s => ∑ k, γ s k) t
      = (2 * loss0 P (γ t) / (sumsq0 (γ t)) ^ 2) * ∑ k, γ t k := by
  have hv := hγ t
  rw [(hasDerivAt_sumC t hv).deriv]
  simp only [vel_apply P hγ t]
  have hdist : ∑ k, (-(sumsq0 (γ t))⁻¹ * gradLoss0 P (γ t) k
        + (loss0 P (γ t) / (sumsq0 (γ t)) ^ 2) * (2 * γ t k))
      = ∑ k, (-(sumsq0 (γ t))⁻¹ * gradLoss0 P (γ t) k)
        + ∑ k, ((loss0 P (γ t) / (sumsq0 (γ t)) ^ 2) * (2 * γ t k)) := by
    rw [Finset.sum_add_distrib]
  have hsum0 : ∑ k, gradLoss0 P (γ t) k = 0 := by
    simpa only [gradLoss0] using loss0_grad_sum_zero P (γ t)
  have hsum2 : ∑ k, (2 * γ t k) = 2 * ∑ k, γ t k := by
    rw [Finset.mul_sum]
  rw [hdist, ← Finset.mul_sum, ← Finset.mul_sum, hsum0, hsum2]
  ring

private theorem constant_of_deriv_zero {f : ℝ → ℝ} (hd : Differentiable ℝ f)
    (hf : ∀ t, deriv f t = 0) (s t : ℝ) : f s = f t := by
  have hkey : ∀ a b : ℝ, a < b → ∀ x ∈ Set.Icc a b, f x = f a := by
    intro a b hab x hx
    refine constant_of_derivWithin_zero (f := f) (a := a) (b := b)
      hd.differentiableOn ?_ x hx
    intro y hy
    have hmem : y ∈ Set.Icc a b := ⟨hy.1, hy.2.le⟩
    have hyd : UniqueDiffWithinAt ℝ (Set.Icc a b) y :=
      (uniqueDiffOn_Icc hab).uniqueDiffWithinAt hmem
    rw [(hd y).derivWithin hyd]
    exact hf y
  rcases le_total s t with hle | hle
  · rcases eq_or_lt_of_le hle with rfl | hlt
    · rfl
    · exact (hkey s t hlt t ⟨hle, le_rfl⟩).symm
  · rcases eq_or_lt_of_le hle with rfl | hlt
    · rfl
    · exact hkey t s hlt s ⟨hle, le_rfl⟩

/-- **Corollary of Eq. 26**: `Z₀` is constant along every integral curve
of the effective flow — the energy norm of the representation never
decreases, which forbids the collapse to zero. -/
theorem flow_sumsq0_constant (P : Finset ((Fin p × Fin p) × (Fin p × Fin p)))
    {γ : ℝ → (Fin p → ℝ)} (hγ : IsEffectiveFlow P γ) (s t : ℝ) :
    sumsq0 (γ s) = sumsq0 (γ t) :=
  constant_of_deriv_zero (fun u => (hasDerivAt_sumsq0_comp u (hγ u)).differentiableAt)
    (flow_deriv_sumsq0_eq_zero P hγ) s t

/-- **Corollary of Eq. 27 (zero-loss regime)**: if the trajectory stays
on the variety `ℓ₀ = 0` (the post-grokking state, the paper's effective
context), then `C = Σ E_k` is conserved there exactly. -/
theorem flow_sum_constant_of_zero_loss (P : Finset ((Fin p × Fin p) × (Fin p × Fin p)))
    {γ : ℝ → (Fin p → ℝ)} (hγ : IsEffectiveFlow P γ)
    (h0 : ∀ s, loss0 P (γ s) = 0) (s t : ℝ) :
    ∑ k, γ s k = ∑ k, γ t k := by
  refine constant_of_deriv_zero (fun u => (hasDerivAt_sumC u (hγ u)).differentiableAt)
    (fun u => ?_) s t
  rw [flow_deriv_sum_apply P hγ u, h0 u]
  simp

end Flow

end LearningTheory.EffectiveTheory
