/-
Grokking — conservation laws of the effective theory (Appendix F of R02).

Formalizes Appendix F of "Towards Understanding Grokking" (Liu, Michaud, Tegmark;
arXiv:2205.10343), issue #16752. The dynamics of the embeddings is modeled by a
gradient flow for the effective loss

  ℓ_eff = ℓ₀ / Z₀,  ℓ₀ = ∑_{(i,j,m,n) ∈ Q} ‖E_i + E_j − E_m − E_n‖²,  Z₀ = ‖E‖²,

where `Q` is a finite set of index quadruples (typically the permissible
parallelograms `P₀` of module `Grokking_en.Effective`). The paper announces two
conserved quantities: the center of mass `C = ∑_k E_k` and the energy `Z₀ = ‖E‖²`.

Results:

* `Grokking_en.loss0_translate` / `Grokking_en.loss0_smul` — ℓ₀ is invariant under
  translation and 2-homogeneous. These are the two identities
  `∑_k ∂ℓ₀/∂E_k = 0` and `∑_k ∂ℓ₀/∂E_k · E_k = 2ℓ₀` of Appendix F, proved
  without any gradient computation.
* `Grokking_en.euler_zero_homogeneous`, `Grokking_en.fderiv_of_translateInvariant`,
  `Grokking_en.eq_of_hasDerivAt_zero` — three general differential-calculus lemmas.
* `Grokking_en.Z0_conserved` — **Z₀ is conserved** along the flow of ℓ_eff
  (scaling is a symmetry of ℓ_eff, and Euler kills the radial direction). This is
  what forbids the collapse of the representation onto zero.
* `Grokking_en.C_conserved_l0` — **C is conserved** along the flow of ℓ₀ alone
  (translation is a symmetry of ℓ₀).
* `Grokking_en.deriv_C_along_eff` — **the honest complement**: along the flow of
  ℓ_eff = ℓ₀/Z₀, the derivative of C is exactly `(2 ℓ₀ / Z₀²) • C`. The proof of
  Appendix F writes `dC/dt = −(1/Z₀) ∑_k ∂ℓ₀/∂E_k`, omitting the `∂Z₀` term of
  the quotient rule; the full computation reveals this residual term,
  proportional to C itself.
* `Grokking_en.meanZero_invariant` — corollary: the hyperplane `C = 0` (centered
  representation) is invariant along the flow of ℓ_eff. This is the exact form of
  the paper's "conservation of C": it holds in the normalized setting of the main
  text (Eqs. 4-5: centered-rescaled embeddings `Ẽ = (E − μ)/σ`), where C ≡ 0 by
  construction.

Working space: scalar embeddings `x : EuclideanSpace ℝ ι` (dimension 1, the
paper's toy setting), `ι` an arbitrary finite type. Then Z₀ = ‖x‖² and C = ∑ k, x k.

A gradient flow for `f : X → ℝ` (X a real inner-product space) is a
differentiable curve `γ` with field `γ'` such that `⟪γ' t, u⟫ = − f' (γ t) u`
for every vector `u`: this is the equation `γ' = −∇f` unfolded through the
Riesz representation, without having to name the gradient.

English mirror of `Grokking/Conservation.lean` (FR-first canonical), EPIC #4980
(i18n Lean). Convention ratified 2026-07-04 (issue #4980): namespace
`Grokking_en` (anti-collision with the FR `Grokking` namespace); cross-module
`_en` imports `_en`; non-docstring proof code unchanged.
-/
import Mathlib

open Finset
open scoped InnerProductSpace Topology

namespace Grokking_en

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The effective loss and its two observables -/

/-- `ℓ₀`: sum of squared parallelogram defects over a finite set of quadruples `Q`
(Eq. 22 of Appendix F, up to the factor `1/|Q|` — a time factor, with no effect
on the conservation laws). -/
noncomputable def loss0 (Q : Finset (ι × ι × ι × ι)) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ q ∈ Q, ‖(x q.1 + x q.2.1) - (x q.2.2.1 + x q.2.2.2)‖ ^ 2

/-- `Z₀`: quadratic energy of the representation (Eq. 24) — the square of the
Euclidean norm for scalar embeddings. -/
noncomputable def Z0 (x : EuclideanSpace ℝ ι) : ℝ := ‖x‖ ^ 2

/-- `C`: sum of the coordinates — the center of mass of the representation times
the number of embeddings (Eq. 24). -/
def Cmass (x : EuclideanSpace ℝ ι) : ℝ := ∑ k, x k

/-- `ℓ_eff = ℓ₀ / Z₀`: the effective loss (Eqs. 5 and 22 of the paper). -/
noncomputable def effLoss (Q : Finset (ι × ι × ι × ι)) (x : EuclideanSpace ℝ ι) : ℝ :=
  loss0 Q x / Z0 x

/-- The constant vector `1`: the translation direction, a symmetry of ℓ₀. -/
def onesVec : EuclideanSpace ℝ ι := WithLp.toLp (2 : ENNReal) fun _ => 1

/-! ### The two symmetries of ℓ₀ -/

/-- ℓ₀ is invariant under constant translation: a parallelogram defect only
depends on differences between embeddings, and the translation `b` cancels in
`E_i + E_j − E_m − E_n`. This is the identity `∑_k ∂ℓ₀/∂E_k = 0` of Appendix F,
proved without any gradient computation. -/
theorem loss0_translate (Q : Finset (ι × ι × ι × ι)) (x : EuclideanSpace ℝ ι)
    (b : ℝ) : loss0 Q (x + WithLp.toLp (2 : ENNReal) fun _ => b) = loss0 Q x := by
  simp only [loss0, PiLp.add_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  have key : (x q.1 + b + (x q.2.1 + b)) - (x q.2.2.1 + b + (x q.2.2.2 + b))
      = (x q.1 + x q.2.1) - (x q.2.2.1 + x q.2.2.2) := by ring
  simp only [key]

/-- The vector `c • 1` is the constant translation of value `c`. -/
theorem smul_onesVec (c : ℝ) :
    c • onesVec = (WithLp.toLp (2 : ENNReal) fun _ => c : EuclideanSpace ℝ ι) := by
  ext k
  simp [onesVec, PiLp.smul_apply, PiLp.toLp_apply]

/-- ℓ₀ is 2-homogeneous: `ℓ₀ (a • x) = a² • ℓ₀ x`. This is Euler's identity
`∑_k ∂ℓ₀/∂E_k · E_k = 2ℓ₀` of Appendix F, proved without any gradient computation. -/
theorem loss0_smul (Q : Finset (ι × ι × ι × ι)) (a : ℝ) (x : EuclideanSpace ℝ ι) :
    loss0 Q (a • x) = a ^ 2 * loss0 Q x := by
  have hc : ∀ i : ι, (a • x) i = a * x i := fun i => by rw [PiLp.smul_apply, smul_eq_mul]
  unfold loss0
  have key : ∀ q : ι × ι × ι × ι,
      ‖((a • x) q.1 + (a • x) q.2.1) - ((a • x) q.2.2.1 + (a • x) q.2.2.2)‖ ^ 2
        = a ^ 2 * ‖(x q.1 + x q.2.1) - (x q.2.2.1 + x q.2.2.2)‖ ^ 2 := by
    intro q
    rw [hc q.1, hc q.2.1, hc q.2.2.1, hc q.2.2.2]
    have hv : (a * x q.1 + a * x q.2.1) - (a * x q.2.2.1 + a * x q.2.2.2)
        = a * ((x q.1 + x q.2.1) - (x q.2.2.1 + x q.2.2.2)) := by ring
    rw [hv, ← smul_eq_mul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => key q

/-- Z₀ is 2-homogeneous: `Z₀ (a • x) = a² • Z₀ x`. -/
theorem Z0_smul (a : ℝ) (x : EuclideanSpace ℝ ι) : Z0 (a • x) = a ^ 2 * Z0 x := by
  unfold Z0
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-! ### Three general differential-calculus lemmas -/

section GeneralCalculus

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The line `t ↦ a + t • b` is differentiable with velocity vector `b`. -/
theorem hasDerivAt_line (a b : X) : HasDerivAt (fun t : ℝ => a + t • b) b (0 : ℝ) := by
  simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
    (ContinuousLinearMap.hasDerivAt
      (ContinuousLinearMap.toSpanSingleton ℝ b) (x := (0 : ℝ))).const_add a

/-- **Euler for 0-homogeneous functions.** If `f` is differentiable at `a` and
0-homogeneous along the radial line (`f (c • a) = f a` for all `c ≠ 0`), then the
radial directional derivative vanishes: `f' a a = 0`. -/
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

/-- **Translation invariance ⟹ killed direction.** If `f` is differentiable at `x`
and invariant under translation in direction `b` (`f (y + c • b) = f y` for all
`c`), then `f' x b = 0`. -/
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

/-! ### Regularity of the observables -/

/-- The coordinates of a Euclidean space are differentiable (continuous linear
forms). -/
theorem differentiable_coord (k : ι) :
    Differentiable ℝ (fun x : EuclideanSpace ℝ ι => x k) := by
  show Differentiable ℝ (fun x => (EuclideanSpace.proj (𝕜 := ℝ) k) x)
  exact (EuclideanSpace.proj (𝕜 := ℝ) k).differentiable

/-- ℓ₀ is differentiable: a finite sum of squares of continuous linear forms. -/
theorem differentiable_loss0 (Q : Finset (ι × ι × ι × ι)) :
    Differentiable ℝ (loss0 Q) := by
  have hnorm : ∀ r : ℝ, ‖r‖ ^ 2 = r ^ 2 := fun r => by rw [Real.norm_eq_abs, sq_abs]
  unfold loss0
  simp only [hnorm]
  refine Differentiable.fun_sum fun q _ => ?_
  exact (((differentiable_coord q.1).add (differentiable_coord q.2.1)).sub
    ((differentiable_coord q.2.2.1).add (differentiable_coord q.2.2.2))).pow 2

/-- Z₀ is differentiable: it is `∑ k, x k ^ 2`, a finite sum of squares of
continuous linear forms. -/
theorem differentiable_Z0 : Differentiable ℝ (Z0 : EuclideanSpace ℝ ι → ℝ) := by
  have h : (Z0 : EuclideanSpace ℝ ι → ℝ) = fun x => ∑ k, x k * x k := by
    funext x
    unfold Z0
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    exact Finset.sum_congr rfl fun k _ => by
      rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, pow_two]
  rw [h]
  exact Differentiable.fun_sum fun k _ => (differentiable_coord k).mul (differentiable_coord k)

/-- ℓ_eff is differentiable wherever `Z₀ ≠ 0` (quotient of differentiable
functions with nonzero denominator). -/
theorem differentiableAt_effLoss (Q : Finset (ι × ι × ι × ι)) {x : EuclideanSpace ℝ ι}
    (hx : Z0 x ≠ 0) : DifferentiableAt ℝ (effLoss Q) x := by
  have hinv : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ ι => (Z0 y)⁻¹) x :=
    (differentiable_Z0 x).inv hx
  have hmul : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ ι => loss0 Q y * (Z0 y)⁻¹) x :=
    (differentiable_loss0 Q x).mul hinv
  unfold effLoss
  simpa only [div_eq_mul_inv] using hmul

theorem hasFDerivAt_effLoss (Q : Finset (ι × ι × ι × ι)) {x : EuclideanSpace ℝ ι}
    (hx : Z0 x ≠ 0) : HasFDerivAt (effLoss Q) (fderiv ℝ (effLoss Q) x) x :=
  (differentiableAt_effLoss Q hx).hasFDerivAt

/-! ### Conservation of Z₀ along the flow of ℓ_eff -/

/-- **Z₀ is conserved along the flow of ℓ_eff.** If `γ` follows `−∇(ℓ₀/Z₀)` and
never crosses `Z₀ = 0` (where ℓ_eff is not defined), then `t ↦ ‖γ t‖²` is
constant: the norm of the representation can neither collapse nor diverge along
the effective dynamics. Proof: the derivative of `‖γ‖²` is `2⟪γ, γ'⟫`, and
`⟪γ', γ⟫ = −(ℓ_eff)' γ γ = 0` by the Euler lemma, ℓ_eff being 0-homogeneous
(quotient of two 2-homogeneous functions). -/
theorem Z0_conserved {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {f : X → ℝ} {γ : ℝ → X} {γ' : ℝ → X}
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
  have hrad : ∀ r, ⟪γ r, γ' r⟫_ℝ = 0 := fun r => by
    rw [real_inner_comm (γ' r) (γ r)]
    exact hrad' r
  have key : ∀ r, HasDerivAt (fun u => ‖γ u‖ ^ 2) 0 r := by
    intro r
    have h := HasDerivAt.inner ℝ (hγ r) (hγ r)
    rw [real_inner_comm (γ' r) (γ r), hrad' r, add_zero] at h
    have hfun : (fun u => ⟪γ u, γ u⟫_ℝ) = fun u => ‖γ u‖ ^ 2 :=
      funext fun u => real_inner_self_eq_norm_sq (γ u)
    rwa [hfun] at h
  exact eq_of_hasDerivAt_zero key s t

/-! ### C along the flows: conservation for ℓ₀, residual term for ℓ_eff -/

/-- Pairing with `1` recovers C: `⟪1, x⟫ = ∑ k, x k`. -/
theorem inner_onesVec (x : EuclideanSpace ℝ ι) : ⟪onesVec, x⟫_ℝ = Cmass x := by
  rw [PiLp.inner_apply]
  unfold Cmass onesVec
  simp [RCLike.inner_apply]

/-- The derivative of `C ∘ γ` along a trajectory is the pairing of its field
with `1`. -/
theorem deriv_Cmass {γ : ℝ → EuclideanSpace ℝ ι} {γ' : ℝ → EuclideanSpace ℝ ι}
    (hγ : ∀ t, HasDerivAt γ (γ' t) t) (t : ℝ) :
    HasDerivAt (fun s => Cmass (γ s)) (⟪onesVec, γ' t⟫_ℝ) t := by
  have hconst : HasDerivAt (fun _ : ℝ => onesVec) (0 : EuclideanSpace ℝ ι) t :=
    hasDerivAt_const (c := onesVec) (x := t)
  have h := HasDerivAt.inner ℝ hconst (hγ t)
  rw [inner_zero_left, add_zero] at h
  have hfun : (fun s => ⟪onesVec, γ s⟫_ℝ) = fun s => Cmass (γ s) :=
    funext fun s => inner_onesVec (γ s)
  rwa [hfun] at h

/-- **C is conserved along the flow of ℓ₀.** If `γ` follows `−∇ℓ₀`, then
`t ↦ ∑ k, γ t k` is constant: translation being a symmetry of ℓ₀, its
differential kills the constant direction `1`, and `C` is the pairing with that
direction. -/
theorem C_conserved_l0 (Q : Finset (ι × ι × ι × ι)) {γ : ℝ → EuclideanSpace ℝ ι}
    {γ' : ℝ → EuclideanSpace ℝ ι}
    (hγ : ∀ t, HasDerivAt γ (γ' t) t)
    (hflow : ∀ t u, ⟪γ' t, u⟫_ℝ = -fderiv ℝ (loss0 Q) (γ t) u)
    (s t : ℝ) : Cmass (γ s) = Cmass (γ t) := by
  have hkill : ∀ r, ⟪onesVec, γ' r⟫_ℝ = 0 := by
    intro r
    rw [real_inner_comm, hflow r onesVec,
      fderiv_of_translateInvariant ((differentiable_loss0 Q (γ r)).hasFDerivAt)
      (fun c y => by
        have := loss0_translate Q y c
        rwa [← smul_onesVec (ι := ι) c] at this)]
    simp
  have key : ∀ r, HasDerivAt (fun u => Cmass (γ u)) 0 r := by
    intro r
    have h := deriv_Cmass hγ r
    rwa [hkill r] at h
  exact eq_of_hasDerivAt_zero key s t

/-- **The residual term.** Along the flow of ℓ_eff = ℓ₀/Z₀ (never `Z₀ = 0`), the
derivative of C is exactly `2 ℓ₀ C / Z₀²`. Appendix F of the paper obtains
`dC/dt = 0` by writing only the term `−(1/Z₀) ∑_k ∂ℓ₀/∂E_k` of the quotient rule;
the missing `∂Z₀` term is precisely this one, proportional to C.

Proof: `C` is the pairing with the constant vector `1`, so
`(C ∘ γ)' t = ⟪1, γ' t⟫ = −(ℓ_eff)' (γ t) 1`. Along the line `s ↦ γ t + s • 1`,
ℓ₀ is constant (translation symmetry) and `Z₀` becomes `Z₀ + 2 s • C + s² • ‖1‖²`:
the derivative of the quotient at `s = 0` is `−2 ℓ₀ C / Z₀²`, hence the result. -/
theorem deriv_C_along_eff (Q : Finset (ι × ι × ι × ι)) {γ : ℝ → EuclideanSpace ℝ ι}
    {γ' : ℝ → EuclideanSpace ℝ ι}
    (hγ : ∀ t, HasDerivAt γ (γ' t) t)
    (hflow : ∀ t u, ⟪γ' t, u⟫_ℝ = -fderiv ℝ (effLoss Q) (γ t) u)
    (hZ0 : ∀ t, Z0 (γ t) ≠ 0) (t : ℝ) :
    HasDerivAt (fun s => Cmass (γ s))
      ((2 * loss0 Q (γ t) / Z0 (γ t) ^ 2) * Cmass (γ t)) t := by
  -- The derivative of C ∘ γ is the pairing of the field with 1, i.e. −(ℓ_eff)' (γ t) 1 :
  have h1 : HasDerivAt (fun s => Cmass (γ s)) (⟪onesVec, γ' t⟫_ℝ) t := deriv_Cmass hγ t
  have h2 : ⟪onesVec, γ' t⟫_ℝ = -fderiv ℝ (effLoss Q) (γ t) onesVec := by
    rw [real_inner_comm]
    exact hflow t onesVec
  -- Closed form of ℓ_eff along the line s ↦ γ t + s • 1 :
  have hnum : ∀ s : ℝ, loss0 Q (γ t + s • onesVec) = loss0 Q (γ t) := by
    intro s
    rw [smul_onesVec (ι := ι) s]
    exact loss0_translate Q (γ t) s
  have hx1 : ⟪onesVec, γ t⟫_ℝ = Cmass (γ t) := inner_onesVec (γ t)
  have hline : HasDerivAt (fun s : ℝ => γ t + s • onesVec) onesVec (0 : ℝ) :=
    hasDerivAt_line (γ t) onesVec
  -- the numerator ℓ₀ is constant along the line (translation symmetry):
  have hg1 : HasDerivAt (fun s : ℝ => loss0 Q (γ t + s • onesVec)) 0 (0 : ℝ) := by
    rw [funext hnum]
    exact hasDerivAt_const _ _
  -- the denominator Z₀ derives to 2 • C (‖x + s•1‖² = ‖x‖² + 2s⟪1,x⟫ + s²‖1‖²):
  have hg2 : HasDerivAt (fun s : ℝ => Z0 (γ t + s • onesVec)) (2 * Cmass (γ t)) (0 : ℝ) := by
    have h := HasDerivAt.inner ℝ hline hline
    simp only [zero_smul, add_zero] at h
    rw [real_inner_comm onesVec (γ t), hx1, ← two_mul] at h
    rw [show (fun s : ℝ => Z0 (γ t + s • onesVec))
        = fun s => ⟪γ t + s • onesVec, γ t + s • onesVec⟫_ℝ from
      funext fun s => (real_inner_self_eq_norm_sq _).symm]
    exact h
  -- the composite itself, with derivative (ℓ_eff)' (γ t) 1 :
  have hcomp : HasDerivAt (fun s => loss0 Q (γ t + s • onesVec) / Z0 (γ t + s • onesVec))
      (fderiv ℝ (effLoss Q) (γ t) onesVec) (0 : ℝ) := by
    have hf0 : HasFDerivAt (effLoss Q) (fderiv ℝ (effLoss Q) (γ t))
        ((fun s : ℝ => γ t + s • onesVec) 0) := by simpa using hasFDerivAt_effLoss Q (hZ0 t)
    have hc := hf0.comp_hasDerivAt (0 : ℝ) hline
    exact hc
  -- quotient rule on num/den along the line:
  have hq : HasDerivAt (fun s => loss0 Q (γ t + s • onesVec) / Z0 (γ t + s • onesVec))
      ((0 * Z0 (γ t) - loss0 Q (γ t) * (2 * Cmass (γ t))) / Z0 (γ t) ^ 2) (0 : ℝ) := by
    have hne0 : Z0 (γ t + (0 : ℝ) • onesVec) ≠ 0 := by
      simpa [zero_smul, add_zero] using hZ0 t
    simpa [zero_smul, add_zero] using HasDerivAt.fun_div hg1 hg2 hne0
  have hq' := hcomp.unique hq
  rw [h2, hq'] at h1
  have hval : -((0 * Z0 (γ t) - loss0 Q (γ t) * (2 * Cmass (γ t))) / Z0 (γ t) ^ 2)
      = (2 * loss0 Q (γ t) / Z0 (γ t) ^ 2) * Cmass (γ t) := by
    have h2ne : Z0 (γ t) ^ 2 ≠ 0 := pow_ne_zero 2 (hZ0 t)
    field_simp
    ring
  rw [hval] at h1
  exact h1

/-- **The centered hyperplane is invariant.** If the representation is centered
at time `0` (`C = 0`) and follows the flow of ℓ_eff, it stays centered for all
times. This is the exact form of the paper's "conservation of C": true as stated
for the flow of ℓ₀ alone, and for ℓ_eff in the normalized regime (centered
embeddings) where C is zero by construction. The derivative of `C ∘ γ` being
proportional to C itself (`η' = κ η`), the integrating factor `exp(−∫κ)` shows
that the solution starting from zero stays there. -/
theorem meanZero_invariant (Q : Finset (ι × ι × ι × ι)) {γ : ℝ → EuclideanSpace ℝ ι}
    {γ' : ℝ → EuclideanSpace ℝ ι}
    (hγ : ∀ t, HasDerivAt γ (γ' t) t)
    (hflow : ∀ t u, ⟪γ' t, u⟫_ℝ = -fderiv ℝ (effLoss Q) (γ t) u)
    (hZ0 : ∀ t, Z0 (γ t) ≠ 0)
    (hκcont : Continuous (fun s => 2 * loss0 Q (γ s) / Z0 (γ s) ^ 2))
    (h0 : Cmass (γ 0) = 0) (t : ℝ) : Cmass (γ t) = 0 := by
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ → ℝ, ∀ s, κ s = 2 * loss0 Q (γ s) / Z0 (γ s) ^ 2 :=
    ⟨_, fun _ => rfl⟩
  have hκc : Continuous κ := by
    rw [show κ = fun s => 2 * loss0 Q (γ s) / Z0 (γ s) ^ 2 from funext hκdef]
    exact hκcont
  have hη : ∀ s, HasDerivAt (fun r => Cmass (γ r)) (κ s * Cmass (γ s)) s := by
    intro s
    rw [hκdef s]
    exact deriv_C_along_eff Q hγ hflow hZ0 s
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ → ℝ, ∀ u, K u = ∫ r in 0..u, κ r := ⟨_, fun _ => rfl⟩
  have hKd : ∀ u, HasDerivAt K (κ u) u := by
    intro u
    rw [show K = fun u => ∫ r in 0..u, κ r from funext hKdef]
    exact intervalIntegral.integral_hasDerivAt_right (hκc.intervalIntegrable (0 : ℝ) u)
      (hκc.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 u)) hκc.continuousAt
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ → ℝ, ∀ s, F s = Cmass (γ s) * Real.exp (- K s) :=
    ⟨_, fun _ => rfl⟩
  have hFd : ∀ s, HasDerivAt F 0 s := by
    intro s
    have h := HasDerivAt.mul (hη s) ((hKd s).neg.exp)
    simp only [Pi.neg_apply] at h
    have hval : (κ s * Cmass (γ s)) * Real.exp (- K s)
        + Cmass (γ s) * (Real.exp (- K s) * -(κ s)) = 0 := by ring
    rw [hval] at h
    rw [show F = fun r => Cmass (γ r) * Real.exp (- K r) from funext hFdef]
    exact h
  have hF0 : F 0 = 0 := by
    have hK0 : K 0 = 0 := by rw [hKdef 0, intervalIntegral.integral_same]
    rw [hFdef 0, hK0, h0, zero_mul]
  have hFt : F t = 0 := by
    rw [eq_of_hasDerivAt_zero hFd t 0, hF0]
  have hlast : Cmass (γ t) * Real.exp (- K t) = 0 := by
    rw [← hFdef t]
    exact hFt
  rcases mul_eq_zero.mp hlast with h | h
  · exact h
  · exact absurd h (Real.exp_ne_zero _)

end Grokking_en
