/-
  Calibration target: Schwartz spaces — decay and regularity
  ==========================================================

  The Schwartz space is the space of smooth functions all of whose
  derivatives decay faster than any power of `‖x‖`. Its distinctive
  capability is twofold, and that duality is what this module teaches:

  * REGULARITY — `C^∞` smoothness, carried by the `smooth'` field;
  * DECAY — the `decay'` field, which uniformly bounds
    `‖x‖^k * ‖iteratedFDeriv ℝ n f x‖` by a constant.

  The family of seminorms `SchwartzMap.seminorm 𝕜 k n` measures both at once:
  `k` indexes decay, `n` the order of differentiation. That structure is what
  gives the space its locally convex topology, and it is what the theorems
  below make manipulable.

  The module instantiates the Mathlib API actually pinned by the lake
  (`Mathlib.Analysis.Distribution.SchwartzSpace.Basic`) — no definition is
  reinvented, no proof is left as `sorry`.

  Harness paths exercised:
  - Target S1 (exists_decay_bound): P3 — the prover must discover the named
    lemma `SchwartzMap.decay`; a bare `simp` will not find it.
  - Target S2 (seminorm_bounds_decay): P3 — the named lemma
    `SchwartzMap.le_seminorm`, not to be confused with its converse.
  - Target S3 (seminorm_le_of_pointwise_bound): P1 — the converse bridge
    `SchwartzMap.seminorm_le_bound`, with its positivity hypothesis.
  - Target S4 (seminorm_smul): P3 — homogeneity comes from the generic lemma
    `SeminormClass.map_smul_eq_mul`, not from `simp`.
  - Target S5 (seminorm_add_le): P1 — subadditivity via the
    `Seminorm.add_le'` field.
  - Target S6 (norm_le_seminorm_div_pow): P2 — the REAL polynomial decay is
    derived from the seminorm; it requires `le_div_iff₀` and then a
    `mul_comm` swap (a two-step proof, the error is distant).
  - Target S7 (exists_schwartzMap_of_compactSupport): P2 — the closure
    statement `HasCompactSupport.toSchwartzMap`, with the equality of the
    underlying function.

  Target difficulty: Goldilocks zone (3-10 prover iterations).

  i18n convention #4980 (sibling pair): this file is the EN sibling of
  `Calibration/Distribution.lean`; the two are never imported together.
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Tactic

open scoped SchwartzMap ContDiff Topology

namespace Calibration.Distribution

/-! ## 1. The contract: decay bounded by a constant -/

section Decay

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Raw decay (target S1).** For every Schwartz function `f` and every pair
of indices `(k, n)` there is a strictly positive constant `C` bounding
`‖x‖^k * ‖iteratedFDeriv ℝ n f x‖` for all `x`.

This is the `decay'` field of the structure, refined by the `decay` lemma
which additionally guarantees `0 < C` (needed to divide). -/
theorem exists_decay_bound (f : 𝓢(E, F)) (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C :=
  f.decay k n

/-- **Regularity (the first half of the contract).** Every Schwartz function is
smooth to infinite order: this is the `smooth'` field, read here as a public
statement about the underlying function. -/
theorem smooth_of_schwartz (f : 𝓢(E, F)) : ContDiff ℝ ∞ (f : E → F) :=
  f.smooth'

/-- **Decay implies vanishing at infinity.** This is the concrete meaning of
"decays faster than any power": `f` tends to `0` along the `cocompact`
filter. -/
theorem tendsto_zero_atInfty [ProperSpace E] (f : 𝓢(E, F)) :
    Filter.Tendsto (f : E → F) (Filter.cocompact E) (𝓝 0) :=
  f.tendsto_cocompact

end Decay

/-! ## 2. The seminorms: measuring decay and regularity in one gesture

`SchwartzMap.seminorm 𝕜 k n` is the best constant in the estimate
`‖x‖^k * ‖iteratedFDeriv ℝ n f x‖ ≤ C`. The theorem `le_seminorm` says it
realizes that estimate (it is an upper bound); `seminorm_le_bound` says it is
the least such constant (every working constant bounds it): the two halves of
the infimum definition, taken from both ends. -/

section Seminorm

variable {𝕜 : Type*} [NormedField 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- **The seminorm realizes the estimate (target S2).** At every point `x`, the
Schwartz estimate is bounded by the seminorm of indices `(k, n)`.

This is the "the seminorm is an upper bound" half. -/
theorem seminorm_bounds_decay (f : 𝓢(E, F)) (k n : ℕ) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ SchwartzMap.seminorm 𝕜 k n f :=
  SchwartzMap.le_seminorm 𝕜 k n f x

/-- **The seminorm is the least upper bound (target S3).** Converse of the
previous theorem: bounding the estimate at EVERY point by a constant `M`
bounds the seminorm by `M`. The hypothesis `hMp : 0 ≤ M` is indispensable
(without it, a strictly negative constant would bound everything). -/
theorem seminorm_le_of_pointwise_bound (f : 𝓢(E, F)) (k n : ℕ) {M : ℝ}
    (hMp : 0 ≤ M)
    (hM : ∀ x : E, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ M) :
    SchwartzMap.seminorm 𝕜 k n f ≤ M :=
  SchwartzMap.seminorm_le_bound 𝕜 k n f hMp hM

/-- **Homogeneity (target S4).** The scalar comes out multiplicatively, as a
norm, of the seminorm. This is the `SMul` axiom of `Seminorm`, read through
the generic lemma `SeminormClass.map_smul_eq_mul`. -/
theorem seminorm_smul (c : 𝕜) (f : 𝓢(E, F)) (k n : ℕ) :
    SchwartzMap.seminorm 𝕜 k n (c • f) = ‖c‖ * SchwartzMap.seminorm 𝕜 k n f :=
  map_smul_eq_mul (SchwartzMap.seminorm 𝕜 k n) c f

/-- **Subadditivity (target S5).** A seminorm is not additive, it is
subadditive: the triangle inequality is an axiom of the structure, read
through the `Seminorm.add_le'` field. -/
theorem seminorm_add_le (f g : 𝓢(E, F)) (k n : ℕ) :
    SchwartzMap.seminorm 𝕜 k n (f + g) ≤
      SchwartzMap.seminorm 𝕜 k n f + SchwartzMap.seminorm 𝕜 k n g :=
  (SchwartzMap.seminorm 𝕜 k n).add_le' f g

/-- **Effective polynomial decay (target S6).** The seminorm of indices
`(k, 0)` — decay of order `k`, no derivative — yields POLYNOMIAL decay of the
function itself: away from the origin,

  `‖f x‖ ≤ C_k / ‖x‖^k`.

The proof moves `‖x‖^k` to the denominator (`le_div_iff₀`, whose hypothesis
`0 < ‖x‖` is what authorizes it), then commutes the two factors to land on
`norm_pow_mul_le_seminorm`. -/
theorem norm_le_seminorm_div_pow (f : 𝓢(E, F)) (k : ℕ) {x : E} (hx : 0 < ‖x‖) :
    ‖f x‖ ≤ SchwartzMap.seminorm 𝕜 k 0 f / ‖x‖ ^ k := by
  rw [le_div_iff₀ (pow_pos hx k)]
  exact (mul_comm _ _).trans_le (SchwartzMap.norm_pow_mul_le_seminorm 𝕜 f k x)

/-- **The `(0, 0)` seminorm bounds the uniform norm.** The `k = 0` special
case of the previous theorem, without any hypothesis: everywhere,
`‖f x‖ ≤ seminorm 𝕜 0 0 f`. That seminorm is the one controlling the sup
of `f`. -/
theorem norm_le_seminorm_zero (f : 𝓢(E, F)) (x : E) :
    ‖f x‖ ≤ SchwartzMap.seminorm 𝕜 0 0 f :=
  SchwartzMap.norm_le_seminorm 𝕜 f x

end Seminorm

/-! ## 3. Closure: compact support manufactures Schwartz functions -/

section CompactSupport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **A smooth compactly supported function is Schwartz (target S7).** The
closure of the class is a fact about compact support: outside the support the
function is zero, so decay is obtained without any hypothesis.

The conclusion additionally witnesses preservation of the underlying function
— `toSchwartzMap` does not change the function, it dresses it in the
contract. -/
theorem exists_schwartzMap_of_compactSupport {f : E → F}
    (hsupp : HasCompactSupport f) (hsmooth : ContDiff ℝ ∞ f) :
    ∃ g : 𝓢(E, F), (g : E → F) = f :=
  ⟨hsupp.toSchwartzMap hsmooth, rfl⟩

end CompactSupport

end Calibration.Distribution
