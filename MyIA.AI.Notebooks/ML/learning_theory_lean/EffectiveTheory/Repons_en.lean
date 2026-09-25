import Mathlib

/-!
# Repons — effective theory R06: clustering by class and a conserved quantity

Tranche **R06** of the "effective theory" arc (#16741, issue #16752):
*Baek, Liu & Tegmark, GenEFT — Understanding Statics and Dynamics of Model
Generalization via Effective Theory* (arXiv:2402.05916, 2024; GDrive PDF
sha8 `B589C4EF`).

Formalized content:

1. **Theorem 1 (GenEFT)** — `clustering_iff_injective_decoder`: for a
   classification autoencoder (output 1 when the two inputs share a class,
   0 otherwise) trained to zero loss, an injective decoder forces
   **clustering by class**: two nodes have the same representation if and
   only if they belong to the same class. The proof is the paper's
   constructive contradiction: if `E i = E j` for distinct classes, then
   `Dec (E i ∥ E k) = Dec (E j ∥ E k)` yields `1 = 0`; conversely, the same
   class ⟹ the outputs are both 1 for the witness `k = i`, and injectivity
   gives `E i = E j`.
2. **Appendix C, Eq. (11)** — `conservedHyperbola_deriv_zero`: the
   interaction system of two repons of one class (Eq. 8-10: decider
   `a₂` and half-separation `c` subject to `da₂/dt = −2 η_A c² a₂` and
   `dc/dt = −η_x a₂² c`) conserves the hyperbolic quantity
   `C = a₂² / (2 η_A) − c² / η_x`: its derivative is identically zero along
   every solution. This is the "Mathlib-style computational proof" requested
   by the issue: substitute the derivatives and cancel exactly,
   `−2 a₂² c² + 2 a₂² c² = 0`. The quantity separates the trajectories:
   `C > 0` ⟹ repon collision (generalization), `C < 0` ⟹ no collision
   (memorization) — the paper's harmonic-oscillator hyperbola.
3. **Appendix C, Eq. (16)** — `rel_eqn_autonomous`: in the paper's gradient
   flow each trajectory undergoes the same common-mode external forcing `g`
   on top of the linear flux `F`; in the difference `x₁ − x₂` it cancels
   exactly and the separation evolves autonomously — a Hooke spring
   `d(x₁ − x₂)/dt = F (x₁ − x₂)`. Migrated from the dissolved module
   `GenEFT.lean` (#17480).

Dependencies: Mathlib only (`hasDerivAt_pow`, `HasDerivAt.comp`,
`HasDerivAt.div_const`, `HasDerivAt.sub`, `field_simp`, `ring`,
`ContinuousLinearMap.map_sub`).
-/

namespace LearningTheory.EffectiveTheory_en

section Clustering

variable {V : Type*} {ι : Type*}

/-- **Theorem 1 (R06)**: zero-loss classification with an injective decoder
⟹ representations group exactly by class.

The decoder `dec : V × V → ℝ` acts on the concatenation of the embeddings
(`Dec (E x ∥ E y)` in the paper); the zero-loss hypothesis says its output is
the indicator of class equality (1 when the classes match, 0 otherwise).
The proof is the paper's constructive contradiction, with the witness
`k = i` (no third element needed: the paper uses a `k` from the class of
`i`, and `i` itself works). -/
theorem clustering_iff_injective_decoder
    (E : ι → V) (dec : V × V → ℝ) (cls : ι → ℕ)
    (hDec : Function.Injective dec)
    (hZeroLoss : ∀ x y, dec (E x, E y) = if cls x = cls y then 1 else 0) :
    ∀ i j, cls i = cls j ↔ E i = E j := by
  intro i j
  constructor
  · -- Same class ⟹ same representations: both outputs towards (E i)
    -- equal 1, and decoder injectivity identifies the pairs.
    intro hcls
    have h1 : dec (E i, E i) = 1 := by simp [hZeroLoss]
    have h2 : dec (E j, E i) = 1 := by simp [hZeroLoss, hcls]
    have hpair : (E i, E i) = (E j, E i) := hDec (by rw [h1, h2])
    exact congrArg Prod.fst hpair
  · -- Distinct classes ⟹ distinct representations (contrapositive by
    -- contradiction: if E i = E j, the same decoding towards witness i
    -- equals both 1 ((i,i)) and 0 ((j,i))).
    intro hE
    by_contra hne
    have key : dec (E i, E i) = dec (E j, E i) := by rw [hE]
    have h1 : dec (E i, E i) = 1 := by simp [hZeroLoss]
    have h0 : dec (E j, E i) = 0 := by
      have hji := hZeroLoss j i
      simp [Ne.symm hne] at hji
      exact hji
    rw [h1, h0] at key
    norm_num at key

end Clustering

section ConservedHyperbola

variable {ηA ηx : ℝ}

/-- **Appendix C (R06), Eq. (11)**: conserved quantity of the two-repon
system of one class. If `a₂` and `c` follow the effective equations
`da₂/dt = −2 η_A c² a₂` and `dc/dt = −η_x a₂² c` (Eq. 10), then
`t ↦ (a₂ t)² / (2 η_A) − (c t)² / ηx` has an identically zero derivative.

Computational proof: the derivative equals
`2 a₂ · (−2 η_A c² a₂) / (2 η_A) − 2 c · (−η_x a₂² c) / ηx = −2 a₂² c² +
2 a₂² c² = 0` — exact mutual cancellation, the harmonic-oscillator energy
structure flagged by the paper. -/
theorem conservedHyperbola_deriv_zero {a₂ c : ℝ → ℝ}
    (hηA : ηA ≠ 0) (hηx : ηx ≠ 0)
    (ha : ∀ t, HasDerivAt a₂ (-2 * ηA * (c t) ^ 2 * a₂ t) t)
    (hc : ∀ t, HasDerivAt c (-ηx * (a₂ t) ^ 2 * c t) t) :
    ∀ t, HasDerivAt (fun t => (a₂ t) ^ 2 / (2 * ηA) - (c t) ^ 2 / ηx) 0 t := by
  intro t
  have h1 := (hasDerivAt_pow 2 (a₂ t)).comp t (ha t)
  have h2 := (hasDerivAt_pow 2 (c t)).comp t (hc t)
  have H := (h1.div_const (2 * ηA)).sub (h2.div_const ηx)
  refine H.congr_deriv ?_
  field_simp
  ring

end ConservedHyperbola

/-! ## Dynamics — autonomy of the separation (Eq. 16)

Migrated from the dissolved module `GenEFT.lean` (#17480). -/

section Dynamics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Eq. 16 of Appendix C — autonomy of the separation.** In the paper's
gradient flow each trajectory undergoes the same external forcing `g` (the
pull-back term towards the target, carried by `Aᵀ y`) on top of the linear
flux `F` (the `-η_x AᵀA` term). This forcing is **common-mode**: in the
difference `x₁ - x₂` it cancels exactly, and the separation evolves
autonomously — a Hooke spring `d(x₁ - x₂)/dt = F (x₁ - x₂)` with
`F = -η_x AᵀA` weakening. -/
theorem rel_eqn_autonomous (x₁ x₂ : ℝ → E) (F : E →L[ℝ] E) (g : ℝ → E)
    (h₁ : ∀ t, HasDerivAt x₁ (F (x₁ t) + g t) t)
    (h₂ : ∀ t, HasDerivAt x₂ (F (x₂ t) + g t) t) (t : ℝ) :
    HasDerivAt (fun t => x₁ t - x₂ t) (F (x₁ t - x₂ t)) t := by
  have hd : HasDerivAt (fun t => x₁ t - x₂ t)
      ((F (x₁ t) + g t) - (F (x₂ t) + g t)) t :=
    (h₁ t).sub (h₂ t)
  convert hd using 2
  simp only [ContinuousLinearMap.map_sub]
  abel

end Dynamics

end LearningTheory.EffectiveTheory_en
