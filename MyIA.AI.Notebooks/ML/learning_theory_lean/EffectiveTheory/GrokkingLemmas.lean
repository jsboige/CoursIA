import Mathlib
import EffectiveTheory.Grokking

/-!
# GrokkingLemmas — apport propre du grain R02 (recadrage #16752)

Module frère de `EffectiveTheory.Grokking` (arbitrage ai-01 c.5790650195,
2026-09-23) : `Grokking.lean` porte déjà sur `main` les parallélogrammes
(Déf. 1, Props 1-2), les identités de l'appendice F, la conservation de `Z₀`
et la dynamique exacte de `C` le long du flot effectif
(`flow_deriv_sum_apply`). Ce module n'ajoute QUE le delta propre du grain
d'origine (branche `feature/16752-grokking-lean`), porté du cadre
`EuclideanSpace ℝ ι` vers le cadre `Fin p → ℝ` de `Grokking.lean` — le
transfert est une réécriture directe (sommes finies vs accouplement avec le
vecteur `1`), aucun lemme de transfert n'est nécessaire.

Contenu :

1. **`C_conserved_l0`** — la somme `C = Σ E k` est conservée le long du flot
   de `ℓ₀` (non normalisé) : la translation étant une symétrie de `ℓ₀`,
   `Σ_k ∂ℓ₀/∂E_k = 0` (`loss0_grad_sum_zero`, identité 1 de l'appendice F)
   tue la direction constante. Distinct du corollaire
   `flow_sum_constant_of_zero_loss` (flot *effectif*, régime à perte nulle).
2. **`meanZero_invariant`** — l'hyperplan centré `C = 0` est invariant le
   long du flot effectif : la dérivée de `C ∘ γ` est proportionnelle à `C`
   (`dC/dt = κ · C`, `flow_deriv_sum_apply`), le facteur intégrant
   `exp(−∫κ)` montre qu'une solution issue de zéro y reste. C'est la forme
   exacte de la « conservation de C » du papier dans le régime normalisé
   (plongements centrés).
3. **Lemmes génériques de calcul différentiel** (cadre : espace normé ou
   préhilbertien quelconque, aucune dépendance au cadre `Fin p → ℝ`) :
   `hasDerivAt_line` (dérivée de la droite `t ↦ a + t • b`),
   `euler_zero_homogeneous` (Euler pour les fonctions 0-homogènes),
   `fderiv_of_translateInvariant` (invariance par translation ⟹ direction
   tuée), `eq_of_hasDerivAt_zero` (dérivée nulle ⟹ constante) et
   `Z0_conserved` (conservation de la norme le long du flot `−∇f` d'une
   fonction 0-homogène).

Sources : *Liu, Michaud, Tegmark — Towards Understanding Grokking: An
Effective Theory of Representation Learning* (arXiv:2205.10343, 2022 ;
PDF GDrive sha8 `88CE88DB`), appendice F et section 4.2.
-/

namespace LearningTheory.EffectiveTheory

open Finset

open scoped InnerProductSpace Topology

/-! ### Lemmes génériques de calcul différentiel -/

section GeneralCalculus

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- La droite `t ↦ a + t • b` est dérivable de vecteur vitesse `b`. -/
theorem hasDerivAt_line (a b : X) : HasDerivAt (fun t : ℝ => a + t • b) b (0 : ℝ) := by
  simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
    (ContinuousLinearMap.hasDerivAt
      (ContinuousLinearMap.toSpanSingleton ℝ b) (x := (0 : ℝ))).const_add a

/-- **Euler pour les fonctions 0-homogènes.** Si `f` est différentiable en `a` et
0-homogène le long de la droite radiale (`f (c • a) = f a` pour tout `c ≠ 0`), alors
la dérivée directionnelle radiale est nulle : `f' a a = 0`. -/
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

/-- **Invariance par translation ⟹ direction tuée.** Si `f` est différentiable en `x`
et invariante par translation dans la direction `b` (`f (y + c • b) = f y` pour tout
`c`), alors `f' x b = 0`. -/
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

/-- **Dérivée nulle partout ⟹ constante.** Une courbe réelle dont la dérivée s'annule
en tout point est constante. -/
theorem eq_of_hasDerivAt_zero {g : ℝ → ℝ} (h : ∀ t, HasDerivAt g 0 t) (s t : ℝ) :
    g s = g t :=
  is_const_of_deriv_eq_zero (fun u => (h u).differentiableAt)
    (fun u => (h u).deriv) s t

end GeneralCalculus

/-! ### Conservation générique de la norme (flot d'une fonction 0-homogène) -/

section NormConservation

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- **Conservation de la norme le long du flot `−∇f` d'une fonction 0-homogène.**
Si `γ` suit `−∇f` (`⟪γ', u⟫ = −f' (γ) u`) et `f (c • x) = f x` pour `c ≠ 0`,
alors `‖γ‖` est constante : la vitesse est orthogonale au rayon (Euler).
Version générique en préhilbertien réel de `flow_sumsq0_constant`
(`Grokking.lean`, Eq. 26), pour une `f` quelconque. -/
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

/-! ### C le long du flot de ℓ₀ : conservation inconditionnelle -/

section L0Flow

variable {p : ℕ}

/-- Composante d'une courbe dérivable à valeurs dans `Fin p → ℝ` : si `γ` a la
vitesse `v` en `t`, chaque composante `s ↦ γ s k` a la vitesse `v k`. -/
private theorem hasDerivAt_component' (γ : ℝ → (Fin p → ℝ)) (k : Fin p) (t : ℝ)
    {v : Fin p → ℝ} (h : HasDerivAt γ v t) : HasDerivAt (fun s => γ s k) (v k) t := by
  have hc := ((ContinuousLinearMap.proj k : (Fin p → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp t h).hasDerivAt
  have h₁ : Filter.EventuallyEq (nhds t) (fun s => γ s k)
      (↑(ContinuousLinearMap.proj k : (Fin p → ℝ) →L[ℝ] ℝ) ∘ γ) :=
    Filter.Eventually.of_forall fun s => rfl
  exact (hc.congr_of_eventuallyEq h₁).congr_deriv (by simp)

/-- Somme des composantes : si `γ` a la vitesse `v` en `t`, la somme
`s ↦ Σ_k γ s k` a la vitesse `Σ_k v k`. -/
private theorem hasDerivAt_sumC' {γ : ℝ → (Fin p → ℝ)} (t : ℝ) {v : Fin p → ℝ}
    (hv : HasDerivAt γ v t) : HasDerivAt (fun s => ∑ k, γ s k) (∑ k, v k) t := by
  have h := HasDerivAt.sum (u := (Finset.univ : Finset (Fin p)))
    fun k _ => hasDerivAt_component' γ k t hv
  have heq : (∑ k : Fin p, fun s => γ s k) = (fun s => ∑ k, γ s k) :=
    funext fun s_ => Finset.sum_apply s_ Finset.univ fun k => fun s => γ s k
  rw [heq] at h
  exact h

/-- **Flot de `ℓ₀` (non normalisé)** : une courbe `γ` suit la descente de
gradient de `ℓ₀` lorsque sa vitesse en `t` vaut `−∇ℓ₀ (γ t)` (à comparer avec
`IsEffectiveFlow`, le flot normalisé `ℓ₀/Z₀` de `Grokking.lean`). -/
def IsL0Flow (P : Finset ((Fin p × Fin p) × (Fin p × Fin p)))
    (γ : ℝ → (Fin p → ℝ)) : Prop :=
  ∀ t, HasDerivAt γ (-(gradLoss0 P (γ t))) t

/-- **`C = Σ E k` est conservée le long du flot de `ℓ₀`**, inconditionnellement.
La translation `E ↦ E + c • 1` est une symétrie de `ℓ₀` (chaque contrainte de
parallélogramme contribue `δ_ik + δ_jk − δ_mk − δ_nk`, de somme nulle —
c'est l'identité 1 de l'appendice F, `loss0_grad_sum_zero`), donc la
différentielle tue la direction constante et `dC/dt = −Σ_k ∂ℓ₀/∂E_k = 0`.

Distinct du corollaire `flow_sum_constant_of_zero_loss` de `Grokking.lean` :
celui-ci concerne le flot *effectif* (normalisé) et exige le régime à perte
nulle ; ici le flot de `ℓ₀` seul conserve `C` sans hypothèse. -/
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

/-! ### Invariance de l'hyperplan centré le long du flot effectif -/

section MeanZero

variable {p : ℕ}

/-- **L'hyperplan centré est invariant.** Si la représentation est centrée à
l'instant `0` (`C = 0`) et suit le flot effectif, elle reste centrée pour tout
temps. C'est la forme exacte de la « conservation de C » du papier : vraie
telle quelle pour le flot de `ℓ₀` seul (`C_conserved_l0`), et pour le flot
effectif dans le régime normalisé (plongements centrés) où `C` est nulle par
construction. La dérivée de `C ∘ γ` étant proportionnelle à `C`
lui-même (`dC/dt = κ · C`, `flow_deriv_sum_apply`), le facteur intégrant
`exp(−∫κ)` montre que la solution issue de zéro y reste. -/
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

end LearningTheory.EffectiveTheory
