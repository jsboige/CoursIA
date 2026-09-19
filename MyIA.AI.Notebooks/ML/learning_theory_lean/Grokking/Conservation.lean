/-
Grokking — lois de conservation de la théorie effective (Appendice F de R02).

Formalise l'Appendice F de « Towards Understanding Grokking » (Liu, Michaud, Tegmark ;
arXiv:2205.10343), issue #16752. La dynamique des plongements est modélisée par un flot
de gradient pour la perte effective

  ℓ_eff = ℓ₀ / Z₀,  ℓ₀ = ∑_{(i,j,m,n) ∈ Q} ‖E_i + E_j − E_m − E_n‖²,  Z₀ = ‖E‖²,

où `Q` est un ensemble fini de quadruples d'indices (typiquement les parallélogrammes
permis `P₀` du module `Grokking.Effective`). Le papier annonce deux quantités
conservées : le centre de masse `C = ∑_k E_k` et l'énergie `Z₀ = ‖E‖²`.

Résultats :

* `Grokking.loss0_translate` / `Grokking.loss0_smul` — ℓ₀ invariante par translation et
  2-homogène. Ce sont les deux identités `∑_k ∂ℓ₀/∂E_k = 0` et
  `∑_k ∂ℓ₀/∂E_k · E_k = 2ℓ₀` de l'Appendice F, démontrées sans calcul de gradient.
* `Grokking.euler_zero_homogeneous`, `Grokking.fderiv_of_translateInvariant`,
  `Grokking.eq_of_hasDerivAt_zero` — trois lemmes généraux de calcul différentiel.
* `Grokking.Z0_conserved` — **Z₀ est conservée** le long du flot de ℓ_eff
  (l'échelle est une symétrie de ℓ_eff, et Euler tue la direction radiale). C'est ce
  qui interdit l'effondrement de la représentation sur zéro.
* `Grokking.C_conserved_l0` — **C est conservée** le long du flot de ℓ₀ seule
  (la translation est une symétrie de ℓ₀).
* `Grokking.deriv_C_along_eff` — **le complément honnête** : le long du flot de
  ℓ_eff = ℓ₀/Z₀, la dérivée de C vaut exactement `(2 ℓ₀ / Z₀²) • C`. La preuve de
  l'Appendice F écrit `dC/dt = −(1/Z₀) ∑_k ∂ℓ₀/∂E_k` en omettant le terme `∂Z₀` de la
  règle du quotient ; le calcul complet fait apparaître ce terme résiduel,
  proportionnel à C lui-même.
* `Grokking.meanZero_invariant` — corollaire : l'hyperplan `C = 0` (représentation
  centrée) est invariant le long du flot de ℓ_eff. C'est la forme exacte de la
  « conservation de C » du papier : elle vaut dans le cadre normalisé du texte
  principal (Éq. 4-5 : plongements centrés-réduits `Ẽ = (E − μ)/σ`), où C ≡ 0 par
  construction.

Espace de travail : plongements scalaires `x : EuclideanSpace ℝ ι` (dimension 1, le
réglage jouet du papier), `ι` fini quelconque. Alors Z₀ = ‖x‖² et C = ∑ k, x k.

Un flot de gradient pour `f : X → ℝ` (X préhilbertien réel) est une courbe `γ`
dérivable de champ `γ'` telle que `⟪γ' t, u⟫ = − f' (γ t) u` pour tout vecteur `u` :
c'est l'équation `γ' = −∇f` développée via la représentation de Riesz, sans avoir à
nommer le gradient.
-/
import Mathlib

open Finset
open scoped InnerProductSpace Topology

namespace Grokking

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### La perte effective et ses deux observables -/

/-- `ℓ₀` : somme des carrés des défauts de parallélogramme sur un ensemble fini de
quadruples `Q` (Éq. 22 de l'Appendice F, au facteur `1/|Q|` près — un facteur de temps,
sans effet sur les lois de conservation). -/
noncomputable def loss0 (Q : Finset (ι × ι × ι × ι)) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ q ∈ Q, ‖(x q.1 + x q.2.1) - (x q.2.2.1 + x q.2.2.2)‖ ^ 2

/-- `Z₀` : énergie quadratique de la représentation (Éq. 24) — le carré de la norme
euclidienne pour des plongements scalaires. -/
noncomputable def Z0 (x : EuclideanSpace ℝ ι) : ℝ := ‖x‖ ^ 2

/-- `C` : somme des coordonnées — le centre de masse de la représentation multiplié
par le nombre de plongements (Éq. 24). -/
def Cmass (x : EuclideanSpace ℝ ι) : ℝ := ∑ k, x k

/-- `ℓ_eff = ℓ₀ / Z₀` : la perte effective (Éq. 5 et 22 du papier). -/
noncomputable def effLoss (Q : Finset (ι × ι × ι × ι)) (x : EuclideanSpace ℝ ι) : ℝ :=
  loss0 Q x / Z0 x

/-- Le vecteur constant `1` : la direction de translation, symétrie de ℓ₀. -/
def onesVec : EuclideanSpace ℝ ι := WithLp.toLp (2 : ENNReal) fun _ => 1

/-! ### Les deux symétries de ℓ₀ -/

/-- ℓ₀ est invariante par translation constante : un défaut de parallélogramme ne
dépend que des différences entre plongements, et la translation `b` s'annule dans
`E_i + E_j − E_m − E_n`. C'est l'identité `∑_k ∂ℓ₀/∂E_k = 0` de l'Appendice F,
démontrée sans calcul de gradient. -/
theorem loss0_translate (Q : Finset (ι × ι × ι × ι)) (x : EuclideanSpace ℝ ι)
    (b : ℝ) : loss0 Q (x + WithLp.toLp (2 : ENNReal) fun _ => b) = loss0 Q x := by
  simp only [loss0, PiLp.add_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  have key : (x q.1 + b + (x q.2.1 + b)) - (x q.2.2.1 + b + (x q.2.2.2 + b))
      = (x q.1 + x q.2.1) - (x q.2.2.1 + x q.2.2.2) := by ring
  simp only [key]

/-- Le vecteur `c • 1` est la translation constante de valeur `c`. -/
theorem smul_onesVec (c : ℝ) :
    c • onesVec = (WithLp.toLp (2 : ENNReal) fun _ => c : EuclideanSpace ℝ ι) := by
  ext k
  simp [onesVec, PiLp.smul_apply, PiLp.toLp_apply]

/-- ℓ₀ est 2-homogène : `ℓ₀ (a • x) = a² • ℓ₀ x`. C'est l'identité d'Euler
`∑_k ∂ℓ₀/∂E_k · E_k = 2ℓ₀` de l'Appendice F, démontrée sans calcul de gradient. -/
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

/-- Z₀ est 2-homogène : `Z₀ (a • x) = a² • Z₀ x`. -/
theorem Z0_smul (a : ℝ) (x : EuclideanSpace ℝ ι) : Z0 (a • x) = a ^ 2 * Z0 x := by
  unfold Z0
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-! ### Trois lemmes généraux de calcul différentiel -/

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

/-! ### Régularité des observables -/

/-- Les coordonnées d'un espace euclidien sont différentiables (formes linéaires
continues). -/
theorem differentiable_coord (k : ι) :
    Differentiable ℝ (fun x : EuclideanSpace ℝ ι => x k) := by
  show Differentiable ℝ (fun x => (EuclideanSpace.proj (𝕜 := ℝ) k) x)
  exact (EuclideanSpace.proj (𝕜 := ℝ) k).differentiable

/-- ℓ₀ est différentiable : somme finie de carrés de formes linéaires continues. -/
theorem differentiable_loss0 (Q : Finset (ι × ι × ι × ι)) :
    Differentiable ℝ (loss0 Q) := by
  have hnorm : ∀ r : ℝ, ‖r‖ ^ 2 = r ^ 2 := fun r => by rw [Real.norm_eq_abs, sq_abs]
  unfold loss0
  simp only [hnorm]
  refine Differentiable.fun_sum fun q _ => ?_
  exact (((differentiable_coord q.1).add (differentiable_coord q.2.1)).sub
    ((differentiable_coord q.2.2.1).add (differentiable_coord q.2.2.2))).pow 2

/-- Z₀ est différentiable : c'est `∑ k, x k ^ 2`, somme finie de carrés de formes
linéaires continues. -/
theorem differentiable_Z0 : Differentiable ℝ (Z0 : EuclideanSpace ℝ ι → ℝ) := by
  have h : (Z0 : EuclideanSpace ℝ ι → ℝ) = fun x => ∑ k, x k * x k := by
    funext x
    unfold Z0
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    exact Finset.sum_congr rfl fun k _ => by
      rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, pow_two]
  rw [h]
  exact Differentiable.fun_sum fun k _ => (differentiable_coord k).mul (differentiable_coord k)

/-- ℓ_eff est différentiable en tout point où `Z₀ ≠ 0` (quotient de fonctions
différentiables à dénominateur non nul). -/
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

/-! ### Conservation de Z₀ le long du flot de ℓ_eff -/

/-- **Z₀ est conservée le long du flot de ℓ_eff.** Si `γ` suit `−∇(ℓ₀/Z₀)` et ne
traverse jamais `Z₀ = 0` (où ℓ_eff n'est pas définie), alors `t ↦ ‖γ t‖²` est
constante : la norme de la représentation ne peut ni s'effondrer ni diverger le long
de la dynamique effective. La preuve : la dérivée de `‖γ‖²` vaut `2⟪γ, γ'⟫`, et
`⟪γ', γ⟫ = −(ℓ_eff)' γ γ = 0` par le lemme d'Euler, ℓ_eff étant 0-homogène
(quotient de deux fonctions 2-homogènes). -/
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

/-! ### C le long des flots : conservation pour ℓ₀, terme résiduel pour ℓ_eff -/

/-- L'accouplement avec `1` redonne C : `⟪1, x⟫ = ∑ k, x k`. -/
theorem inner_onesVec (x : EuclideanSpace ℝ ι) : ⟪onesVec, x⟫_ℝ = Cmass x := by
  rw [PiLp.inner_apply]
  unfold Cmass onesVec
  simp [RCLike.inner_apply]

/-- La dérivée de `C ∘ γ` le long d'une trajectoire est l'accouplement de son champ
avec `1`. -/
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

/-- **C est conservée le long du flot de ℓ₀.** Si `γ` suit `−∇ℓ₀`, alors
`t ↦ ∑ k, γ t k` est constante : la translation étant une symétrie de ℓ₀, sa
différentielle tue la direction constante `1`, et `C` est l'accouplement avec cette
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

/-- **Le terme résiduel.** Le long du flot de ℓ_eff = ℓ₀/Z₀ (jamais `Z₀ = 0`), la
dérivée de C vaut exactement `2 ℓ₀ C / Z₀²`. L'Appendice F du papier obtient `dC/dt = 0`
en n'écrivant que le terme `−(1/Z₀) ∑_k ∂ℓ₀/∂E_k` de la règle du quotient ; le terme
`∂Z₀` manquant est précisément celui-ci, proportionnel à C.

Preuve : `C` est l'accouplement avec le vecteur constant `1`, donc
`(C ∘ γ)' t = ⟪1, γ' t⟫ = −(ℓ_eff)' (γ t) 1`. Le long de la droite `s ↦ γ t + s • 1`,
ℓ₀ est constante (translation-symétrie) et `Z₀` devient `Z₀ + 2 s • C + s² • ‖1‖²` :
la dérivée du quotient en `s = 0` vaut `−2 ℓ₀ C / Z₀²`, d'où le résultat. -/
theorem deriv_C_along_eff (Q : Finset (ι × ι × ι × ι)) {γ : ℝ → EuclideanSpace ℝ ι}
    {γ' : ℝ → EuclideanSpace ℝ ι}
    (hγ : ∀ t, HasDerivAt γ (γ' t) t)
    (hflow : ∀ t u, ⟪γ' t, u⟫_ℝ = -fderiv ℝ (effLoss Q) (γ t) u)
    (hZ0 : ∀ t, Z0 (γ t) ≠ 0) (t : ℝ) :
    HasDerivAt (fun s => Cmass (γ s))
      ((2 * loss0 Q (γ t) / Z0 (γ t) ^ 2) * Cmass (γ t)) t := by
  -- La dérivée de C ∘ γ est l'accouplement du champ avec 1, c.-à-d. −(ℓ_eff)' (γ t) 1 :
  have h1 : HasDerivAt (fun s => Cmass (γ s)) (⟪onesVec, γ' t⟫_ℝ) t := deriv_Cmass hγ t
  have h2 : ⟪onesVec, γ' t⟫_ℝ = -fderiv ℝ (effLoss Q) (γ t) onesVec := by
    rw [real_inner_comm]
    exact hflow t onesVec
  -- Forme fermée de ℓ_eff le long de la droite s ↦ γ t + s • 1 :
  have hnum : ∀ s : ℝ, loss0 Q (γ t + s • onesVec) = loss0 Q (γ t) := by
    intro s
    rw [smul_onesVec (ι := ι) s]
    exact loss0_translate Q (γ t) s
  have hx1 : ⟪onesVec, γ t⟫_ℝ = Cmass (γ t) := inner_onesVec (γ t)
  have hline : HasDerivAt (fun s : ℝ => γ t + s • onesVec) onesVec (0 : ℝ) :=
    hasDerivAt_line (γ t) onesVec
  -- le numérateur ℓ₀ est constant le long de la droite (translation-symétrie) :
  have hg1 : HasDerivAt (fun s : ℝ => loss0 Q (γ t + s • onesVec)) 0 (0 : ℝ) := by
    rw [funext hnum]
    exact hasDerivAt_const _ _
  -- le dénominateur Z₀ dérive vers 2 • C (‖x + s•1‖² = ‖x‖² + 2s⟪1,x⟫ + s²‖1‖²) :
  have hg2 : HasDerivAt (fun s : ℝ => Z0 (γ t + s • onesVec)) (2 * Cmass (γ t)) (0 : ℝ) := by
    have h := HasDerivAt.inner ℝ hline hline
    simp only [zero_smul, add_zero] at h
    rw [real_inner_comm onesVec (γ t), hx1, ← two_mul] at h
    rw [show (fun s : ℝ => Z0 (γ t + s • onesVec))
        = fun s => ⟪γ t + s • onesVec, γ t + s • onesVec⟫_ℝ from
      funext fun s => (real_inner_self_eq_norm_sq _).symm]
    exact h
  -- la composée elle-même, de dérivée (ℓ_eff)' (γ t) 1 :
  have hcomp : HasDerivAt (fun s => loss0 Q (γ t + s • onesVec) / Z0 (γ t + s • onesVec))
      (fderiv ℝ (effLoss Q) (γ t) onesVec) (0 : ℝ) := by
    have hf0 : HasFDerivAt (effLoss Q) (fderiv ℝ (effLoss Q) (γ t))
        ((fun s : ℝ => γ t + s • onesVec) 0) := by simpa using hasFDerivAt_effLoss Q (hZ0 t)
    have hc := hf0.comp_hasDerivAt (0 : ℝ) hline
    exact hc
  -- règle du quotient sur num/den le long de la droite :
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

/-- **L'hyperplan centré est invariant.** Si la représentation est centrée à
l'instant `0` (`C = 0`) et suit le flot de ℓ_eff, elle reste centrée pour tout temps.
C'est la forme exacte de la « conservation de C » du papier : vraie telle quelle pour
le flot de ℓ₀ seul, et pour ℓ_eff dans le régime normalisé (plongements centrés) où
C est nulle par construction. La dérivée de `C ∘ γ` étant proportionnelle à C
lui-même (`η' = κ η`), le facteur intégrant `exp(−∫κ)` montre que la solution issue
de zéro y reste. -/
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

end Grokking
