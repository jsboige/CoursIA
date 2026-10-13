import Mathlib

/-!
# Grokking — théorie effective R02 : parallélogrammes et lois de conservation

Tranche **R02** de l'arc « théorie effective » (#16741, issue #16752) :
*Liu et al., Towards Understanding Grokking — An Effective Theory of
Representation Learning* (arXiv:2205.10343, 2022 ; PDF GDrive sha8 `88CE88DB`).

Contenu formalisé (énoncés courts, preuves constructives — le terrain le plus
propre du corpus selon l'issue) :

1. **Définition 1 (δ-parallélogramme)** — `IsDeltaParallelogram` : un quadruplet
   d'embeddings `(i, j, m, n)` forme un parallélogramme à δ près lorsque
   `‖E i + E j − (E m + E n)‖ ≤ δ`. Les dérivations du papier prennent δ = 0
   (version égalité `parallelogram`).
2. **Proposition 1** — `prop1_zeroLoss` : à perte d'entraînement nulle et
   étiquettes distinctes, tout parallélogramme `(i,j,m,n)` vérifie
   `i + j = m + n`. Preuve par contradiction exactement comme au papier :
   `Y_{i+j} = Dec(E i + E j) = Dec(E m + E n) = Y_{m+n}`, puis l'injectivité
   des étiquettes conclut.
3. **Proposition 2** — `prop2_injectiveDecoder` : à perte nulle avec décodeur
   injectif, deux échantillons d'entraînement de même somme forcent un
   parallélogramramme `E i + E j = E m + E n` — le mécanisme de *formation*
   des parallélogrammes.
4. **Appendice F, lois de conservation** — le cœur calculatoire des Eq. (26)-(27)
   du papier, pour des embeddings scalaires `E : Fin p → ℝ` (le papier se place
   à `din = 1` sans perte de généralité) :
   - `loss0_grad_sum_zero` : la somme des composantes du gradient de `ℓ₀`
     est nulle (chaque contrainte de parallélogramme contribue
     `δ_ik + δ_jk − δ_mk − δ_nk`, de somme nulle) — c'est l'identité qui fait
     dériver `C = Σ E k` constant le long du flot (Eq. 27) ;
   - `loss0_grad_dot_self` : l'identité d'Euler `Σ_k (∂ℓ₀/∂E_k) · E k = 2 ℓ₀`
     (fonction quadratique homogène de degré 2) — c'est elle qui fait dériver
     `Z₀ = Σ E k²` constant le long du flot normalisé (Eq. 26).

5. **Flot effectif et lois de conservation (App F complet)** — la règle de
   chaîne le long d'une courbe intégrale `γ` du flot `dE/dt = −∂(ℓ₀/Z₀)/∂E`
   (Eq. 23, forme développée Eq. 25) :
   - `flow_deriv_sumsq0_eq_zero` / `flow_sumsq0_constant` : **`Z₀` est
     conservé inconditionnellement** (Eq. 26) — le terme en `∇ℓ₀` se ferme
     par l'identité d'Euler, le terme en `∇Z₀` par `Σ E k² = Z₀` ;
   - `flow_deriv_sum_apply` : **audit de l'Eq. 27** — la règle de chaîne
     complète donne `dC/dt = (2 ℓ₀/Z₀²) · C` : le terme
     `(ℓ₀/Z₀²) · Σ ∂Z₀/∂E_k` omis par la dérivation imprimée du papier
     n'est nul que sur le régime à perte nulle ;
   - `flow_sum_constant_of_zero_loss` : sur ce régime (l'état
     post-grokking, là où vit l'analyse effective), `C = Σ E k` est
     conservé exactement.

Dépendances : Mathlib uniquement (`HasFDerivAt`, `ContinuousLinearMap.proj`,
`HasFDerivAt.sum`, `hasDerivAt_pow.comp_hasFDerivAt`). Aucun couplage aux
modules frères du lake.
-/

namespace LearningTheory.EffectiveTheory

section Parallelograms

variable {p : ℕ} {V : Type*} [NormedAddCommGroup V] {Y : Type*}

/-- **Définition 1 (R02)** : le quadruplet de paires `(q, r)` (paires
d'indices d'entraînement) forme un δ-parallélogramme dans la représentation
`E` si `‖E q.1 + E q.2 − (E r.1 + E r.2)‖ ≤ δ`. -/
def IsDeltaParallelogram (E : Fin p → V) (δ : ℝ) (q r : Fin p × Fin p) : Prop :=
  ‖E q.1 + E q.2 - (E r.1 + E r.2)‖ ≤ δ

/-- Version δ = 0 utilisée dans les dérivations du papier : le
parallélogramme exact `E i + E j = E m + E n`. -/
theorem parallelogram_iff_eq (E : Fin p → V) (q r : Fin p × Fin p) :
    IsDeltaParallelogram E 0 q r ↔ E q.1 + E q.2 = E r.1 + E r.2 := by
  simp [IsDeltaParallelogram, sub_eq_zero]

/-- **Proposition 1 (R02)** : à perte d'entraînement nulle (chaque paire
d'entraînement `(i, j)` satisfait `Dec (E i + E j) = Y (i + j)`) et étiquettes
distinctes (`Y` injective), tout parallélogramme `(q, r)` du jeu
d'entraînement vérifie `q.1 + q.2 = r.1 + r.2`.

C'est la contraposée pédagogique du grokking : une représentation qui
généralise (beaucoup de parallélogrammes) doit respecter l'arithmétique
sous-jacente. -/
theorem prop1_zeroLoss (E : Fin p → V) (dec : V → Y) (label : ℕ → Y)
    (hLabel : Function.Injective label)
    (D : Finset (Fin p × Fin p))
    (hZeroLoss : ∀ q ∈ D, dec (E q.1 + E q.2) = label ((q.1 : ℕ) + q.2))
    {q r : Fin p × Fin p} (hq : q ∈ D) (hr : r ∈ D)
    (hPara : E q.1 + E q.2 = E r.1 + E r.2) :
    (q.1 : ℕ) + q.2 = (r.1 : ℕ) + r.2 := by
  refine hLabel ?_
  rw [← hZeroLoss q hq, ← hZeroLoss r hr, hPara]

/-- **Proposition 2 (R02)** : à perte nulle avec décodeur injectif, deux
échantillons d'entraînement `(q, r)` de même somme `q.1 + q.2 = r.1 + r.2`
forcent le parallélogramme exact `E q.1 + E q.2 = E r.1 + E r.2`.

C'est le mécanisme de *formation* : l'injectivité du décodeur empêche deux
représentations différentes de coder la même étiquette. -/
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

/-- Forme linéaire d'un quadruplet de parallélogramme :
`linQ t E = E i + E j − (E m + E n)` pour `t = ((i, j), (m, n))`. -/
private def linQ (t : (Fin p × Fin p) × (Fin p × Fin p)) :
    (Fin p → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj t.1.1 : (Fin p → ℝ) →L[ℝ] ℝ)
    + (ContinuousLinearMap.proj t.1.2 : (Fin p → ℝ) →L[ℝ] ℝ)
    - (ContinuousLinearMap.proj t.2.1 : (Fin p → ℝ) →L[ℝ] ℝ)
    - (ContinuousLinearMap.proj t.2.2 : (Fin p → ℝ) →L[ℝ] ℝ)

/-- Évaluation explicite de la forme linéaire (évite `map_sum`/`map_smul` sur
le CLM, dont l'élaboration traverse un diamant d'instances coûteux). -/
private theorem linQ_apply (t : (Fin p × Fin p) × (Fin p × Fin p))
    (v : Fin p → ℝ) :
    linQ t v = v t.1.1 + v t.1.2 - (v t.2.1 + v t.2.2) := by
  simp only [linQ, add_apply, sub_apply, ContinuousLinearMap.proj_apply]
  ring

/-- Perte effective quadratique `ℓ₀` (Eq. 5 et 24 du papier) : moyenne omise
des carrés des résidus de parallélogramme sur l'ensemble `P` des quadruplets
admissibles (les constantes multiplicatives positives ne changent ni le
signe du gradient ni les identités de conservation). -/
noncomputable def loss0 (P : Finset ((Fin p × Fin p) × (Fin p × Fin p)))
    (E : Fin p → ℝ) : ℝ :=
  ∑ t ∈ P, (linQ t E) ^ 2

/-- Norme d'énergie `Z₀ = Σ_k (E k)²` (Eq. 5 et 24 du papier) : la seconde
quantité conservée, celle qui interdit l'effondrement à zéro de la
représentation. -/
noncomputable def sumsq0 (E : Fin p → ℝ) : ℝ :=
  ∑ k, (E k) ^ 2

/-- Projection `E ↦ E k` encapsulée dans un def : fixe une fois pour toutes
le profil d'instances du CLM (même pattern que `linQ`). -/
private def projCLM (k : Fin p) : (Fin p → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj k : (Fin p → ℝ) →L[ℝ] ℝ)

private theorem hasFDerivAt_loss0_term
    (t : (Fin p × Fin p) × (Fin p × Fin p)) (E : Fin p → ℝ) :
    HasFDerivAt (fun F : Fin p → ℝ => (linQ t F) ^ 2) ((2 * linQ t E) • linQ t) E := by
  simpa only [Function.comp_def, show (2 : ℕ) - 1 = 1 from rfl, pow_one,
    show ((2 : ℕ) : ℝ) = 2 from rfl] using
    HasDerivAt.comp_hasFDerivAt E (hasDerivAt_pow 2 (linQ t E)) (linQ t).hasFDerivAt

/-- Dérivée de `ℓ₀` : `fderiv ℝ (loss0 P) E = Σ_t (2 · linQ t E) • linQ t`. -/
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

/-- Dérivée de `Z₀` : `fderiv ℝ sumsq0 E = Σ_k (2 · E k) • proj k`. -/
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

/-- Reconstruction : la famille des vecteurs de base `Pi.single k 1` décompose
tout `E` (identité utilisée par la chasse aux Kronecker de l'appendice F). -/
private theorem sum_smul_piSingle_self (E : Fin p → ℝ) :
    ∑ k, E k • (Pi.single k (1 : ℝ) : Fin p → ℝ) = E := by
  funext i
  simp [Finset.sum_apply, Pi.single_apply, mul_ite]

/-- **Appendice F, Eq. (27) — identité 1** : la somme des composantes du
gradient de `ℓ₀` est nulle :
`Σ_k (fderiv ℓ₀ E) (e_k) = 0`.

Chaque quadruplet `t` contribue `δ_{t.1.1 k} + δ_{t.1.2 k} − δ_{t.2.1 k}
− δ_{t.2.2 k}` à la composante `k`, de somme sur `k` exactement nulle. C'est
le cœur algébrique qui fait de `C = Σ_k E k` une quantité conservée le long
du flot effectif (Eq. 27 : `dC/dt = −(1/Z₀) Σ_k ∂ℓ₀/∂E_k = 0`). -/
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

/-- **Appendice F, Eq. (26) — identité 2 (Euler)** : l'identité d'homogénéité
de la perte quadratique :
`Σ_k (fderiv ℓ₀ E) (e_k) * E k = 2 * ℓ₀ E`.

C'est le cœur algébrique de la conservation de `Z₀ = Σ_k E k²` le long du flot
normalisé `dE/dt = −∂(ℓ₀/Z₀)/∂E` (Eq. 25-26 du papier, qui substitue
exactement `Σ_k (∂ℓ₀/∂E_k) · E k = 2 ℓ₀` pour conclure `dZ₀/dt = 0`). -/
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

/-- Composante d'une courbe dérivable : si `γ` a la vitesse `v` en `t`,
chaque composante `s ↦ γ s k` a la vitesse `v k`. -/
private theorem hasDerivAt_component (γ : ℝ → (Fin p → ℝ)) (k : Fin p) (t : ℝ)
    {v : Fin p → ℝ} (h : HasDerivAt γ v t) : HasDerivAt (fun s => γ s k) (v k) t := by
  have hc := ((projCLM k).hasFDerivAt.comp t h).hasDerivAt
  have h₁ : Filter.EventuallyEq (nhds t) (fun s => γ s k) (↑(projCLM k) ∘ γ) :=
    Filter.Eventually.of_forall fun s => (projCLM_apply k (γ s)).symm
  exact (hc.congr_of_eventuallyEq h₁).congr_deriv (by simp [projCLM_apply])

/-- Somme des composantes : si `γ` a la vitesse `v` en `t`, la somme
`s ↦ Σ_k γ s k` a la vitesse `Σ_k v k`. -/
private theorem hasDerivAt_sumC {γ : ℝ → (Fin p → ℝ)} (t : ℝ) {v : Fin p → ℝ}
    (hv : HasDerivAt γ v t) : HasDerivAt (fun s => ∑ k, γ s k) (∑ k, v k) t := by
  have h := HasDerivAt.sum (u := (Finset.univ : Finset (Fin p)))
    fun k _ => hasDerivAt_component γ k t hv
  have heq : (∑ k : Fin p, fun s => γ s k) = (fun s => ∑ k, γ s k) :=
    funext fun s_ => Finset.sum_apply s_ Finset.univ fun k => fun s => γ s k
  rw [heq] at h
  exact h

/-- Énergie : si `γ` a la vitesse `v` en `t`, la trajectoire d'énergie
`s ↦ Z₀ (γ s)` a la vitesse `Σ_k 2 E_k v_k`. -/
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

/-- **Gradient de `ℓ₀`** (Eq. 25 du papier) : la composante `k` du vecteur
gradient est `∂ℓ₀/∂E_k := fderiv ℝ (loss0 P) E (e_k)`. -/
noncomputable def gradLoss0 (P : Finset ((Fin p × Fin p) × (Fin p × Fin p)))
    (E : Fin p → ℝ) : Fin p → ℝ :=
  fun k => fderiv ℝ (loss0 P) E (Pi.single k (1 : ℝ))

/-- **Gradient de `Z₀`** : composante `k` = `∂Z₀/∂E_k`. -/
noncomputable def gradSumSq0 (E : Fin p → ℝ) : Fin p → ℝ :=
  fun k => fderiv ℝ sumsq0 E (Pi.single k (1 : ℝ))

/-- Le gradient de `Z₀ = Σ E k²` est `2 • E`. -/
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

/-- **Flot effectif (Eq. 23, forme développée Eq. 25)** : une courbe
d'embeddings `γ` suit la descente de gradient de `ℓ_eff = ℓ₀/Z₀` lorsque sa
vitesse en `t` vaut `−(1/Z₀) • ∇ℓ₀ + (ℓ₀/Z₀²) • ∇Z₀`, gradients évalués
en `γ t` (règle du quotient appliquée à `∂(ℓ₀/Z₀)/∂E`). -/
def IsEffectiveFlow (P : Finset ((Fin p × Fin p) × (Fin p × Fin p)))
    (γ : ℝ → (Fin p → ℝ)) : Prop :=
  ∀ t, HasDerivAt γ
    (-(sumsq0 (γ t))⁻¹ • gradLoss0 P (γ t)
      + (loss0 P (γ t) / (sumsq0 (γ t)) ^ 2) • gradSumSq0 (γ t)) t

/-- Composante de la vitesse du flot (Eq. 25) :
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

/-- **Eq. 26 — `Z₀` est conservé le long du flot effectif** :
`d/dt (Σ_k E_k(t)²) = 0`, inconditionnellement. La règle de chaîne donne
`dZ₀/dt = Σ_k 2 E_k · Ė_k` ; substituer la vitesse (Eq. 25) fait apparaître
exactement les deux identités de gradient : le terme en `∇ℓ₀` se ferme par
l'identité d'Euler (`loss0_grad_dot_self`), le terme en `∇Z₀` par
`Σ E k² = Z₀`. C'est la conservation qui interdit à la représentation de
s'effondrer en zéro. -/
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

/-- **Eq. 27 auditée — la somme `C = Σ E_k` n'est conservée que sur le
régime à perte nulle.** La règle de chaîne appliquée à la vitesse complète
(Eq. 25) donne `dC/dt = −(1/Z₀) Σ_k ∂ℓ₀/∂E_k + (ℓ₀/Z₀²) · 2 C`. La
dérivation imprimée en Eq. 27 du papier ne garde que le premier terme et
conclut `dC/dt = 0` via `Σ_k ∂ℓ₀/∂E_k = 0` — le second terme
`(2 ℓ₀/Z₀²) · C` n'est nul que si `ℓ₀ = 0` le long de la trajectoire
(l'état post-grokking, là où vit l'analyse effective) ou si `C = 0`
(repère translaté). Le théorème ci-dessous formalise la dynamique exacte ;
la conservation inconditionnelle de `C` n'est PAS un théorème du flot. -/
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

/-- **Corollaire Eq. 26** : `Z₀` est constant le long de toute courbe
intégrale du flot effectif — la norme d'énergie de la représentation ne
décroît jamais, ce qui interdit l'effondrement en zéro. -/
theorem flow_sumsq0_constant (P : Finset ((Fin p × Fin p) × (Fin p × Fin p)))
    {γ : ℝ → (Fin p → ℝ)} (hγ : IsEffectiveFlow P γ) (s t : ℝ) :
    sumsq0 (γ s) = sumsq0 (γ t) :=
  constant_of_deriv_zero (fun u => (hasDerivAt_sumsq0_comp u (hγ u)).differentiableAt)
    (flow_deriv_sumsq0_eq_zero P hγ) s t

/-- **Corollaire Eq. 27 (régime à perte nulle)** : si la trajectoire reste
dans la variété `ℓ₀ = 0` (l'état post-grokking, contexte effectif du
papier), alors `C = Σ E_k` y est conservé exactement. -/
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
