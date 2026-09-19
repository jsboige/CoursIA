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

Le lien exact avec les Eq. (25)-(27) du papier (flot `dE/dt = −∂(ℓ₀/Z₀)/∂E`)
est documenté dans les docstrings : les deux identités ci-dessus sont les
cœurs algébriques — la partie « règle de chaîne le long d'une courbe intégrale »
est standard et reportée à une tranche suivante.

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

end LearningTheory.EffectiveTheory
