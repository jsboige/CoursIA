import Mathlib

/-!
# PacLearning.BernoulliMGF — borne analytique de la MGF de Bernoulli (brique 2c/3-hoeffding-2b/5)

Sous-module de `PacLearning` : **cœur analytique** de la concentration de Hoeffding.
La brique précédente (`MGF.lean`, PR #4525) a réduit algébriquement la MGF centrée à sa
forme fermée :

    E_D [ exp (t · (ind(x) − μ)) ] = μ · exp(t·(1−μ)) + (1−μ) · exp(−t·μ).

Cette brique (2b/5) borne cette forme fermée :

    μ · exp(t·(1−μ)) + (1−μ) · exp(−t·μ)  ≤  exp(t²/8)

pour `μ ∈ [0, 1]` et `t ∈ ℝ`. C'est le **lemme de Hoeffding** (forme Bernoulli) — le
résultat analytique dur requis pour clore la concentration. On établit ici les
**ingrédients prouvés** (variance de Bernoulli `≤ 1/4`, positivité, normalisation, et le
**cas symétrique `μ = 1/2`** via `cosh x ≤ exp(x²/2)`), et documente la borne générale
comme OPEN avec sa preuve variationnelle (Donsker–Varadhan + Pinsker).

## Pourquoi la borne générale est OPEN (honnête, G.3)

La borne `μ·exp(t(1−μ)) + (1−μ)·exp(−tμ) ≤ exp(t²/8)` est le vrai contenu analytique de
Hoeffding. Trois routes de preuve, toutes lourdes hors du cadre Measure de Mathlib :

1. **Second-deriv + Taylor** : `K(t) = ln(E[exp(t(ind−μ))])` satisfait `K(0) = K'(0) = 0`
   et `K''(t) ≤ 1/4` (variance de la Bernoulli **tiltée**). Alors `K(t) ≤ t²/8` via Taylor
   à reste intégral. Mathlib (`SubGaussian.lean:826`) suit cette voie mais via `cgf` +
   `tilted` + `variance_le_sq_of_bounded` (cadre Measure + ℝ≥0∞).
2. **Variationnelle (Donsker–Varadhan)** : `ln(p·e^a + (1−p)·e^b) = sup_q [q·a + (1−q)·b
   − D(q‖p)]` (KL). Avec `a = t(1−μ)`, `b = −tμ` : `K(t) = sup_q [t(q−μ) − D(q‖μ)]`.
   Pinsker `D(q‖μ) ≥ 2(q−μ)²` donne `K(t) ≤ sup_u [tu − 2u²] = t²/8`. Lemme de
   log-sum-exp variationnel absent de Mathlib hors `MeasureTheory/Measure/Tilted.lean`.
3. **Optimisation 2D** : `h(μ,t) = exp(t²/8) − MGF ≥ 0` par analyse du point critique
   (non trivial — le max de la MGF en `μ` n'est PAS en `1/2`).

Le **cas symétrique `μ = 1/2`** (cette brique) se ferme élégamment : la MGF devient
`cosh(t/2)` et `cosh x ≤ exp(x²/2)` (Mathlib `cosh_le_exp_half_sq`) donne
`cosh(t/2) ≤ exp((t/2)²/2) = exp(t²/8)`. La borne générale est laissée OPEN — c'est un
travail d'analyse dédié (cycle futur), pas un stub non prouvé.

## Briques Hoeffding (décomposition 5 sous-briques)

- 1/5 Chernoff-Markov (`chernoff_ineq`) — PR #4516
- 2a/5 MGF réduction algébrique (`expect_exp_centered_eq`) — PR #4525
- **2b/5 borne analytique** — Cette PR (ingrédients + cas symétrique prouvés, général OPEN) :
  - **2b/5-étape2 LIVRÉE** : cœur analytique de Hoeffding prouvé — dérivée du log-MGF
    `φ'(t) = q(t)` (moyenne tiltée), `q ∈ [0,1]`, et **2e dérivée `φ''(t) = q(t)(1−q(t)) ≤ 1/4`**
    (variance tiltée, via `bernoulli_var_le` inconditionnelle). C'est l'ingrédient exact
    de Hoeffding : la variance d'une v.a. bornée dans [0,1] est ≤ (plage/2)² = 1/4.
  - **2b/5-restant OPEN** : borne finale `MGF ≤ exp(t²/8)` depuis `φ''≤1/4` (pas Taylor/
    convexity : `K(t) = φ(t) − tμ` a `K(0)=K'(0)=0`, `K''≤1/4` ⟹ `K(t)≤t²/8`), nécessite
    le machinery `convexOn_univ_of_deriv2_nonneg` + `(deriv^[2] f)` qui timeout sur `simp`.
- 3/5 indépendance produit (MGF d'une somme = produit des MGF) — OPEN
- 4/5 optimisation `t = 4ε` — OPEN
- 5/5 concentration bilatérale — OPEN

Style **ℝ-weight pédagogique** (pas de `ℝ≥0∞` / `Measure`), cohérent avec `Data.lean`.
-/

namespace PacLearning

open Real

/-- **Borne de variance de Bernoulli** : pour tout `μ ∈ ℝ`, `μ · (1 − μ) ≤ 1/4`. C'est le
fait clé sous-jacent à Hoeffding : la variance d'une variable bornée dans `[0, 1]` est
majorée par le carré de la demi-plage `(1/2)²`. Preuve : `1/4 − μ(1−μ) = (μ − 1/2)² ≥ 0`
(complétion du carré — donc la borne est **inconditionnelle**, vraie pour tout `μ`,
même hors `[0, 1]` où `μ(1−μ) < 0`). Ingrédient exact de la borne `K''(t) ≤ 1/4`
(route 1 ci-dessus). -/
theorem bernoulli_var_le (μ : ℝ) :
    μ * (1 - μ) ≤ 1 / 4 := by
  have h : 1 / 4 - μ * (1 - μ) = (μ - 1 / 2) ^ 2 := by ring
  linarith [sq_nonneg (μ - 1 / 2)]

/-- **Normalisation** : la MGF centrée vaut `1` en `t = 0` (l'exponentielle de `0` est
`1`, et `μ + (1 − μ) = 1`). C'est `K(0) = ln(1) = 0`, point d'ancrage de la route Taylor. -/
theorem bernoulli_mgf_zero (μ : ℝ) :
    μ * Real.exp (0 * (1 - μ)) + (1 - μ) * Real.exp (-(0 * μ)) = 1 := by
  simp only [zero_mul, Real.exp_zero, neg_zero]
  ring

/-- **Positivité (cas intérieur)** : pour `0 < μ < 1`, la MGF centrée est strictement
positive (somme de deux termes strictement positifs : poids `> 0` fois `exp > 0`). -/
theorem bernoulli_mgf_pos (μ t : ℝ) (hμ : 0 < μ) (hμ' : μ < 1) :
    0 < μ * Real.exp (t * (1 - μ)) + (1 - μ) * Real.exp (-(t * μ)) := by
  apply add_pos
  · exact mul_pos hμ (Real.exp_pos _)
  · exact mul_pos (by linarith) (Real.exp_pos _)

/-- **Borne de Hoeffding — cas symétrique `μ = 1/2`** : la MGF centrée en `μ = 1/2`
se réduit à `cosh(t/2)`, et le lemme de Mathlib `cosh x ≤ exp(x²/2)` donne la borne
`cosh(t/2) ≤ exp((t/2)²/2) = exp(t²/8)`.

C'est le seul cas où la borne générale se ferme élégamment (la MGF est symétrique en `t`,
le max en `μ` est atteint en `1/2`). La borne générale `μ·exp(t(1−μ)) + (1−μ)·exp(−tμ)
≤ exp(t²/8)` pour `μ ∈ [0,1]` arbitraire est documentée OPEN (voir docstring module) :
elle requiert la route variationnelle (Pinsker) ou la seconde-dérivée (cgf tilté), lourdes
hors du cadre Measure. -/
theorem bernoulli_mgf_half_le (t : ℝ) :
    (1 : ℝ) / 2 * Real.exp (t * ((1 : ℝ) / 2)) + (1 : ℝ) / 2 * Real.exp (-(t * ((1 : ℝ) / 2))) ≤
      Real.exp (t ^ 2 / 8) := by
  have hcosh : (1 : ℝ) / 2 * Real.exp (t * ((1 : ℝ) / 2)) + (1 : ℝ) / 2 * Real.exp (-(t * ((1 : ℝ) / 2))) =
      Real.cosh (t / 2) := by
    rw [Real.cosh_eq (t / 2)]
    field_simp
  rw [hcosh]
  have hle := Real.cosh_le_exp_half_sq (t / 2)
  rw [show (t / 2) ^ 2 / 2 = t ^ 2 / 8 from by ring] at hle
  exact hle

/-! ## Brique 2b/5-étape2 — dérivée du log-MGF (moyenne tiltée) et borne analytique

Ingrédient analytique de la borne générale `bernoulli_mgf_le` (encore OPEN). On
établit la structure dérivée du **log-MGF non-centré** `φ(t) = log((1−μ) + μ·exp t)` :

  φ'(t) = q(t) := μ·exp t / ((1−μ) + μ·exp t)   (« moyenne tiltée », ∈ [0,1] pour μ ∈ [0,1])
  φ''(t) = q(t)·(1 − q(t)) ≤ 1/4                 (« variance tiltée », ingrédient exact de Hoeffding)

La borne `φ'' ≤ 1/4` est le **cœur analytique** de Hoeffding (toute la difficulté de la
concentration réside là : la variance d'une v.a. bornée dans [0,1] est ≤ (plage/2)² = 1/4).
La borne finale `MGF ≤ exp(t²/8)` suit par convexité/Taylor (K(t) := φ(t) − tμ a K(0)=K'(0)=0
et K'' = φ'' ≤ 1/4 ⟹ K(t) ≤ t²/8) — étape documentée OPEN (reste le pas Taylor/convexité).
-/

/-- **Positivité du dénominateur du log-MGF** : pour `μ ∈ [0,1]` et tout `t`,
    `(1−μ) + μ·exp t > 0`. En effet, c'est une somme pondérée (`μ` et `1−μ`) de termes
    `≥ 0` dont au moins un est strictement `> 0` (cas `μ < 1` : `1−μ > 0` ; cas `μ = 1` :
    `μ·exp t = exp t > 0`). C'est la condition de domaine du log-MGF. -/
theorem bernoulli_logmgf_denom_pos (μ t : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    0 < (1 - μ) + μ * Real.exp t := by
  have h1mu : 0 ≤ 1 - μ := sub_nonneg.mpr hμ2
  have hmexp : 0 ≤ μ * Real.exp t := mul_nonneg hμ (le_of_lt (Real.exp_pos t))
  by_cases hμ1 : μ = 1
  · -- μ = 1 : (1−μ) = 0, donc somme = 0 + exp t = exp t > 0.
    subst hμ1; simp [Real.exp_pos]
  · -- μ < 1 : (1−μ) > 0, donc somme = (terme ≥ 0) + (terme > 0) > 0.
    have h1mu_pos : 0 < 1 - μ := lt_of_le_of_ne h1mu (fun heq => hμ1 (by linarith))
    linarith

/-- **Dérivée du log-MGF de Bernoulli** : pour `μ ∈ [0,1]` et le log-MGF non-centré
    `φ(t) = log((1−μ) + μ·exp t)`, la dérivée est la « moyenne tiltée »
    `q(t) = μ·exp t / ((1−μ) + μ·exp t)`. Preuve : `HasDerivAt.log` (chaîne sur `log`)
    + `hasDerivAt_exp` + `const_mul` + `const_add`, le dénominateur étant `≠ 0`
    via `bernoulli_logmgf_denom_pos`. -/
theorem bernoulli_logmgf_deriv (μ t : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    deriv (fun s => Real.log ((1 - μ) + μ * Real.exp s)) t =
      μ * Real.exp t / ((1 - μ) + μ * Real.exp t) := by
  apply HasDerivAt.deriv
  apply HasDerivAt.log
  · exact HasDerivAt.const_add _ (HasDerivAt.const_mul _ (hasDerivAt_exp t))
  · exact ne_of_gt (bernoulli_logmgf_denom_pos μ t hμ hμ2)

/-- **La moyenne tiltée est dans [0,1]** : pour `μ ∈ [0,1]`, `q(t) = μ·exp t/((1−μ)+μ·exp t)
    ∈ [0,1]`. C'est la « probabilité a posteriori » que `ind = 1` sous la loi tiltée de
    paramètre `t` — toujours une probabilité valide. -/
theorem bernoulli_tilted_mean_mem_Icc (μ t : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    μ * Real.exp t / ((1 - μ) + μ * Real.exp t) ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Set.mem_Icc]
  have hDpos : 0 < (1 - μ) + μ * Real.exp t := bernoulli_logmgf_denom_pos μ t hμ hμ2
  refine ⟨?_, ?_⟩
  · -- 0 ≤ μ·exp t / D  (numérateur ≥ 0, dénominateur > 0).
    exact div_nonneg (mul_nonneg hμ (le_of_lt (Real.exp_pos t))) (le_of_lt hDpos)
  · -- μ·exp t / D ≤ 1  ⟺  μ·exp t ≤ (1−μ) + μ·exp t  ⟺  0 ≤ (1−μ)  (vrai car μ ≤ 1).
    rw [div_le_iff₀ hDpos, one_mul]
    exact le_add_of_nonneg_left (sub_nonneg.mpr hμ2)

/-- **Dérivée de la moyenne tiltée (= 2e dérivée du log-MGF)** : pour `q(t) =
    μ·exp t/((1−μ)+μ·exp t)` (la moyenne tiltée, = `φ'`), on a `q'(t) = q(t)·(1−q(t))`
    (« variance tiltée »). C'est la 2e dérivée `φ''(t)` du log-MGF non-centré. Preuve :
    règle du quotient `HasDerivAt.div` sur `num = μ·exp t` (numérateur) et `D = (1−μ)+μ·exp t`
    (dénominateur, tous deux de dérivée `μ·exp t`), puis fermeture algébrique
    (`field_simp` + `ring`) : la forme quotient `μ·exp t·(D − μ·exp t)/D²` se réduit à
    `q(t)·(1−q(t))` car `D − μ·exp t = 1−μ`. -/
theorem bernoulli_tilted_mean_deriv (μ t : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    deriv (fun s => μ * Real.exp s / ((1 - μ) + μ * Real.exp s)) t =
      μ * Real.exp t / ((1 - μ) + μ * Real.exp t) *
        (1 - μ * Real.exp t / ((1 - μ) + μ * Real.exp t)) := by
  have hDpos : 0 < (1 - μ) + μ * Real.exp t := bernoulli_logmgf_denom_pos μ t hμ hμ2
  have hDne : (1 - μ) + μ * Real.exp t ≠ 0 := ne_of_gt hDpos
  have hnum : HasDerivAt (fun s => μ * Real.exp s) (μ * Real.exp t) t :=
    HasDerivAt.const_mul μ (hasDerivAt_exp t)
  have hD : HasDerivAt (fun s => (1 - μ) + μ * Real.exp s) (μ * Real.exp t) t :=
    HasDerivAt.const_add _ (HasDerivAt.const_mul _ (hasDerivAt_exp t))
  have hdiv : HasDerivAt (fun s => μ * Real.exp s / ((1 - μ) + μ * Real.exp s))
      ((μ * Real.exp t * ((1 - μ) + μ * Real.exp t) - μ * Real.exp t * (μ * Real.exp t)) /
        ((1 - μ) + μ * Real.exp t) ^ 2) t :=
    HasDerivAt.div hnum hD hDne
  rw [HasDerivAt.deriv hdiv]
  field_simp

/-- **La variance tiltée est ≤ 1/4 (= borne de Hoeffding)** : la 2e dérivée du log-MGF
    non-centré `φ''(t) = q(t)·(1−q(t))` satisfait `≤ 1/4` — le **cœur analytique** de
    Hoeffding. La borne `x·(1−x) ≤ 1/4` est **inconditionnelle** (vraie ∀ `x ∈ ℝ`, via la
    complétion du carré `(x − 1/2)² ≥ 0`), donc s'applique à `x = q(t)` sans hypothèse de
    domaine. C'est l'ingrédient exact qui, combiné à Taylor/convexité (`K(t) = φ(t) − tμ`
    avec `K(0) = K'(0) = 0`), donne la borne finale `MGF ≤ exp(t²/8)` (étape OPEN). -/
theorem bernoulli_logmgf_second_deriv_le (μ t : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    deriv (fun s => μ * Real.exp s / ((1 - μ) + μ * Real.exp s)) t ≤ 1 / 4 := by
  rw [bernoulli_tilted_mean_deriv μ t hμ hμ2]
  exact bernoulli_var_le _

end PacLearning
