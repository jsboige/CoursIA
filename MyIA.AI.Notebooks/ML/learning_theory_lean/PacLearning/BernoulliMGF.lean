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


/-! ## Brique 2b/5-finale — borne MGF générale `bernoulli_mgf_le`

La borne finale de Hoeffding (forme Bernoulli) : pour `μ ∈ [0, 1]` et `t ∈ ℝ`,

    μ · exp(t · (1 − μ)) + (1 − μ) · exp(−(t · μ))  ≤  exp(t² / 8).

C'est le **lemme de Hoeffding** complet. La preuve contourne le machinery lourd
`convexOn_univ_of_deriv2_nonneg` + `deriv^[2]` (qui timeout sur `simp`) en passant par la
**monotonie de la dérivée** : on pose le log-MGF centré `K(t) = log((1−μ) + μ·exp t) − t·μ`
(de sorte que `MGF = exp(K)`), et le gap `g(t) = t²/8 − K(t)`. On montre `g ≥ 0` via :

1. la dérivée `g'(t) = t/4 − (q(t) − μ)` (notée `g₁`) est **monotone croissante globale**
   (`g₁'(t) = 1/4 − q(t)·(1−q(t)) ≥ 0` par `bernoulli_var_le`) ;
2. `g₁(0) = 0`, donc `g₁(t) ≥ 0` pour `t ≥ 0` (et `≤ 0` pour `t ≤ 0`) ;
3. sur `Set.Ici 0`, `g' = g₁ ≥ 0` ⟹ `g` monotone croissante ⟹ `g(t) ≥ g(0) = 0` ;
4. sur `Set.Iic 0`, `g' ≤ 0` ⟹ `g` monotone décroissante ⟹ `g(t) ≥ g(0) = 0` ;
5. `g(t) ≥ 0` ⟹ `t²/8 ≥ K(t)` ⟹ (exponentielle croissante) `exp(t²/8) ≥ exp(K(t)) = MGF`.

La monotonie s'établit via `monotone_of_hasDerivAt_nonneg` / `monotoneOn_of_deriv_nonneg`
(HasDerivAt pointwise, **aucun `deriv^[2]`**, aucun `Differentiable ℝ` global à synthétiser).
-/

/-- La « moyenne tiltée » `q(t) = μ·exp t / ((1−μ) + μ·exp t)`, exposée pour réutilisation.
C'est `φ'(t)` (dérivée du log-MGF non-centré) et l'argument de `bernoulli_var_le` donnant
`φ''(t) ≤ 1/4`. -/
noncomputable def bernoulliTiltedMean (μ t : ℝ) : ℝ := μ * Real.exp t / ((1 - μ) + μ * Real.exp t)

/-- `g₁ μ t = t/4 − (q(t) − μ)` : la dérivée du gap `g μ`. -/
noncomputable def bernoulliMGFDeriv (μ t : ℝ) : ℝ := t / 4 - (bernoulliTiltedMean μ t - μ)

/-- Le gap `g μ t = t²/8 − K(t)` où `K(t) = log((1−μ)+μ·exp t) − t·μ` est le log-MGF centré.
Prouver `g μ t ≥ 0` ⟹ `MGF ≤ exp(t²/8)`. -/
noncomputable def bernoulliMGFGap (μ t : ℝ) : ℝ := t^2 / 8 - (Real.log ((1 - μ) + μ * Real.exp t) - t * μ)

/-- `HasDerivAt` de la moyenne tiltée : `q'(t) = q(t)·(1 − q(t))` (variance tiltée). -/
theorem bernoulliTiltedMean_hasDerivAt (μ t : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    HasDerivAt (bernoulliTiltedMean μ)
      (bernoulliTiltedMean μ t * (1 - bernoulliTiltedMean μ t)) t := by
  have hDpos : 0 < (1 - μ) + μ * Real.exp t := bernoulli_logmgf_denom_pos μ t hμ hμ2
  have hDne : (1 - μ) + μ * Real.exp t ≠ 0 := ne_of_gt hDpos
  have hnum : HasDerivAt (fun s => μ * Real.exp s) (μ * Real.exp t) t :=
    HasDerivAt.const_mul μ (hasDerivAt_exp t)
  have hdenom : HasDerivAt (fun s => (1 - μ) + μ * Real.exp s) (μ * Real.exp t) t :=
    HasDerivAt.const_add _ (HasDerivAt.const_mul _ (hasDerivAt_exp t))
  have hdiv : HasDerivAt (fun s => μ * Real.exp s / ((1 - μ) + μ * Real.exp s))
      ((μ * Real.exp t * ((1 - μ) + μ * Real.exp t) - μ * Real.exp t * (μ * Real.exp t)) /
        ((1 - μ) + μ * Real.exp t) ^ 2) t :=
    HasDerivAt.div hnum hdenom hDne
  have hfun : (fun s => μ * Real.exp s / ((1 - μ) + μ * Real.exp s)) = bernoulliTiltedMean μ := by
    funext s; rfl
  rw [hfun] at hdiv
  have heq : bernoulliTiltedMean μ t * (1 - bernoulliTiltedMean μ t) =
      (μ * Real.exp t * ((1 - μ) + μ * Real.exp t) - μ * Real.exp t * (μ * Real.exp t)) /
        ((1 - μ) + μ * Real.exp t) ^ 2 := by
    simp only [bernoulliTiltedMean]
    field_simp
  rw [heq]
  exact hdiv

/-- `HasDerivAt` du log-MGF non-centré `φ(t) = log((1−μ)+μ·exp t)` : `φ'(t) = q(t)`. -/
theorem bernoulli_logmgf_hasDerivAt (μ t : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    HasDerivAt (fun s => Real.log ((1 - μ) + μ * Real.exp s)) (bernoulliTiltedMean μ t) t := by
  have hDpos : 0 < (1 - μ) + μ * Real.exp t := bernoulli_logmgf_denom_pos μ t hμ hμ2
  have hDne : (1 - μ) + μ * Real.exp t ≠ 0 := ne_of_gt hDpos
  have hinner : HasDerivAt (fun s => (1 - μ) + μ * Real.exp s) (μ * Real.exp t) t :=
    HasDerivAt.const_add _ (HasDerivAt.const_mul _ (hasDerivAt_exp t))
  have hlog : HasDerivAt (fun s => Real.log ((1 - μ) + μ * Real.exp s))
      ((μ * Real.exp t) / ((1 - μ) + μ * Real.exp t)) t :=
    HasDerivAt.log hinner hDne
  simpa [bernoulliTiltedMean] using hlog

/-- `HasDerivAt` du gap `g` : `g'(t) = g₁(t) = t/4 − (q(t) − μ)`. -/
theorem bernoulliMGFGap_hasDerivAt (μ t : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    HasDerivAt (bernoulliMGFGap μ) (bernoulliMGFDeriv μ t) t := by
  have hlog : HasDerivAt (fun s : ℝ => Real.log ((1 - μ) + μ * Real.exp s))
      (bernoulliTiltedMean μ t) t := bernoulli_logmgf_hasDerivAt μ t hμ hμ2
  have hsq8 : HasDerivAt (fun s : ℝ => s ^ 2 / 8) (2 * t / 8) t := by
    have h := HasDerivAt.div (hasDerivAt_pow 2 t) (hasDerivAt_const t 8) (by norm_num : (8 : ℝ) ≠ 0)
    convert h using 1 <;> first
      | rfl
      | (rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one]; ring)
  have htmu : HasDerivAt (fun s : ℝ => s * μ) (1 * μ) t :=
    (hasDerivAt_id' t).mul_const μ
  have hK : HasDerivAt (fun s : ℝ => Real.log ((1 - μ) + μ * Real.exp s) - s * μ)
      (bernoulliTiltedMean μ t - 1 * μ) t := HasDerivAt.sub hlog htmu
  have hgap : HasDerivAt
      (fun s : ℝ => s ^ 2 / 8 - (Real.log ((1 - μ) + μ * Real.exp s) - s * μ))
      (2 * t / 8 - (bernoulliTiltedMean μ t - 1 * μ)) t :=
    HasDerivAt.sub hsq8 hK
  have hfun : (fun s : ℝ => s ^ 2 / 8 - (Real.log ((1 - μ) + μ * Real.exp s) - s * μ)) =
      bernoulliMGFGap μ := by funext s; rfl
  rw [hfun] at hgap
  have heq : bernoulliMGFDeriv μ t =
      2 * t / 8 - (bernoulliTiltedMean μ t - 1 * μ) := by
    simp only [bernoulliMGFDeriv, one_mul]
    ring
  rw [heq]
  exact hgap

/-- `g₁` est monotone croissante globale : `g₁'(t) = 1/4 − q(t)·(1−q(t)) ≥ 0` (bernoulli_var_le). -/
theorem bernoulliMGFDeriv_monotone (μ : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    Monotone (bernoulliMGFDeriv μ) := by
  apply monotone_of_hasDerivAt_nonneg
    (f' := fun x => 1 / 4 - bernoulliTiltedMean μ x * (1 - bernoulliTiltedMean μ x))
  · intro x
    have hs4 : HasDerivAt (fun s : ℝ => s / 4) (1 / 4) x := by
      have h := HasDerivAt.div (hasDerivAt_id' x) (hasDerivAt_const x 4) (by norm_num : (4 : ℝ) ≠ 0)
      convert h using 1 <;> first | rfl | ring
    have hq : HasDerivAt (bernoulliTiltedMean μ)
        (bernoulliTiltedMean μ x * (1 - bernoulliTiltedMean μ x)) x :=
      bernoulliTiltedMean_hasDerivAt μ x hμ hμ2
    have hqmu : HasDerivAt (fun s : ℝ => bernoulliTiltedMean μ s - μ)
        (bernoulliTiltedMean μ x * (1 - bernoulliTiltedMean μ x) - 0) x :=
      HasDerivAt.sub hq (hasDerivAt_const x μ)
    have hg1 : HasDerivAt (fun s : ℝ => s / 4 - (bernoulliTiltedMean μ s - μ))
        (1 / 4 - (bernoulliTiltedMean μ x * (1 - bernoulliTiltedMean μ x) - 0)) x :=
      HasDerivAt.sub hs4 hqmu
    have hfun : (fun s : ℝ => s / 4 - (bernoulliTiltedMean μ s - μ)) = bernoulliMGFDeriv μ := by
      funext s; rfl
    rw [hfun] at hg1
    convert hg1 using 1 <;> first | rfl | ring
  · intro x
    have h := bernoulli_var_le (bernoulliTiltedMean μ x)
    show 0 ≤ 1 / 4 - bernoulliTiltedMean μ x * (1 - bernoulliTiltedMean μ x)
    linarith

/-- `g₁(0) = 0` (car `q(0) = μ`). -/
theorem bernoulliMGFDeriv_zero (μ : ℝ) : bernoulliMGFDeriv μ 0 = 0 := by
  have hq : bernoulliTiltedMean μ 0 = μ := by
    simp only [bernoulliTiltedMean, Real.exp_zero, mul_one]
    field_simp
    ring
  simp only [bernoulliMGFDeriv, zero_div, hq, sub_self]

/-- `deriv g = g₁` (funext + HasDerivAt.deriv). -/
theorem deriv_bernoulliMGFGap (μ : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    deriv (bernoulliMGFGap μ) = bernoulliMGFDeriv μ := by
  funext x
  exact HasDerivAt.deriv (bernoulliMGFGap_hasDerivAt μ x hμ hμ2)

/-- `g` est continue (composée de polynôme, log, exp ; le log est défini car denom > 0). -/
theorem continuous_bernoulliMGFGap (μ : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    Continuous (bernoulliMGFGap μ) := by
  have hlog : Continuous (fun t : ℝ => Real.log ((1 - μ) + μ * Real.exp t)) := by
    apply Continuous.log
    · fun_prop
    · intro x; exact ne_of_gt (bernoulli_logmgf_denom_pos μ x hμ hμ2)
  show Continuous (fun t : ℝ => t ^ 2 / 8 - (Real.log ((1 - μ) + μ * Real.exp t) - t * μ))
  fun_prop

/-- `g(t) ≥ 0` pour `0 ≤ t` : g monotone croissante sur `Set.Ici 0`, `g(0) = 0`. -/
theorem bernoulliMGFGap_nonneg_of_nonneg (μ : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ bernoulliMGFGap μ t := by
  have hmono : MonotoneOn (bernoulliMGFGap μ) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (continuous_bernoulliMGFGap μ hμ hμ2).continuousOn
    · intro x _; exact (bernoulliMGFGap_hasDerivAt μ x hμ hμ2).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [deriv_bernoulliMGFGap μ hμ hμ2]
      have h0x : (0 : ℝ) ≤ x := Set.mem_Ici.mp (interior_subset hx)
      have h1 : bernoulliMGFDeriv μ 0 ≤ bernoulliMGFDeriv μ x :=
        (bernoulliMGFDeriv_monotone μ hμ hμ2) h0x
      rw [bernoulliMGFDeriv_zero] at h1
      exact h1
  have h0 : bernoulliMGFGap μ 0 = 0 := by
    have h1 : (1 - μ : ℝ) + μ = 1 := by ring
    show (0 : ℝ) ^ 2 / 8 - (Real.log ((1 - μ) + μ * Real.exp 0) - 0 * μ) = 0
    simp only [Real.exp_zero, mul_one, zero_mul, sub_zero]
    rw [h1, Real.log_one]
    ring
  have hIn : (0 : ℝ) ∈ Set.Ici 0 := Set.mem_Ici.mpr (le_refl _)
  have htIn : t ∈ Set.Ici 0 := Set.mem_Ici.mpr ht
  have := hmono hIn htIn ht
  rwa [h0] at this

/-- `g(t) ≥ 0` pour `t ≤ 0` : `−g` monotone croissante sur `Set.Iic 0` (car `g' = g₁ ≤ 0` sur
`Iio 0`), `g(0) = 0`. -/
theorem bernoulliMGFGap_nonneg_of_nonpos (μ : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) {t : ℝ}
    (ht : t ≤ 0) : 0 ≤ bernoulliMGFGap μ t := by
  have hcont : ContinuousOn (fun s => -bernoulliMGFGap μ s) (Set.Iic 0) :=
    (continuous_bernoulliMGFGap μ hμ hμ2).neg.continuousOn
  have hmono : MonotoneOn (fun s => -bernoulliMGFGap μ s) (Set.Iic 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iic 0)
    · exact hcont
    · intro x _
      exact (bernoulliMGFGap_hasDerivAt μ x hμ hμ2).differentiableAt.neg.differentiableWithinAt
    · intro x hx
      have hderiv : deriv (fun s => -bernoulliMGFGap μ s) x = -bernoulliMGFDeriv μ x :=
        (bernoulliMGFGap_hasDerivAt μ x hμ hμ2).neg.deriv
      rw [hderiv]
      have hx0 : x ≤ (0 : ℝ) := Set.mem_Iic.mp (interior_subset hx)
      have h1 : bernoulliMGFDeriv μ x ≤ bernoulliMGFDeriv μ 0 :=
        (bernoulliMGFDeriv_monotone μ hμ hμ2) hx0
      rw [bernoulliMGFDeriv_zero] at h1
      linarith
  have h0 : bernoulliMGFGap μ 0 = 0 := by
    have h1 : (1 - μ : ℝ) + μ = 1 := by ring
    show (0 : ℝ) ^ 2 / 8 - (Real.log ((1 - μ) + μ * Real.exp 0) - 0 * μ) = 0
    simp only [Real.exp_zero, mul_one, zero_mul, sub_zero]
    rw [h1, Real.log_one]
    ring
  have hIn : (0 : ℝ) ∈ Set.Iic 0 := Set.mem_Iic.mpr (le_refl _)
  have htIn : t ∈ Set.Iic 0 := Set.mem_Iic.mpr ht
  have hle := hmono htIn hIn ht
  simp only at hle
  rw [h0, neg_zero] at hle
  linarith

/-- Le **lemme de Hoeffding** (forme Bernoulli) — borne analytique finale. Pour `μ ∈ [0, 1]`
et tout `t ∈ ℝ`, la MGF centrée est majorée par `exp(t²/8)`. C'est l'ingrédient exact qui,
combiné à l'indépendance produit (brique 3/5) et à l'optimisation `t = 4ε` (brique 4/5), donne
la concentration bilatérale de Hoeffding (brique 5/5). Preuve via le gap `g = t²/8 − log MGF ≥ 0`
(monotonie de la dérivée, sans `deriv^[2]`), puis exponentiation. -/
theorem bernoulli_mgf_le (μ t : ℝ) (hμ : 0 ≤ μ) (hμ2 : μ ≤ 1) :
    μ * Real.exp (t * (1 - μ)) + (1 - μ) * Real.exp (-(t * μ)) ≤ Real.exp (t ^ 2 / 8) := by
  have hgeq : 0 ≤ bernoulliMGFGap μ t := by
    by_cases ht : 0 ≤ t
    · exact bernoulliMGFGap_nonneg_of_nonneg μ hμ hμ2 ht
    · simp only [not_le] at ht
      exact bernoulliMGFGap_nonneg_of_nonpos μ hμ hμ2 ht.le
  have hDpos : 0 < (1 - μ) + μ * Real.exp t := bernoulli_logmgf_denom_pos μ t hμ hμ2
  have hlogle : Real.log ((1 - μ) + μ * Real.exp t) - t * μ ≤ t ^ 2 / 8 := by
    have heq : bernoulliMGFGap μ t = t ^ 2 / 8 - (Real.log ((1 - μ) + μ * Real.exp t) - t * μ) := rfl
    rw [heq, le_sub_iff_add_le] at hgeq
    linarith
  -- Forme produit (via `exp_add`, pas `exp_sub`) : la MGF = exp(log D) · exp(−tμ) = D · exp(−tμ).
  have hexp : (1 - μ + μ * Real.exp t) * Real.exp (-(t * μ)) ≤ Real.exp (t ^ 2 / 8) := by
    have hkey : Real.exp (Real.log ((1 - μ) + μ * Real.exp t) + -(t * μ)) ≤ Real.exp (t ^ 2 / 8) := by
      apply Real.exp_le_exp.mpr
      linarith [hlogle]
    rw [Real.exp_add, Real.exp_log hDpos] at hkey
    exact hkey
  -- Factorisation : μ·exp(t(1−μ)) + (1−μ)·exp(−tμ) = (1−μ+μ·exp t)·exp(−tμ) (algèbre, atomes
  -- `exp t` et `exp(−tμ)`), via `exp_add` sur `exp(t(1−μ)) = exp(t − tμ)`.
  rw [show t * (1 - μ) = t + -(t * μ) by ring, Real.exp_add]
  have heq : μ * (Real.exp t * Real.exp (-(t * μ))) + (1 - μ) * Real.exp (-(t * μ)) =
      (1 - μ + μ * Real.exp t) * Real.exp (-(t * μ)) := by ring
  rw [heq]
  exact hexp


end PacLearning
