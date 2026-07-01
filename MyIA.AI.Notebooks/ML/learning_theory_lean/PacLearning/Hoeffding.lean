import Mathlib
import PacLearning.Data
import PacLearning.Sample
import PacLearning.SampleExpect
import PacLearning.UnionBound
import PacLearning.MGF
import PacLearning.BernoulliMGF

/-!
# PacLearning.Hoeffding — concentration de Hoeffding-for-Bernoulli (brique 2c/3, en cours)

Sous-module de `PacLearning` : la **moitié analytique** du flagship
`pac_finite_class_bound` (l'autre moitié, combinatoire = union bound, est livrée dans
`UnionBound.lean`). On prouve la **concentration de Hoeffding** pour la moyenne
d'indicateurs i.i.d. :

    ℙ_S [ |empError − trueError| > ε ] ≤ 2·exp(−2·n·ε²).

Méthode de Chernoff (ℝ-weight pédagogique, pas le cadre Mathlib Kernel/Measure) :

1. **Chernoff-Markov** (ce livrable, brique 1/5) — `ℙ[Y ≥ a] ≤ e^{−t·a}·E[e^{t·Y}]` pour
   `t > 0` : Markov sur la variable positive `Z = e^{t·Y}` au seuil `e^{t·a}`, via
   `{Z ≥ e^{t·a}} = {Y ≥ a}` (car `x ↦ e^{t·x}` strictement croissante pour `t > 0`).
2. **MGF Bernoulli** (OPEN, brique 2/5) — `E_D[exp(t·(ind − μ))] ≤ exp(t²/8)` (lemme de
   Hoeffding, `X ∈ [0,1]` ⟹ variance `≤ 1/4` ⟹ log-MGF `≤ t²/8`).
3. **Indépendance produit** (OPEN, brique 3/5) — `E_S[exp(t·Σᵢ(ind(Sᵢ) − μ))] =
   ∏ᵢ E_D[...] ≤ exp(n·t²/8)` (technique `sampleExpect_coord` étendue aux produits).
4. **Optimisation** (OPEN, brique 4/5) — `min_t e^{−t·n·ε}·e^{n·t²/8} = e^{−2·n·ε²}`
   (atteint en `t = 4ε`).
5. **Bilatéral** (OPEN, brique 5/5) — `|empError − trueError| ≥ ε = (· ≥ ε) ∪ (· ≤ −ε)` →
   borne `· 2` via `sampleProb_union_bound` (UnionBound.lean).

Ce livrable pose la **brique 1 (Chernoff-Markov)** `chernoff_ineq`, ingrédient fondamental
de toute la chaîne, entièrement prouvé (sans tactic d'ajournement). On reste dans le style **ℝ-weight
pédagogique** : la probabilité est une somme pondérée (`sampleProb`), l'espérance aussi
(`sampleExpect`), et la méthode de Chernoff ne fait appel qu'à la monotonie de
`sampleExpect` et à la croissance de l'exponentielle.
-/

namespace PacLearning

open Finset
open scoped Classical

variable {X : Type*} [Fintype X]
variable (D : Distribution X)
variable {D}

/-- **Linéarité en un facteur scalaire à droite** : `E[g · c] = E[g] · c` (le scalaire
sort de la somme pondérée via `Finset.sum_mul`). Variante à droite de `sampleExpect_smul`
(qui sort le scalaire à gauche). Réutilisé par `chernoff_ineq` (pour factoriser la
constante `e^{−t·a}` hors de l'espérance de `e^{t·Y}`). -/
theorem sampleExpect_mul_const {n : ℕ} (c : ℝ) (g : (Fin n → X) → ℝ) :
    sampleExpect D (fun S ↦ g S * c) = sampleExpect D g * c := by
  dsimp only [sampleExpect]
  simp only [show ∀ S, sampleWeight D S * (g S * c) = (sampleWeight D S * g S) * c from
               fun _ ↦ by ring]
  rw [← Finset.sum_mul]

/-- **Chernoff-Markov (inégalité de Chernoff sur l'exponentielle)** : pour `t > 0`, la
probabilité que `Y ≥ a` est majorée par `e^{−t·a} · E[e^{t·Y}]`.

    ℙ_S [ Y S ≥ a ] ≤ e^{−t·a} · E_{S∼D^m} [ e^{t·Y S} ].

C'est Markov appliqué à la variable positive `Z = e^{t·Y}` au seuil `e^{t·a}` :
`{Z ≥ e^{t·a}} = {Y ≥ a}` (car `x ↦ e^{t·x}` est strictement croissante pour `t > 0`),
donc `ℙ[Y ≥ a] = ℙ[Z ≥ e^{t·a}] ≤ E[Z] / e^{t·a} = e^{−t·a} · E[e^{t·Y}]`.

Preuve directe en ℝ-weight : point par point, l'indicateur `𝟙{a ≤ Y S}` est
`≤ e^{t·(Y S − a)}` (cas `a ≤ Y` : `t·(Y−a) ≥ 0` ⟹ `e^{t·(Y−a)} ≥ e⁰ = 1 = 𝟙` par
croissance de l'exponentielle ; cas `¬(a ≤ Y)` : `𝟙 = 0 ≤ e^{...}`, l'exponentielle étant
strictement positive). On passe alors par `sampleExpect` (monotonie `sampleExpect_mono`),
puis on factorise `e^{t·(Y−a)} = e^{t·Y} · e^{−t·a}` (`Real.exp_add`) où `e^{−t·a}` est
constant en `S`, sorti via `sampleExpect_mul_const`.

C'est l'**ingrédient #1** de la concentration de Hoeffding (brique 1/5) : borne
générique de Chernoff, valable pour toute fonction `Y : (Fin n → X) → ℝ`, indépendante
de la structure Bernoulli (qui n'intervient qu'à la brique 2 via la MGF). -/
theorem chernoff_ineq {n : ℕ} (Y : (Fin n → X) → ℝ) (a : ℝ) (t : ℝ) (ht : 0 < t) :
    sampleProb D (fun S ↦ a ≤ Y S) ≤
      sampleExpect D (fun S ↦ Real.exp (t * Y S)) * Real.exp (-(t * a)) := by
  -- (1) Point par point : `𝟙{a ≤ Y S} ≤ e^{t·(Y S − a)}` (le seul `if`, isolé dans un
  -- `have` hors du calc des sommes, évitant les frictions d'instance `Decidable`).
  have hind : ∀ S : Fin n → X,
      (if a ≤ Y S then (1 : ℝ) else 0) ≤ Real.exp (t * (Y S - a)) := by
    intro S
    by_cases h : a ≤ Y S
    · -- `Y ≥ a` ⟹ `t·(Y−a) ≥ 0` ⟹ `e^{t·(Y−a)} ≥ e⁰ = 1`.
      rw [if_pos h, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr
        (mul_nonneg (le_of_lt ht) (sub_nonneg.mpr h))
    · -- `Y < a` ⟹ `𝟙 = 0 ≤ e^{...}` (exponentielle strictement positive).
      rw [if_neg h]
      exact (Real.exp_pos _).le
  -- (2) `e^{t·(Y−a)} = e^{t·Y} · e^{−t·a}` point par point (`Real.exp_add`).
  have hexp : ∀ S : Fin n → X,
      Real.exp (t * (Y S - a)) = Real.exp (t * Y S) * Real.exp (-(t * a)) := by
    intro S
    rw [show t * (Y S - a) = t * Y S + (-(t * a)) from by ring, Real.exp_add]
  -- (3) Assemblage : `ℙ = E[𝟙] ≤ E[e^{t(Y−a)}] = E[e^{tY}·e^{−ta}] = e^{−ta}·E[e^{tY}]`.
  calc sampleProb D (fun S ↦ a ≤ Y S)
      = sampleExpect D (fun S ↦ (if a ≤ Y S then (1 : ℝ) else 0)) :=
          sampleProb_eq_sampleExpect _
    _ ≤ sampleExpect D (fun S ↦ Real.exp (t * (Y S - a))) :=
        sampleExpect_mono hind
    _ = sampleExpect D (fun S ↦ Real.exp (t * Y S) * Real.exp (-(t * a))) :=
        congr_arg (sampleExpect D) (funext hexp)
    _ = sampleExpect D (fun S ↦ Real.exp (t * Y S)) * Real.exp (-(t * a)) :=
        sampleExpect_mul_const (Real.exp (-(t * a))) (fun S ↦ Real.exp (t * Y S))


/-! ## Briques 4/5 + 5/5 — concentration bilatérale de Hoeffding (itération finale)

On assemble la concentration complète de Hoeffding pour la moyenne d'indicateurs i.i.d. :

    ℙ_S [ |empError f h S − trueError D f h| ≥ ε ] ≤ 2 · exp(−2 · n · ε²).

Décomposition (chaque ingrédient est documenté comme brique 2-3 de l'analyse) :

1. `hoeffding_mgf_sum_le` (valable ∀ t ∈ ℝ) : `E_S[exp(t · Σ_i(ind_i − μ))] ≤ exp(n · t²/8)`,
   combinant l'**indépendance produit** (`sampleExpect_prod_coord`, brique 3/5), la **réduction
   algébrique** de la MGF (`expect_exp_centered_eq`, brique 2a/5) et la **borne analytique**
   (`bernoulli_mgf_le`, brique 2c/3).
2. `hoeffding_upper_tail` (brique 4/5) : `P(Σ_i(ind_i − μ) ≥ n·ε) ≤ exp(−2nε²)` via
   `chernoff_ineq` à `t = 4ε`, l'optimisation `t²/8 − t·ε = 2ε² − 4ε² = −2ε²` étant faite
   par `ring` dans la borne finale.
3. `hoeffding_lower_tail` : `P(Σ_i(ind_i − μ) ≤ −n·ε) ≤ exp(−2nε²)` — symétrique, via
   `chernoff_ineq` appliquée à `−Z` et `hoeffding_mgf_sum_le` en `t = −4ε` (légitime car ce
   dernier est valable ∀ t, lui-même conséquence de `bernoulli_mgf_le` ∀ t).
4. `hoeffding_concentration` (brique 5/5, flagship) : union des deux tails via
   `sampleProb_or_le`, après avoir réécrit `|empError − μ| ≥ ε` en la disjonction des deux
   tails sur `Z = Σ_i(ind_i − μ)` via l'identité `empError f h S − μ = Z S / n`.

On reste dans le style **ℝ-weight pédagogique** : aucune machine `ℝ≥0∞`/`Measure`/`iIndepFun`.
-/

/-- **Union de deux événements** (cas binaire de l'union bound) : la probabilité d'une
disjonction est majorée par la somme des probabilités. Plus léger que
`sampleProb_union_bound` (indexé par un `Finset`) lorsque l'on a exactement deux
événements — c'est le cadre du flagship bilatéral `(Z ≥ nε) ∨ (Z ≤ −nε)`. -/
theorem sampleProb_or_le {n : ℕ} (P Q : (Fin n → X) → Prop) [DecidablePred P] [DecidablePred Q] :
    sampleProb D (fun S ↦ P S ∨ Q S) ≤ sampleProb D P + sampleProb D Q := by
  -- Point par point : `𝟙{P∨Q} ≤ 𝟙_P + 𝟙_Q` (le seul `if`, isolé hors des sommes).
  have hind : ∀ S : Fin n → X,
      (if P S ∨ Q S then (1 : ℝ) else 0) ≤
        (if P S then (1 : ℝ) else 0) + (if Q S then (1 : ℝ) else 0) := by
    intro S
    by_cases hP : P S <;> by_cases hQ : Q S <;> simp [hP, hQ] <;> norm_num
  -- Assemblage : `ℙ = E[𝟙] ≤ E[𝟙_P + 𝟙_Q] = E[𝟙_P] + E[𝟙_Q] = ℙ_P + ℙ_Q`.
  calc sampleProb D (fun S ↦ P S ∨ Q S)
      = sampleExpect D (fun S ↦ (if P S ∨ Q S then (1 : ℝ) else 0)) := sampleProb_eq_sampleExpect _
    _ ≤ sampleExpect D (fun S ↦ (if P S then (1 : ℝ) else 0) + (if Q S then (1 : ℝ) else 0)) :=
        sampleExpect_mono hind
    _ = sampleExpect D (fun S ↦ (if P S then (1 : ℝ) else 0)) +
        sampleExpect D (fun S ↦ (if Q S then (1 : ℝ) else 0)) := by
        -- Additivité ponctuelle de `sampleExpect` : on déplie la définition (somme pondérée),
        -- puis `mul_add` distribue le poids sur chaque indicateur et `sum_add_distrib` scinde
        -- la somme. Évite `sampleExpect_linear (1)(1)` dont les args `g₁ g₂` implicites laissent
        -- une instance `typeclass problem is stuck`.
        dsimp only [sampleExpect]
        simp only [mul_add, Finset.sum_add_distrib]
    _ = sampleProb D P + sampleProb D Q := by
        rw [← sampleProb_eq_sampleExpect P, ← sampleProb_eq_sampleExpect Q]

/-- **Extensionnalité de `sampleProb`** : deux prédicats pointwise équivalents donnent la même
probabilité (les indicateurs `𝟙` coïncident point par point). Réutilisé par `hoeffding_lower_tail`
(flip d'événement `Z ≤ −nε ⟺ nε ≤ −Z`) et `hoeffding_concentration` (découplage
`|empError − μ| ≥ ε ⟺ (nε ≤ Z) ∨ (Z ≤ −nε)`). Évite les frictions d'instance `DecidablePred`
qu'engendre `congr_arg (sampleProb D)` sur les args implicites `{n}` et l'instance. -/
theorem sampleProb_congr {n : ℕ} (P Q : (Fin n → X) → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ S, P S ↔ Q S) : sampleProb D P = sampleProb D Q := by
  dsimp only [sampleProb]
  refine Finset.sum_congr rfl (fun S _ ↦ ?_)
  by_cases hP : P S
  · rw [if_pos hP, if_pos ((h S).mp hP)]
  · rw [if_neg hP, if_neg (mt (h S).mpr hP)]

/-- **MGF de la somme centrée** (brique combinée 3/5 + 2c/3) : pour `μ = trueError` et
`ind = 𝟙{h≠f}`, la fonction génératrice de moments de la somme empirique centrée
`Z S = Σ_i (ind(S_i) − μ)` est majorée par `exp(n · t²/8)`, **pour tout `t ∈ ℝ`**.

    E_{S∼D^m} [ exp (t · Σ_i (ind(S_i) − μ)) ] ≤ exp (n · t²/8).

Preuve : `exp(t·Σ_i g_i) = ∏_i exp(t·g_i)` (`Real.exp_sum` après `Finset.mul_sum`), puis
l'**indépendance produit** `sampleExpect_prod_coord` factorise en `∏_i E_D[exp(t·(ind−μ))]`,
chaque facteur se réduit algébriquement (`expect_exp_centered_eq`) en
`μ·exp(t(1−μ)) + (1−μ)·exp(−tμ)`, borné par `exp(t²/8)` (`bernoulli_mgf_le`, ∀ t). Le produit
des `n` facteurs `≤ exp(t²/8)` donne `exp(t²/8)^n = exp(n·t²/8)` (`Real.exp_nat_mul`).

La validité **∀ t** (pas seulement `t > 0`) est cruciale : elle rend le lower tail
immédiat (appliquer ce lemme en `t = −4ε`), car `bernoulli_mgf_le` est elle-même ∀ t. -/
theorem hoeffding_mgf_sum_le (f h : Hypothesis X) {n : ℕ} (t : ℝ) :
    sampleExpect D (fun S : Fin n → X ↦
      Real.exp (t * (∑ i : Fin n, ((if h (S i) ≠ f (S i) then (1 : ℝ) else 0) - trueError D f h)))) ≤
      Real.exp ((n : ℝ) * t ^ 2 / 8) := by
  set μ := trueError D f h
  have hμ : 0 ≤ μ := trueError_nonneg
  have hμ2 : μ ≤ 1 := trueError_le_one
  -- (1) `exp(t · Σ_i g_i) = ∏_i exp(t · g_i)` point par point (`mul_sum` sort le `t`, puis `exp_sum`).
  have hexp : ∀ S : Fin n → X,
      Real.exp (t * (∑ i : Fin n, ((if h (S i) ≠ f (S i) then (1 : ℝ) else 0) - μ))) =
        ∏ i : Fin n, Real.exp (t * ((if h (S i) ≠ f (S i) then (1 : ℝ) else 0) - μ)) := by
    intro S
    rw [← Real.exp_sum, ← Finset.mul_sum]
  -- (2) Assemblage : produit → indépendance produit → réduction algébrique → borne analytique.
  calc sampleExpect D (fun S : Fin n → X ↦
          Real.exp (t * (∑ i : Fin n, ((if h (S i) ≠ f (S i) then (1 : ℝ) else 0) - μ))))
      = sampleExpect D (fun S : Fin n → X ↦
          ∏ i : Fin n, Real.exp (t * ((if h (S i) ≠ f (S i) then (1 : ℝ) else 0) - μ))) := by
          simp only [hexp]
    _ = ∏ i : Fin n,
          expect D (fun x ↦ Real.exp (t * ((if h x ≠ f x then (1 : ℝ) else 0) - μ))) := by
          exact sampleExpect_prod_coord (fun x ↦ Real.exp (t * ((if h x ≠ f x then (1 : ℝ) else 0) - μ)))
    _ = ∏ i : Fin n, (μ * Real.exp (t * (1 - μ)) + (1 - μ) * Real.exp (-(t * μ))) := by
          congr 1
          funext i
          exact expect_exp_centered_eq f h t
    _ ≤ ∏ i : Fin n, Real.exp (t ^ 2 / 8) := by
          apply Finset.prod_le_prod
          · intro i _; positivity
          · intro i _; exact bernoulli_mgf_le μ t hμ hμ2
    _ = Real.exp ((n : ℝ) * t ^ 2 / 8) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
          congr 1; ring

/-- **Upper tail de Hoeffding** (brique 4/5) : la probabilité d'un excès `Z ≥ n·ε` de la
somme centrée `Z = Σ_i(ind_i − μ)` est majorée par `exp(−2·n·ε²)`.

    ℙ_S [ n·ε ≤ Σ_i (ind(S_i) − μ) ] ≤ exp(−2·n·ε²).

Preuve : `chernoff_ineq` à `t = 4ε` (`> 0`) borne `ℙ[Z ≥ nε]` par
`E[exp(4ε·Z)]·exp(−4ε·nε)`. La MGF `hoeffding_mgf_sum_le` (en `t = 4ε`) donne
`E[exp(4ε·Z)] ≤ exp(n·(4ε)²/8) = exp(2nε²)`, d'où `exp(2nε²)·exp(−4nε²) = exp(−2nε²)`
(l'algèbre des exposants via `Real.exp_add`). -/
theorem hoeffding_upper_tail (f h : Hypothesis X) {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    sampleProb D (fun S : Fin n → X ↦
      ↑n * ε ≤ ∑ i : Fin n, ((if h (S i) ≠ f (S i) then (1 : ℝ) else 0) - trueError D f h)) ≤
      Real.exp (-(2 * ↑n * ε ^ 2)) := by
  set μ := trueError D f h
  set Z : (Fin n → X) → ℝ := fun S ↦ ∑ i : Fin n, ((if h (S i) ≠ f (S i) then (1 : ℝ) else 0) - μ)
  have ht : 0 < (4 : ℝ) * ε := by positivity
  -- Chernoff-Markov : `ℙ[Z ≥ nε] ≤ E[exp(4ε·Z)] · exp(−4ε·nε)`.
  have hch : sampleProb D (fun S : Fin n → X ↦ ↑n * ε ≤ Z S) ≤
      sampleExpect D (fun S ↦ Real.exp (4 * ε * Z S)) * Real.exp (-(4 * ε * (↑n * ε))) :=
    @chernoff_ineq _ _ D _ Z (↑n * ε) (4 * ε) ht
  -- MGF bornée en `t = 4ε` : `E[exp(4ε·Z)] ≤ exp(2nε²)`.
  have hmgf : sampleExpect D (fun S : Fin n → X ↦ Real.exp (4 * ε * Z S)) ≤
      Real.exp (↑n * (4 * ε) ^ 2 / 8) :=
    hoeffding_mgf_sum_le f h (4 * ε)
  -- `exp(2nε²) · exp(−4nε²) = exp(−2nε²)` (`Real.exp_add` sur les exposants).
  calc sampleProb D (fun S ↦ ↑n * ε ≤ Z S)
      ≤ sampleExpect D (fun S ↦ Real.exp (4 * ε * Z S)) * Real.exp (-(4 * ε * (↑n * ε))) := hch
    _ ≤ Real.exp (↑n * (4 * ε) ^ 2 / 8) * Real.exp (-(4 * ε * (↑n * ε))) := by
          -- On borne `A·c ≤ B·c` (c = exp(−4ε·nε) > 0) par `mul_le_mul_of_nonneg_right`.
          -- `gcongr` ferme seul ce but sans laisser de sous-but à `exact` (instance stuck),
          -- d'où la forme explicite `hmgf` + `(Real.exp_pos _).le`.
          exact mul_le_mul_of_nonneg_right hmgf (Real.exp_pos _).le
    _ = Real.exp (-(2 * ↑n * ε ^ 2)) := by
          rw [← Real.exp_add]
          congr 1
          ring

/-- **Lower tail de Hoeffding** : la probabilité d'un défaut `Z ≤ −n·ε` est majorée par
`exp(−2·n·ε²)`.

    ℙ_S [ Σ_i (ind(S_i) − μ) ≤ −n·ε ] ≤ exp(−2·n·ε²).

Preuve : `Z ≤ −nε ⟺ −Z ≥ nε`. On applique `chernoff_ineq` à `−Z` à `t = 4ε` :
`ℙ[−Z ≥ nε] ≤ E[exp(4ε·(−Z))]·exp(−4ε·nε)`. Or `E[exp(4ε·(−Z))] = E[exp((−4ε)·Z)] ≤ exp(n·(−4ε)²/8)`
par `hoeffding_mgf_sum_le` en `t = −4ε` (valable ∀ t), soit `exp(2nε²)`. On conclut comme
l'upper tail. -/
theorem hoeffding_lower_tail (f h : Hypothesis X) {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    sampleProb D (fun S : Fin n → X ↦
      ∑ i : Fin n, ((if h (S i) ≠ f (S i) then (1 : ℝ) else 0) - trueError D f h) ≤ -(↑n * ε)) ≤
      Real.exp (-(2 * ↑n * ε ^ 2)) := by
  set μ := trueError D f h
  set Z : (Fin n → X) → ℝ := fun S ↦ ∑ i : Fin n, ((if h (S i) ≠ f (S i) then (1 : ℝ) else 0) - μ)
  have ht : 0 < (4 : ℝ) * ε := by positivity
  -- Chernoff-Markov sur `−Z` à `t = 4ε` : `ℙ[nε ≤ −Z] ≤ E[exp(4ε·(−Z))]·exp(−4ε·nε)`.
  have hch : sampleProb D (fun S : Fin n → X ↦ ↑n * ε ≤ -Z S) ≤
      sampleExpect D (fun S ↦ Real.exp (4 * ε * (-Z S))) * Real.exp (-(4 * ε * (↑n * ε))) :=
    @chernoff_ineq _ _ D _ (fun S ↦ -Z S) (↑n * ε) (4 * ε) ht
  -- MGF en `t = −4ε` (valable ∀ t, car `bernoulli_mgf_le` est ∀ t) : `E[exp(−4ε·Z)] ≤ exp(n·(−4ε)²/8)`.
  have hmgf : sampleExpect D (fun S : Fin n → X ↦ Real.exp (-(4 * ε) * Z S)) ≤
      Real.exp (↑n * (-(4 * ε)) ^ 2 / 8) :=
    hoeffding_mgf_sum_le f h (-(4 * ε))
  have hexpm : ∀ S, Real.exp (4 * ε * (-Z S)) = Real.exp (-(4 * ε) * Z S) := fun S ↦ by congr 1; ring
  -- `Z ≤ −nε ⟺ nε ≤ −Z` (point par point), puis on assemble comme l'upper tail.
  calc sampleProb D (fun S ↦ Z S ≤ -(↑n * ε))
      = sampleProb D (fun S ↦ ↑n * ε ≤ -Z S) :=
          sampleProb_congr _ _ (fun S ↦ ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩)
    _ ≤ sampleExpect D (fun S ↦ Real.exp (4 * ε * (-Z S))) * Real.exp (-(4 * ε * (↑n * ε))) := hch
    _ = sampleExpect D (fun S ↦ Real.exp (-(4 * ε) * Z S)) * Real.exp (-(4 * ε * (↑n * ε))) := by
          rw [show ((fun S : Fin n → X ↦ Real.exp (4 * ε * (-Z S))) :
                       (Fin n → X) → ℝ) = (fun S ↦ Real.exp (-(4 * ε) * Z S)) from funext hexpm]
    _ ≤ Real.exp (↑n * (-(4 * ε)) ^ 2 / 8) * Real.exp (-(4 * ε * (↑n * ε))) := by
          exact mul_le_mul_of_nonneg_right hmgf (Real.exp_pos _).le
    _ = Real.exp (-(2 * ↑n * ε ^ 2)) := by
          rw [← Real.exp_add]
          congr 1
          ring

/-- **Flagship — concentration bilatérale de Hoeffding** (brique 5/5) : pour `n ≥ 1` tirages
i.i.d. et `ε > 0`, la probabilité que l'erreur empirique dévie de son espérance d'au moins
`ε` est majorée par `2·exp(−2·n·ε²)`.

    ℙ_{S∼D^n} [ |empError f h S − trueError D f h| ≥ ε ] ≤ 2 · exp(−2 · n · ε²).

C'est le **résultat central** de la concentration pour la moyenne d'indicateurs de Bernoulli
i.i.d. — l'ingrédient exact qui, combiné à l'union bound sur une classe finie d'hypothèses
(`UnionBound.lean`), donne la complexité d'échantillon PAC de Valiant `m ≥ (1/ε)(ln|H|+ln(1/δ))`
(cas réalisable, brique 3/3) et `1/ε²` (cas agnostic).

Preuve : `|empError − μ| ≥ ε = (empError − μ ≥ ε) ∨ (μ − empError ≥ ε)`. Via l'identité
`empError f h S − μ = Z S / n` (`Z = Σ_i(ind_i − μ)`, `n > 0`), chaque branche se réécrit en un
tail sur `Z` borné par `hoeffding_upper_tail` / `hoeffding_lower_tail`. `sampleProb_or_le`
additionne les deux tails, donnant `2·exp(−2nε²)`. -/
theorem hoeffding_concentration (f h : Hypothesis X) {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    sampleProb D (fun S : Fin n → X ↦ ε ≤ |empError f h S - trueError D f h|) ≤
      2 * Real.exp (-(2 * ↑n * ε ^ 2)) := by
  set μ := trueError D f h
  set Z : (Fin n → X) → ℝ := fun S ↦ ∑ i : Fin n, ((if h (S i) ≠ f (S i) then (1 : ℝ) else 0) - μ)
  have hnreal : (0 : ℝ) < ↑n := mod_cast hn
  -- Identité clé : `empError − μ = Z S / n` (`Z = Σ_i(ind_i − μ) = A − nμ`, donc `Z/n = A/n − μ`).
  have hZid : ∀ S : Fin n → X, empError f h S - μ = Z S / (n : ℝ) := by
    intro S
    dsimp only [empError, Z]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    field_simp
    ring
  -- Découplage `|empError − μ| ≥ ε ⟺ (nε ≤ Z) ∨ (Z ≤ −nε)` via `empError − μ = Z/n` (n > 0).
  have hkey : ∀ S : Fin n → X,
      (ε ≤ |empError f h S - μ|) ↔ ((↑n * ε ≤ Z S) ∨ (Z S ≤ -(↑n * ε))) := by
    intro S
    rw [hZid, abs_div, abs_of_pos hnreal, le_div_iff₀ hnreal]
    constructor
    · -- `nε ≤ |Z| → (nε ≤ Z) ∨ (Z ≤ −nε)`
      intro h
      rcases le_total (Z S) 0 with hZ | hZ
      · rw [abs_of_nonpos hZ] at h; exact Or.inr (by linarith)
      · rw [abs_of_nonneg hZ] at h; exact Or.inl (by linarith)
    · -- `(nε ≤ Z) ∨ (Z ≤ −nε) → nε ≤ |Z|`
      rintro (h | h)
      · linarith [le_abs_self (Z S)]
      · have h2 : -Z S ≤ |Z S| := abs_neg (Z S) ▸ le_abs_self (-Z S)
        linarith
  -- Réécriture de l'événement `|empError − μ| ≥ ε` en la disjonction des deux tails sur `Z`,
  -- puis `sampleProb_or_le` les additionne, chacun borné par `exp(−2nε²)`.
  calc sampleProb D (fun S ↦ ε ≤ |empError f h S - μ|)
      = sampleProb D (fun S ↦ (↑n * ε ≤ Z S) ∨ (Z S ≤ -(↑n * ε))) :=
          sampleProb_congr _ _ (fun S ↦ hkey S)
    _ ≤ sampleProb D (fun S ↦ ↑n * ε ≤ Z S) + sampleProb D (fun S ↦ Z S ≤ -(↑n * ε)) :=
        sampleProb_or_le (fun S ↦ ↑n * ε ≤ Z S) (fun S ↦ Z S ≤ -(↑n * ε))
    _ ≤ Real.exp (-(2 * ↑n * ε ^ 2)) + Real.exp (-(2 * ↑n * ε ^ 2)) := by
          gcongr
          · exact hoeffding_upper_tail f h hε
          · exact hoeffding_lower_tail f h hε
    _ = 2 * Real.exp (-(2 * ↑n * ε ^ 2)) := by ring

end PacLearning
