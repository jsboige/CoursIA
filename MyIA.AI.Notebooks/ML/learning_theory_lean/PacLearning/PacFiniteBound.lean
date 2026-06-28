import Mathlib
import PacLearning.Data
import PacLearning.Sample
import PacLearning.Concentration
import PacLearning.SampleExpect
import PacLearning.UnionBound

set_option maxHeartbeats 4000000

/-!
# PacLearning.PacFiniteBound — borne de complexité d'échantillon (flagship PAC)

Sous-module de `PacLearning` : le **théorème phare** `pac_finite_class_bound`
(complexité d'échantillon pour une classe finie, Valiant 1984). Pour une classe
d'hypothèses finie `H` et un concept cible `f`, si la taille d'échantillon `n`
dépasse `(1/ε)·(ln|H| + ln(1/δ))`, alors avec probabilité `≥ 1 − δ` sur `S ∼ D^n`,
**toute** hypothèse cohérente sur `S` a une erreur vraie `≤ ε` :

    n ≥ (1/ε)·(ln|H| + ln(1/δ))  ⟹
    ℙ_S [ ∃ hyp ∈ H, empError(hyp) = 0 ∧ ε < trueError(hyp) ] ≤ δ.

## Cadre : cas réalisable (Valiant 1984, forme originale)

C'est la borne **réalisable** canonique (le learner retourne une hypothèse
cohérente avec l'échantillon, cadre ERM-réalisable). Elle combine trois
ingrédients, dont deux déjà prouvés dans les briques précédentes :

1. **Factorisation d'indépendance i.i.d.** (`sampleExpect_prod_coord`, brique 3/5)
   via le lemme-clé `sampleProb_consistent_le` : la probabilité qu'une hypothèse
   `hyp` (d'erreur vraie `μ`) soit cohérente sur l'échantillon vaut
   `∏_i E_D[𝟙{hyp=f}] = (1 − μ)^n` — les tirages étant i.i.d. par construction de
   la mesure produit `D^n`. C'est le pont entre l'indépendance (brique 3/5) et la
   concentration.
2. **Borne géométrique** `one_sub_pow_le_exp` : `(1 − x)^n ≤ exp(−ε·n)` dès que
   `ε ≤ x ≤ 1` (via `log(1−x) ≤ −x`, lemme `Real.log_le_sub_one_of_pos`). Comme
   `μ_h ≥ ε` pour une « mauvaise » hypothèse, on obtient `(1−μ_h)^n ≤ exp(−ε·n)`.
3. **Union bound** (`sampleProb_union_bound`, brique 3/3) sur la classe finie :
   `ℙ[∃ hyp, cohérente ∧ μ_h > ε] ≤ ∑_hyp exp(−ε·n) = |H|·exp(−ε·n) ≤ δ`, la
   dernière inégalité se réécrivant exactement en `n ≥ (1/ε)(ln|H| + ln(1/δ))`.

## OPEN — cas agnostique (Hoeffding)

La borne **agnostique** `n ≥ (1/(2ε²))·(ln(2|H|/δ))` (Shalev-Shwartz–Ben-David,
*Understanding Machine Learning* §2.4) requiert la concentration de
Hoeffding-for-Bernoulli `ℙ[|empError − trueError| > ε] ≤ 2·exp(−2nε²)`,
elle-même bloquée sur la borne analytique de MGF générale (brique 2b/5,
`bernoulli_mgf_le` — route de convexité documentée OPEN dans `BernoulliMGF.lean`).
Le présent module livre le **cas réalisable** (qui est la borne `1/ε` originale de
Valiant 1984, exactement celle énoncée dans le docstring module de `Data.lean`) ;
l'agnostique suivra quand 2b/5 sera clos.

Style **ℝ-weight pédagogique** (pas de `ℝ≥0∞` / `Measure`), cohérent avec `Data.lean`.
-/

namespace PacLearning

open Finset
-- NOTE : pas de `open scoped Classical` ici. Raison : il active `Classical.propDecidable`
-- globalement, ce qui ferait que la synthèse de l'instance `Decidable` pour le prédicat
-- existentiel `∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp` du flagship
-- préférerait `Classical.decPred` au lieu du paramètre explicite `hDec` (→ non-defeq).
-- Sans `open scoped Classical`, tous les `by_cases`/`if` du module — qui portent sur des
-- Props *constructivement* décidables (ℝ `=`, ℝ `<`, Bool `≠`, conjonctions, ∃ sur Finset
-- via le paramètre `hDec`) — synthétisent exactement `hDec` pour le ∃, sans blowup de
-- l'énumération `decidableExistsAndFinsetCoe` (hDec prime sur la synthèse Finset).
variable {X : Type*} [Fintype X]
variable (D : Distribution X)

/-- **Caractérisation de la cohérence** : l'erreur empirique est nulle ssi `hyp`
classe correctement **tous** les exemples de `S`. C'est le pont entre la définition
numérique `empError = (∑ indicateurs)/n` et l'événement booléen « cohérent sur `S` ».

Preuve : `empError = 0 ⟺ (∑ ind)/n = 0` puis (n > 0) `⟺ ∑ ind = 0`
(`div_eq_zero_iff` : `a/b = 0 ↔ a = 0 ∨ b = 0`, et `n > 0` écarte `b = 0`)
`⟺ ∀ i, ind(S_i) = 0` (`sum_eq_zero_iff_of_nonneg` : une somme de termes `≥ 0`
est nulle ssi tous ses termes le sont — **contraposée**, pas de borne inférieure)
`⟺ ∀ i, hyp(S_i) = f(S_i)`. -/
theorem empError_eq_zero_iff {n : ℕ} (f hyp : Hypothesis X) (S : Fin n → X) (hn : 0 < n) :
    empError f hyp S = 0 ↔ ∀ i : Fin n, hyp (S i) = f (S i) := by
  dsimp only [empError]
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hnonneg : ∀ i, 0 ≤ (if hyp (S i) ≠ f (S i) then (1 : ℝ) else 0) := by
    intro i
    by_cases hsi : hyp (S i) ≠ f (S i) <;> simp [hsi]
  constructor
  · -- (→) chaque indicateur est nul (somme nulle de termes ≥ 0).
    intro h i
    have hsum0 : ∑ j, (if hyp (S j) ≠ f (S j) then (1 : ℝ) else 0) = 0 := by
      rcases (div_eq_zero_iff).mp h with h0 | hn0
      · exact h0
      · exact absurd hn0 (by exact_mod_cast (ne_of_gt hn))
    have hall : ∀ i, (if hyp (S i) ≠ f (S i) then (1 : ℝ) else 0) = 0 := by
      intro i
      exact (sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hsum0 i (mem_univ i)
    by_cases hsi : hyp (S i) = f (S i)
    · exact hsi
    · -- hsi : hyp(S_i) ≠ f(S_i) : l'indicateur vaut 1, contredisant `hall` (= 0).
      exfalso
      have h1 : (if hyp (S i) ≠ f (S i) then (1 : ℝ) else 0) = 1 := if_pos hsi
      linarith [hall i]
  · -- (←) tous corrects ⟹ tous indicateurs nuls ⟹ somme nulle ⟹ empError = 0.
    intro h
    have hsum0 : ∑ i, (if hyp (S i) ≠ f (S i) then (1 : ℝ) else 0) = 0 := by
      apply (sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mpr
      intro i _
      have hi : hyp (S i) = f (S i) := h i
      simp [hi]
    -- (∑ indicateurs)/n = 0 via ∑ = 0 (branche `a = 0` de `div_eq_zero_iff`).
    exact (div_eq_zero_iff).mpr (Or.inl hsum0)

/-- **Borne géométrique → exponentielle** : pour `ε ≤ x ≤ 1`, `(1 − x)^n ≤ exp(−ε·n)`.
Lemme analytique générique (pas spécifique à PAC). Preuve par route du logarithme :
`log(1 − x) ≤ (1 − x) − 1 = −x` (`Real.log_le_sub_one_of_pos`), donc
`log((1−x)^n) = n·log(1−x) ≤ −(x·n) ≤ −(ε·n)`, et `(1−x)^n = exp(log((1−x)^n))
≤ exp(−ε·n)` par monotonie de `exp`. Le cas `x = 1` (`(1−x) = 0`) est traité à part. -/
theorem one_sub_pow_le_exp (x : ℝ) (n : ℕ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (ε : ℝ)
    (hxe : ε ≤ x) : (1 - x) ^ n ≤ Real.exp (-(ε * n)) := by
  have h1mx : 0 ≤ 1 - x := by linarith
  by_cases hz : 1 - x = 0
  · -- x = 1 : (1-x)^n = 0^n. n = 0 ⟹ 0^0 = 1 ≤ exp(0) = 1 ; n > 0 ⟹ 0 ≤ exp(−εn).
    have hx1' : x = 1 := by linarith
    subst hx1'
    by_cases hn : n = 0
    · simp [hn, Real.exp_zero]
    · have h0n : (1 - 1 : ℝ) ^ n = 0 := by
        have h11 : (1 - 1 : ℝ) = 0 := by norm_num
        rw [h11]
        exact zero_pow (by omega)
      rw [h0n]
      exact (le_of_lt (Real.exp_pos _))
  · have hpos : 0 < 1 - x := lt_of_le_of_ne h1mx (Ne.symm hz)
    have hpospow : 0 < (1 - x) ^ n := pow_pos hpos n
    have hlog : Real.log (1 - x) ≤ -x := by
      have := Real.log_le_sub_one_of_pos hpos
      linarith
    -- (1-x)^n = exp(n · log(1-x)).
    have heq : (1 - x) ^ n = Real.exp (n * Real.log (1 - x)) := by
      rw [← Real.exp_log hpospow, Real.log_pow]
    rw [heq]
    refine Real.exp_le_exp.mpr ?_
    -- n · log(1-x) ≤ -(x·n) (via log(1-x) ≤ -x), puis -(x·n) ≤ -(ε·n) (via ε ≤ x).
    have hstep : (n : ℝ) * Real.log (1 - x) ≤ -(x * (n : ℝ)) := by
      calc (n : ℝ) * Real.log (1 - x)
          ≤ (n : ℝ) * (-x) := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (n := n))
        _ = -(x * (n : ℝ)) := by ring
    have hen : -(x * (n : ℝ)) ≤ -(ε * (n : ℝ)) := by
      have hle : ε * (n : ℝ) ≤ x * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hxe (Nat.cast_nonneg (n := n))
      linarith [hle]
    linarith [hstep, hen]

/-- **Probabilité de cohérence** d'une hypothèse `hyp` sur `S ∼ D^n` :
`ℙ_S[empError(hyp) = 0] ≤ (1 − trueError(hyp))^n`. C'est le **lemme-pivot** du cas
réalisable : il traduit la factorisation i.i.d. (brique 3/5) en une borne concrète.

Preuve : l'indicateur `𝟙{empError=0}` coïncide point par point avec le produit des
indicateurs de bonne classification par coordonnée `∏_i cc(S_i)` (`cc = 𝟙{hyp=f}`) —
via `empError_eq_zero_iff` (un produit de valeurs `{0,1}` vaut `1` ssi toutes
valent `1`). On passe alors à `sampleExpect` : `E_S[∏_i cc(S_i)] = ∏_i E_D[cc]`
(factorisation i.i.d. `sampleExpect_prod_coord`, brique 3/5), et `E_D[cc] =
1 − trueError` (l'espérance du complément de l'indicateur d'erreur, via
`expect_linear` + `trueError_eq_expect`). -/
theorem sampleProb_consistent_le {n : ℕ} (f hyp : Hypothesis X) (hn : 0 < n) :
    sampleProb D (fun S : Fin n → X => empError f hyp S = 0) ≤
      (1 - trueError D f hyp) ^ n := by
  -- (1) `𝟙{empError=0} = ∏_i cc(S_i)` point par point, cc(x) = 𝟙{hyp x = f x}.
  have hind : ∀ S : Fin n → X,
      (if empError f hyp S = 0 then (1 : ℝ) else 0) =
        ∏ i : Fin n, (if hyp (S i) = f (S i) then (1 : ℝ) else 0) := by
    intro S
    by_cases hS : empError f hyp S = 0
    · -- Tous corrects ⟹ ∏ cc(S_i) = 1 (chaque cc = 1).
      rw [if_pos hS]
      have hall := (empError_eq_zero_iff f hyp S hn).mp hS
      have hcc1 : ∀ i : Fin n, (if hyp (S i) = f (S i) then (1 : ℝ) else 0) = 1 :=
        fun i => if_pos (hall i)
      simp [hcc1]
    · -- Au moins un incorrect ⟹ ∏ cc(S_i) = 0 (un facteur cc = 0).
      rw [if_neg hS]
      have hnot : ¬ ∀ i : Fin n, hyp (S i) = f (S i) := by
        intro hall
        exact hS ((empError_eq_zero_iff f hyp S hn).mpr hall)
      obtain ⟨i₀, hi₀⟩ := not_forall.mp hnot
      have hprod : ∏ i : Fin n, (if hyp (S i) = f (S i) then (1 : ℝ) else 0) = 0 := by
        rw [Finset.prod_eq_zero_iff]
        exact ⟨i₀, mem_univ i₀, if_neg hi₀⟩
      rw [hprod]
  -- expect D cc = 1 − trueError (cc = 1 − indicateur d'erreur).
  have hbase : expect D (fun x => if hyp x = f x then (1 : ℝ) else 0) = 1 - trueError D f hyp := by
    rw [show (fun x => (if hyp x = f x then (1 : ℝ) else 0)) =
          (fun x => (1 : ℝ) * ((fun _ : X => (1 : ℝ)) x) + (-(1 : ℝ)) *
            ((fun x => if hyp x ≠ f x then (1 : ℝ) else 0) x)) from
        by funext x; by_cases hx : hyp x = f x <;> simp [hx]]
    rw [expect_linear (1 : ℝ) (-1 : ℝ), expect_const (1 : ℝ),
        ← trueError_eq_expect f hyp]
    ring
  -- (2) Chaîne d'ÉGALITÉS : sampleProb = sampleExpect(ind) = sampleExpect(∏ cc)
  --     = ∏ E_D[cc] = (1-trueError)^n (l'indicateur = le produit cc, point par point).
  have key : sampleProb D (fun S : Fin n → X => empError f hyp S = 0) =
      (1 - trueError D f hyp) ^ n := by
    calc sampleProb D (fun S : Fin n → X => empError f hyp S = 0)
        = sampleExpect D (fun S => (if empError f hyp S = 0 then (1 : ℝ) else 0)) :=
            sampleProb_eq_sampleExpect _
      _ = sampleExpect D (fun S => ∏ i : Fin n, (if hyp (S i) = f (S i) then (1 : ℝ) else 0)) := by
            simp only [hind]
      _ = ∏ _ : Fin n, expect D (fun x => if hyp x = f x then (1 : ℝ) else 0) :=
            sampleExpect_prod_coord (fun x => if hyp x = f x then (1 : ℝ) else 0)
      _ = (expect D (fun x => if hyp x = f x then (1 : ℝ) else 0)) ^ n := by
            rw [prod_const, Finset.card_univ, Fintype.card_fin]
      _ = (1 - trueError D f hyp) ^ n := by rw [hbase]
  exact key.le

/-! ## Instance décidable partagée (garantie defeq)

Deux littéraux `Classical.decPred _` distincts sont **non-defeq** car `Classical.choice`
est opaque (axiomatique) : le `hDec` du `@sampleProb ...` du *statement* ne s'unifie pas
avec celui passé à `_aux`. On factorise donc l'instance en un **symbole unique**
`pacDecidable` (`@[reducible]` pour satisfaire le linter des class-types), référencé
identiquement des deux côtés → defeq garanti par construction (le prédicat étant fixé par
la signature de `pacDecidable`, les deux occurrences unfold vers le *même* terme
`Classical.decPred P`, defeq — contrairement à deux `_` séparés). -/

@[reducible] noncomputable def pacDecidable {n : ℕ} (Hs : Finset (Hypothesis X)) (f : Hypothesis X)
    (ε : ℝ) (D : Distribution X) :
    DecidablePred (fun S : Fin n → X =>
      ∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp) :=
  Classical.decPred _

/-! ## Théorème phare — complexité d'échantillon PAC (cas réalisable)

Borne de Valiant (1984) : pour une classe finie `Hs`, un concept cible `f`, et
`n ≥ (1/ε)·(ln|Hs| + ln(1/δ))`, la probabilité qu'existe une hypothèse **cohérente** sur
l'échantillon `S` mais d'erreur vraie `> ε` est bornée par `δ`. Preuve (3 ingrédients) :

1. **Borne par-hypothèse** (`sampleProb_consistent_le` + `one_sub_pow_le_exp`) : pour chaque
   `hyp` « mauvaise » (`trueError > ε`), `ℙ[cohérente ∧ mauvaise] ≤ ℙ[cohérente] ≤
   (1−μ)^n ≤ exp(−εn)` (i.i.d. via `sampleExpect_prod_coord`). Si `hyp` est bonne, vide.
2. **Union bound** (Bornes de Boole) au niveau `sampleExpect` : point par point
   `𝟙{∃ hyp ∈ Hs, cohérente ∧ mauvaise} ≤ ∑_hyp 𝟙{cohérente ∧ mauvaise}` (via
   `Finset.single_le_sum`), puis monotonie + linéarité Finset ⟹ `ℙ[∃ hyp mauvais cohérent]
   ≤ ∑_hyp ℙ[hyp] ≤ |Hs|·exp(−εn)`.
3. **Algèbre finale** : `|Hs|·exp(−εn) ≤ δ ⟺ ln|Hs| + ln(1/δ) ≤ εn ⟺ n ≥ (1/ε)(ln|Hs| +
   ln(1/δ))` (hypothèse `hm`), via `Real.exp_add` + `Real.exp_log`.

**Note technique** (`_aux`) : ce lemme prend l'instance `DecidablePred` **explicite**
(paramètre `hDec`), mis en scope locale via `haveI := hDec`. Requis car la synthèse par
défaut du prédicat existentiel `∃ hyp ∈ Hs, …` tombe sur `decidableExistsAndFinsetCoe`
qui **énumère** la classe de fonctions `Hypothesis X = X → Bool` (~12.7M réductions,
timeout). L'annotation `@ite ℝ (∃ hyp ∈ Hs, …) (hDec S)` force l'instance sans synthèse.
Le wrapper public `pac_finite_class_bound` (ci-dessous) instancie `hDec` via `pacDecidable`.
-/
theorem pac_finite_class_bound_aux {n : ℕ} (Hs : Finset (Hypothesis X)) (f : Hypothesis X)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hH : 0 < (Hs.card : ℝ)) (hn : 0 < n)
    (hm : (1 / ε) * (Real.log (Hs.card : ℝ) + Real.log (1 / δ)) ≤ n)
    (hDec : DecidablePred (fun S : Fin n → X =>
      ∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp)) :
    @sampleProb X _ D n (fun S : Fin n → X =>
      ∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp) hDec ≤ δ := by
  haveI := hDec
  let P (hyp : Hypothesis X) (S : Fin n → X) : Prop :=
    empError f hyp S = 0 ∧ ε < trueError D f hyp
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  -- Étape 1 : borne par-hypothèse `ℙ[P hyp] ≤ exp(−εn)`.
  have hPhyp : ∀ hyp ∈ Hs, sampleProb D (P hyp) ≤ Real.exp (-(ε * n)) := by
    intro hyp hhyp
    by_cases hbad : ε < trueError D f hyp
    · -- `P hyp ⊆ {empError=0}` (probabilités monotones pour l'inclusion).
      have hsub : sampleProb D (P hyp) ≤ sampleProb D (fun S : Fin n → X => empError f hyp S = 0) := by
        rw [sampleProb_eq_sampleExpect, sampleProb_eq_sampleExpect]
        apply sampleExpect_mono
        intro S
        by_cases hS : empError f hyp S = 0
        · -- empError=0 ∧ hbad ⟹ P hyp S, both indicateurs = 1 ⟹ 1 ≤ 1.
          rw [if_pos ⟨hS, hbad⟩, if_pos hS]
        · -- empError≠0 ⟹ ind(E=0)=0 et P=False ⟹ ind(P)=0 ⟹ 0 ≤ 0.
          rw [if_neg (fun h => hS h.1), if_neg hS]
      calc sampleProb D (P hyp)
          ≤ sampleProb D (fun S : Fin n → X => empError f hyp S = 0) := hsub
        _ ≤ (1 - trueError D f hyp) ^ n := sampleProb_consistent_le D f hyp hn
        _ ≤ Real.exp (-(ε * n)) :=
            one_sub_pow_le_exp (trueError D f hyp) n
              (trueError_nonneg (D := D) (f := f) (h := hyp))
              (trueError_le_one (D := D) (f := f) (h := hyp)) ε (le_of_lt hbad)
    · -- `hyp` est bonne : `P hyp` est vide, probabilité `0`.
      have h0 : sampleProb D (P hyp) = 0 := by
        dsimp only [sampleProb]
        apply sum_eq_zero
        intro S _
        rw [if_neg (fun h => hbad h.2), mul_zero]
      rw [h0]
      exact (le_of_lt (Real.exp_pos _))
  -- Étape 2 : union bound sur `Hs` fini, au niveau `sampleExpect` (évite le blowup
  -- whnf de la synthèse Decidable par défaut, qui énumère `Hypothesis X = X → Bool`
  -- via `decidableExistsAndFinsetCoe` — ~12.7M réductions). L'instance `DecidablePred`
  -- pour `∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp` est fournie par le
  -- paramètre `hDec` (mis en scope locale via `haveI := hDec`) : tout `if (∃ hyp ∈ Hs, ...)`
  -- synthétise alors `hDec` (sans énumérer la classe de fonctions). L'union bound se
  -- prouve point par point `𝟙{∃ hyp ∈ Hs, P hyp S} ≤ ∑_hyp 𝟙{P hyp S}` (via
  -- `Finset.single_le_sum`), puis on remonte à `sampleExpect` (monotonie + linéarité
  -- Finset). On évite ainsi `sampleProb_union_bound` (dont le LHS `sampleProb D (∃ hyp
  -- ∈ Hs, ...)` synthétiserait son instance Finset et serait non-defeq avec `hDec`).
  have hind_le : ∀ S : Fin n → X,
      @ite ℝ (∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp) (hDec S) (1:ℝ) 0 ≤
        ∑ hyp ∈ Hs, (if empError f hyp S = 0 ∧ ε < trueError D f hyp then (1:ℝ) else 0) := by
    intro S
    -- `Classical.em` évite la synthèse `Decidable` (qui tomberait sur `decidableExist-
    -- sAndFinsetCoe` → énumération de `Hypothesis X`). L'instance est fournie par `hDec`.
    rcases Classical.em (∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp) with h | h
    · -- témoin `hyp₀` : son indicateur vaut `1`, et les autres sont `≥ 0`.
      obtain ⟨hyp₀, hhyp₀, hP₀⟩ := h
      have hge : ∀ hyp ∈ Hs, 0 ≤ (if empError f hyp S = 0 ∧ ε < trueError D f hyp then (1:ℝ) else 0) := by
        intro hyp _; by_cases hp : empError f hyp S = 0 ∧ ε < trueError D f hyp <;> simp [hp]
      calc @ite ℝ (∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp) (hDec S) (1:ℝ) 0
          = 1 := if_pos ⟨hyp₀, hhyp₀, hP₀⟩
        _ = (if empError f hyp₀ S = 0 ∧ ε < trueError D f hyp₀ then 1 else 0) := (if_pos hP₀).symm
        _ ≤ ∑ hyp ∈ Hs, (if empError f hyp S = 0 ∧ ε < trueError D f hyp then (1:ℝ) else 0) :=
              Finset.single_le_sum hge hhyp₀
    · -- pas de témoin : indicateur(`∃`) = 0 ≤ somme (de termes `≥ 0`).
      simp only [if_neg h]
      exact Finset.sum_nonneg (fun hyp _ =>
        by by_cases hp : empError f hyp S = 0 ∧ ε < trueError D f hyp <;> simp [hp])
  calc @sampleProb X _ D n (fun S : Fin n → X =>
        ∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp) hDec
      = sampleExpect D (fun S =>
          @ite ℝ (∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp) (hDec S) (1:ℝ) 0) :=
          @sampleProb_eq_sampleExpect X _ D n
            (fun S : Fin n → X => ∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp) hDec
    _ ≤ sampleExpect D (fun S =>
          ∑ hyp ∈ Hs, (if empError f hyp S = 0 ∧ ε < trueError D f hyp then (1:ℝ) else 0)) :=
          sampleExpect_mono hind_le
    _ = ∑ hyp ∈ Hs, sampleExpect D (fun S =>
          (if empError f hyp S = 0 ∧ ε < trueError D f hyp then (1:ℝ) else 0)) := by
        dsimp only [sampleExpect]
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ hyp ∈ Hs, sampleProb D (P hyp) := by
          refine Finset.sum_congr rfl (fun hyp _ => (sampleProb_eq_sampleExpect (P hyp)).symm)
    _ ≤ ∑ hyp ∈ Hs, Real.exp (-(ε * n)) := sum_le_sum (fun hyp hh => hPhyp hyp hh)
    _ = (Hs.card : ℝ) * Real.exp (-(ε * n)) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          -- `ring` omis : `simp` réduit déjà `∑_hyp exp = ↑card · exp` à `rfl`.
    _ ≤ δ := by
        -- `|Hs|·exp(−εn) ≤ δ` depuis `n ≥ (1/ε)(ln|Hs| + ln(1/δ))`.
        -- (a) log|Hs| + log(1/δ) ≤ ε·n.
        have hL : Real.log (Hs.card : ℝ) + Real.log (1 / δ) ≤ ε * n := by
          have hm' : (Real.log (Hs.card : ℝ) + Real.log (1 / δ)) / ε ≤ n := by
            rw [show (Real.log (Hs.card : ℝ) + Real.log (1 / δ)) / ε =
                    (1 / ε) * (Real.log (Hs.card : ℝ) + Real.log (1 / δ)) from by ring]
            exact hm
          linarith [(div_le_iff₀ hε).mp hm']
        -- (b) exp(log|Hs| + log(1/δ)) ≤ exp(ε·n)  ⟹  |Hs| · (1/δ) ≤ exp(εn).
        have hexp := Real.exp_le_exp.mpr hL
        rw [Real.exp_add, Real.exp_log hH, Real.exp_log (one_div_pos.mpr hδ)] at hexp
        -- hexp : (Hs.card : ℝ) * (1/δ) ≤ exp(ε·n).
        -- (c) |Hs| ≤ δ · exp(εn) (multiplier hexp par δ > 0).
        have hcard : (Hs.card : ℝ) ≤ δ * Real.exp (ε * n) := by
          calc (Hs.card : ℝ)
              = (Hs.card : ℝ) * ((1 / δ) * δ) := by
                  rw [div_mul_cancel₀ (1 : ℝ) (ne_of_gt hδ), mul_one]
            _ = ((Hs.card : ℝ) * (1 / δ)) * δ := by ring
            _ ≤ Real.exp (ε * n) * δ := mul_le_mul_of_nonneg_right hexp hδ.le
            _ = δ * Real.exp (ε * n) := by ring
        -- (d) |Hs| · exp(−εn) = |Hs| · exp(εn)⁻¹ ≤ (δ · exp(εn)) · exp(εn)⁻¹ = δ.
        rw [Real.exp_neg]
        calc (Hs.card : ℝ) * (Real.exp (ε * n))⁻¹
            ≤ (δ * Real.exp (ε * n)) * (Real.exp (ε * n))⁻¹ :=
                mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr (Real.exp_pos _).le)
          _ = δ := by
                rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.exp_pos _)), mul_one]

/-- **Théorème phare — complexité d'échantillon PAC (cas réalisable, Valiant 1984)** :
wrapper public du lemme auxiliaire `pac_finite_class_bound_aux`, instancié avec
`pacDecidable` (instance décidable classique du prédicat d'existence sur `Hs`
fini, factorisée en symbole unique pour garantir le defeq *statement*↔appel). Voir `pac_finite_class_bound_aux` pour le corps de preuve et la
justification du passage d'instance explicite (contournement du non-defeq de
`Classical.choice`). -/
theorem pac_finite_class_bound {n : ℕ} (Hs : Finset (Hypothesis X)) (f : Hypothesis X)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hH : 0 < (Hs.card : ℝ)) (hn : 0 < n)
    (hm : (1 / ε) * (Real.log (Hs.card : ℝ) + Real.log (1 / δ)) ≤ n) :
    @sampleProb X _ D n (fun S : Fin n → X =>
      ∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp) (pacDecidable Hs f ε D) ≤ δ :=
  pac_finite_class_bound_aux D Hs f ε δ hε hδ hH hn hm (pacDecidable Hs f ε D)

end PacLearning
