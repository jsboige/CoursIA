import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic

/-!
# Actualisation géométrique — Identités prouvées

Lemmas sur l'actualisation géométrique utilisant l'analyse réelle de Mathlib.
Ce sont les briques élémentaires de la formalisation de l'indice de Gittins.
-/

namespace Gittins

open Real

/-!
## Série géométrique

La série géométrique Σ γ^n converge vers 1/(1-γ) pour |γ| < 1.
Mathlib fournit `tsum_geometric_of_lt_one` pour cela.
-/

/-- La somme partielle d'une série géométrique : Σ_{k=0}^{n-1} γ^k -/
def geometricPartialSum (γ : ℝ) (n : ℕ) : ℝ :=
  (List.range n).foldl (fun acc k => acc + γ ^ k) 0

/-!
## Faits fondamentaux sur la somme partielle finie

La série géométrique infinie (`∑' n, γ^n`) est traitée plus bas via Mathlib. Ces
lemmas établissent les identités élémentaires sur la somme partielle *finie*
`geometricPartialSum γ n` — la somme vide, la récurrence télescopique qui la
construit terme par terme, et la forme fermée classique `(1 − γ^n)/(1 − γ)` valable
pour `γ ≠ 1`. Ils sont le pendant fini de `geometric_series_converges` et rendent
la définition de somme partielle utilisable (elle était précédemment définie mais
inutilisée).
-/

/-- **Somme partielle vide.** `geometricPartialSum γ 0 = 0` — sommer sur la plage
    vide `List.range 0 = []` donne l'identité additive. -/
lemma geometricPartialSum_zero (γ : ℝ) : geometricPartialSum γ 0 = 0 := by
  simp [geometricPartialSum]

/-- **Récurrence télescopique.** Chaque terme ajouté contribue `γ^n` :
    `geometricPartialSum γ (n+1) = geometricPartialSum γ n + γ^n`. C'est l'identité
    pas-à-pas sous-jacente à la somme finie (et le moteur d'induction de la forme
    fermée ci-dessous). -/
lemma geometricPartialSum_succ (γ : ℝ) (n : ℕ) :
    geometricPartialSum γ (n + 1) = geometricPartialSum γ n + γ ^ n := by
  simp only [geometricPartialSum, List.range_succ, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

/-- **Forme fermée de la somme partielle finie** (identité classique). Pour
    `γ ≠ 1`, la somme partielle `Σ_{k=0}^{n-1} γ^k` vaut `(1 − γ^n) / (1 − γ)`.
    Prouvée par récurrence sur `n` utilisant la récurrence
    `geometricPartialSum_succ`. C'est l'analogue fini de
    `geometric_series_converges` (qui fait tendre `n → ∞`). -/
lemma geometricPartialSum_closed {γ : ℝ} (hγ : γ ≠ 1) (n : ℕ) :
    geometricPartialSum γ n = (1 - γ ^ n) / (1 - γ) := by
  have hdenom : (1:ℝ) - γ ≠ 0 := sub_ne_zero.mpr hγ.symm
  induction n with
  | zero => simp [geometricPartialSum]
  | succ k ih =>
    rw [geometricPartialSum_succ, ih]
    field_simp [hdenom]
    ring

/-- Pour 0 ≤ γ < 1, la série géométrique converge.
    Encapsule `tsum_geometric_of_lt_one` de Mathlib. -/
theorem geometric_series_converges {γ : ℝ} (hγ₁ : 0 ≤ γ) (hγ₂ : γ < 1) :
    ∑' n : ℕ, γ ^ n = 1 / (1 - γ) := by
  rw [one_div]
  exact tsum_geometric_of_lt_one hγ₁ hγ₂

/-- Pour 0 ≤ γ < 1, 1 - γ > 0. -/
lemma one_minus_gamma_pos {γ : ℝ} (h : γ < 1) (h₀ : 0 ≤ γ) : 0 < 1 - γ := by
  linarith

/-- Pour 0 < γ < 1, la somme infinie actualisée d'une récompense constante r vaut
    r/(1-γ). Identité fondamentale utilisée dans le calcul de la valeur d'un bandit. -/
theorem present_value_constant {γ r : ℝ} (hγ₁ : 0 < γ) (hγ₂ : γ < 1) (hr : 0 ≤ r) :
    ∑' n : ℕ, γ ^ n * r = r / (1 - γ) := by
  have hγ₁' : 0 ≤ γ := le_of_lt hγ₁
  -- Sum_n gamma^n * r = (Sum_n gamma^n) * r = (1-gamma)^{-1} * r = r / (1-gamma)
  rw [tsum_mul_right, tsum_geometric_of_lt_one hγ₁' hγ₂]
  ring

/-- Un facteur d'actualisation plus proche de 1 donne une valeur présente plus
    élevée. Si γ₁ ≤ γ₂, alors Σ γ₁^n ≤ Σ γ₂^n.

    **Stratégie de preuve** : réécrire les deux tsum via l'identité géométrique
    fermée `∑' n, γ^n = 1/(1-γ)` (`geometric_series_converges`), puis ramener le
    but à `1/(1-γ₁) ≤ 1/(1-γ₂)`. Comme `γ₁ ≤ γ₂` on a `1-γ₂ ≤ 1-γ₁`, et les deux
    dénominateurs sont positifs (`γ₂ < 1`), donc `one_div_le_one_div_of_le` clôt le
    but. Cela contourne l'absence de `tsum_le_tsum` sur `ℝ` (non disponible dans
    Mathlib v4.30.0-rc2 pour les séries sur `ℝ` brut) en exploitant la forme
    fermée. -/
theorem discount_monotone {γ₁ γ₂ : ℝ} (h₁ : 0 ≤ γ₁) (h₂ : γ₁ ≤ γ₂) (h₃ : γ₂ < 1) :
    ∑' n : ℕ, γ₁ ^ n ≤ ∑' n : ℕ, γ₂ ^ n := by
  have hγ₁_lt : γ₁ < 1 := lt_of_le_of_lt h₂ h₃
  have hγ₂_nn : 0 ≤ γ₂ := le_trans h₁ h₂
  rw [geometric_series_converges h₁ hγ₁_lt, geometric_series_converges hγ₂_nn h₃]
  -- But : 1 / (1 - γ₁) ≤ 1 / (1 - γ₂)
  -- Comme γ₁ ≤ γ₂, on a 1 - γ₂ ≤ 1 - γ₁ ; les deux dénominateurs sont positifs.
  apply one_div_le_one_div_of_le
  · exact sub_pos.mpr (by linarith)  -- 0 < 1 - γ₂
  · linarith                        -- 1 - γ₂ ≤ 1 - γ₁

end Gittins
