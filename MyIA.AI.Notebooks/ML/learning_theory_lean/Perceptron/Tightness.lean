import Mathlib
import Perceptron.Perceptron
import Perceptron.Convergence

/-!
# Saturation de la borne de Novikoff — un témoin serrant (sharpness)

> **Résultat.** La borne de Novikoff `n · γ² ≤ R²` (autrement dit
> `n ≤ (R/γ)²` mises à jour) est **optimale** : on exhibe une exécution valide du
> perceptron, sur `ℂ` vu comme espace préhilbertien réel de dimension 2, qui
> **sature** la borne — `n · γ² = R²` exactement. Une constante universelle
> strictement plus petite que `1` devant `(R/γ)²` ne saurait donc majorer le
> nombre d'erreurs sur toutes les exécutions séparables.

**Témoin géométrique.** Deux points `x₀ = 1 + I`, `x₁ = 1 − I` (demi-droites à
±45°), tous deux d'étiquette `+1`, séparés par le vecteur unitaire `u = 1` avec
marge `γ = 1`, chacun de norme `‖xₖ‖ = √2` (donc `R = √2`). La première mise à
jour fait `w₁ = x₀ = 1 + I` ; au deuxième pas,
`⟪w₁, x₁⟫ = ⟨1 + I, 1 − I⟩ = 0` (les deux demi-droites sont orthogonales) :
`x₁` est exactement sur la frontière de décision de `w₁`, donc la mise à jour est
une erreur. On obtient alors `n · γ² = 2 · 1 = 2 = (√2)² = R²` : **égalité** — la
borne est atteinte, donc serrée.

L'espace `ℂ` porte l'instance `InnerProductSpace ℝ ℂ` ; le produit scalaire réel
se déplie par `⟪w, z⟫_ℝ = (z · conj w).re` (`Complex.inner` +
`Complex.starRingEnd_apply`), i.e. `w.re · z.re + w.im · z.im`, et les normes par
`‖z‖² = Complex.normSq z = z.re² + z.im²` (`Complex.normSq_eq_norm_sq`,
`Complex.normSq_apply`).

Ce module est **entièrement sorry-free** : il s'agit d'un résultat de *sharpness*
concret (égalité atteinte), distinct du théorème de borne universelle
`novikoff_mistake_bound` (inégalité) démontré dans `Convergence.lean`.
-/

open scoped InnerProductSpace

open Complex

namespace Perceptron

/-- Produit scalaire réel sur `ℂ` déplié en coordonnées : `⟪w, z⟫ = w.re·z.re +
w.im·z.im` (lemme utilitaire pour les calculs concrets du témoin). -/
theorem complex_inner_re (w z : ℂ) : ⟪w, z⟫_ℝ = w.re * z.re + w.im * z.im := by
  rw [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Les points `xₖ` du témoin : `x₀ = 1 + I`, `xₖ = 1 − I` pour `k ≥ 1`
(deux demi-droites à ±45° du plan complexe). -/
def witnessPts : ℕ → ℂ
  | 0 => 1 + I
  | _ + 1 => 1 - I

/-- Les étiquettes du témoin : toutes `+1`. -/
def witnessLbl : ℕ → ℝ := fun _ => 1

/-- `‖xₖ‖² = 2` pour tout `k` (les deux demi-droites ont même norme `√2`). -/
theorem witnessPts_norm_sq (k : ℕ) : ‖witnessPts k‖ ^ 2 = 2 := by
  rcases k with rfl | k
  · rw [show ‖witnessPts 0‖ ^ 2 = Complex.normSq (witnessPts 0) from
          (Complex.normSq_eq_norm_sq _).symm,
        Complex.normSq_apply, witnessPts]
    norm_num [Complex.add_re, Complex.add_im, I_re, I_im]
  · rw [show ‖witnessPts (k + 1)‖ ^ 2 = Complex.normSq (witnessPts (k + 1)) from
          (Complex.normSq_eq_norm_sq _).symm,
        Complex.normSq_apply, witnessPts]
    norm_num [Complex.sub_re, Complex.sub_im, I_re, I_im]

/-- La marge `⟪u, xₖ⟫ = ⟨1, xₖ⟩ = 1` pour tout `k` (égale à `γ`). -/
theorem witness_margin_inner (k : ℕ) : ⟪(1 : ℂ), witnessPts k⟫_ℝ = 1 := by
  rw [complex_inner_re]
  rcases k with rfl | k
  · rw [witnessPts]
    norm_num [Complex.add_re, Complex.add_im, I_re, I_im]
  · rw [witnessPts]
    norm_num [Complex.sub_re, Complex.sub_im, I_re, I_im]

/-- Le produit scalaire « d'erreur » `⟪1 + I, 1 − I⟫ = 0` (orthogonalité des deux
demi-droites) — cœur de la deuxième mise à jour. -/
theorem witness_cross_inner : ⟪(1 + I : ℂ), 1 - I⟫_ℝ = 0 := by
  rw [complex_inner_re]
  norm_num [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, I_re, I_im]

/-- Après la première mise à jour, `w₁ = x₀ = 1 + I`. -/
theorem witness_w1 : perceptronWeights witnessPts witnessLbl 1 = 1 + I := by
  rw [perceptronWeights_succ, perceptronWeights_zero, zero_add]
  show witnessLbl 0 • witnessPts 0 = 1 + I
  rw [show witnessLbl 0 = 1 from rfl, show witnessPts 0 = (1 + I : ℂ) from rfl]
  exact one_smul _ _

theorem witness_lbl : ∀ k < (2 : ℕ), witnessLbl k ^ 2 = 1 := by
  intro k _
  rw [show witnessLbl k = 1 from rfl]
  norm_num

theorem witness_rad : ∀ k < (2 : ℕ), ‖witnessPts k‖ ≤ Real.sqrt 2 := by
  intro k _
  have h := witnessPts_norm_sq k
  have hnn : 0 ≤ ‖witnessPts k‖ := norm_nonneg _
  calc ‖witnessPts k‖
      = Real.sqrt (‖witnessPts k‖ ^ 2) := (Real.sqrt_sq hnn).symm
    _ = Real.sqrt 2 := by rw [h]
    _ ≤ Real.sqrt 2 := le_refl _

theorem witness_margin : ∀ k < (2 : ℕ),
    (1 : ℝ) ≤ witnessLbl k * ⟪(1 : ℂ), witnessPts k⟫_ℝ := by
  intro k _
  rw [show witnessLbl k = 1 from rfl, one_mul]
  linarith [witness_margin_inner k]

theorem witness_mistake : ∀ k < (2 : ℕ),
    witnessLbl k * ⟪perceptronWeights witnessPts witnessLbl k, witnessPts k⟫_ℝ ≤ 0 := by
  intro k _
  have h01 : k = 0 ∨ k = 1 := by omega
  rcases h01 with rfl | rfl
  · rw [perceptronWeights_zero, inner_zero_left, show witnessLbl 0 = 1 from rfl]
    norm_num
  · rw [witness_w1, show witnessLbl 1 = 1 from rfl, one_mul,
        show witnessPts 1 = (1 - I : ℂ) from rfl]
    linarith [witness_cross_inner]

/-- L'exécution saturante : `n = 2` points de `ℂ`, séparés par `u = 1` avec marge
`γ = 1`, de rayon `R = √2`, atteignant `n · γ² = R²`. -/
noncomputable def tightnessRun : PerceptronRun ℂ :=
  { n := 2,
    pts := witnessPts,
    lbl := witnessLbl,
    u := 1,
    R := Real.sqrt 2,
    γ := 1,
    hR := Real.sqrt_nonneg _,
    hγ := one_pos,
    hUnit := norm_one,
    hLbl := witness_lbl,
    hRad := witness_rad,
    hMargin := witness_margin,
    hMistake := witness_mistake }

/-- Le témoin atteint la borne **avec égalité** : `n · γ² = R²`. -/
theorem tightnessRun_saturates :
    (tightnessRun.n : ℝ) * tightnessRun.γ ^ 2 = tightnessRun.R ^ 2 := by
  have hn : tightnessRun.n = 2 := rfl
  have hγ : tightnessRun.γ = 1 := rfl
  have hR : tightnessRun.R = Real.sqrt 2 := rfl
  rw [hn, hγ, hR]
  rw [show (Real.sqrt 2 : ℝ) ^ 2 = 2 from Real.sq_sqrt (by norm_num)]
  norm_num

/-- **La borne de Novikoff est serrée.** Il existe une exécution valide (sur `ℂ`)
qui l'atteint avec égalité `n · γ² = R²`. Puisque `novikoff_mistake_bound` donne
l'inégalité universelle `n · γ² ≤ R²` et que l'égalité est atteinte par
`tightnessRun`, aucune borne de la forme `n · γ² ≤ c · R²` avec `c < 1` n'est
universellement valable : la constante `1` (devant `(R/γ)²`) est optimale. -/
theorem novikoff_bound_is_sharp :
    ∃ run : PerceptronRun ℂ, (run.n : ℝ) * run.γ ^ 2 = run.R ^ 2 :=
  ⟨tightnessRun, tightnessRun_saturates⟩

end Perceptron
