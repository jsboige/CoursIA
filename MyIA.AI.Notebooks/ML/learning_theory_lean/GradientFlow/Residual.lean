import Mathlib

/-!
# GradientFlow.Residual — survie du gradient dans une pile résiduelle

Sous-module de `GradientFlow` (digestion #13106, forme formalisation) : chaque
bloc de la pile est maintenant un **bloc résiduel** `h ↦ h + f h` — le raccourci
identité de He, Zhang, Ren & Sun (*Deep Residual Learning for Image
Recognition*, arXiv:1512.03385, 2015). Si chaque branche contracte la dérivée
(`|f'_k| ≤ c` avec `c ≤ 1`), le terme `+1` du raccourci change la marche : la
dérivée de chaque bloc est `1 + f'_k`, de module au moins `1 - c > 0`, et
l'induction sur la profondeur donne

    (1 - c) ^ n ≤ |(g_{n-1} ∘ … ∘ g_0)'|,

le gradient **survit** géométriquement au lieu de mourir. À contraction de
branche égale `c = 0,4`, l'écart avec la pile plain est de trois ordres de
grandeur à profondeur 20 : `0,6 ^ 20 ≈ 3,7e-5` contre `0,4 ^ 20 ≈ 1,1e-8` —
ancres numériques `three_fifths_pow_twenty_gt` et
`GradientFlow.two_fifths_pow_twenty_lt`.

La borne inférieure repose sur l'anti-inégalité triangulaire tirée de
`abs_add_le` (`1 - |t| ≤ |1 + t|`). Toutes les preuves sont **0-sorry**.
-/

namespace GradientFlow

variable (fs : ℕ → ℝ → ℝ) (c : ℝ)

/-- Bloc résiduel (raccourci identité, He et al. 2016) : `h ↦ h + f h`. La
dérivée en un point est `1 + f'`, de module au moins `1 - |f'|`. -/
def residualBlock (f : ℝ → ℝ) : ℝ → ℝ := fun h => h + f h

/-- **Anti-inégalité triangulaire (forme du bloc résiduel)** : le terme `+1` du
raccourci garantit `1 - |t| ≤ |1 + t|` — la dérivée d'un bloc résiduel ne peut
pas descendre sous `1 - c` quand la branche contracte à `|f'| ≤ c`. -/
theorem one_sub_le_abs_add (t : ℝ) : 1 - |t| ≤ |1 + t| := by
  have h : (1 : ℝ) ≤ |1 + t| + |t| := by
    simpa using abs_add_le (1 + t) (-t)
  linarith

/-- Pile résiduelle de profondeur `n` : composition des blocs résiduels
construits sur `fs 0, …, fs (n-1)`. `residualStack fs 0 = id` et
`residualStack fs (n + 1) = residualBlock (fs n) ∘ residualStack fs n`. -/
def residualStack (fs : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => id
  | n + 1 => residualBlock (fs n) ∘ residualStack fs n

/-- **Lemme central** : par induction sur la profondeur, la pile résiduelle
dérive en un produit dont le module est **minoré** par `(1 - c) ^ n` dès que
chaque branche dérive et contracte (`|f'_k| ≤ c`, `c ≤ 1`). -/
theorem residualStack_deriv_bound (hc1 : c ≤ 1)
    (hf : ∀ k x, DifferentiableAt ℝ (fs k) x ∧ |deriv (fs k) x| ≤ c) (x : ℝ) :
    ∀ n, ∃ d : ℝ, HasDerivAt (residualStack fs n) d x ∧ (1 - c) ^ n ≤ |d| := by
  intro n
  induction n with
  | zero =>
    refine ⟨1, ?_, ?_⟩
    · simpa [residualStack] using hasDerivAt_id x
    · simp
  | succ n ih =>
    obtain ⟨dA, hA, hB⟩ := ih
    have hfd := (hf n (residualStack fs n x)).1
    have hBlock : HasDerivAt (residualBlock (fs n))
        (1 + deriv (fs n) (residualStack fs n x)) (residualStack fs n x) :=
      (hasDerivAt_id _).add hfd.hasDerivAt
    have hcomp := HasDerivAt.comp x hBlock hA
    show ∃ d : ℝ, HasDerivAt (residualBlock (fs n) ∘ residualStack fs n) d x ∧
      (1 - c) ^ (n + 1) ≤ |d|
    refine ⟨(1 + deriv (fs n) (residualStack fs n x)) * dA, hcomp, ?_⟩
    have hFs : |deriv (fs n) (residualStack fs n x)| ≤ c := (hf n _).2
    have hLow : 1 - c ≤ |1 + deriv (fs n) (residualStack fs n x)| :=
      (sub_le_sub_left hFs 1).trans (one_sub_le_abs_add _)
    have hc0 : 0 ≤ 1 - c := sub_nonneg.mpr hc1
    rw [abs_mul, pow_succ, ← mul_comm (1 - c) ((1 - c) ^ n)]
    calc (1 - c) * (1 - c) ^ n
        ≤ |1 + deriv (fs n) (residualStack fs n x)| * (1 - c) ^ n :=
          mul_le_mul_of_nonneg_right hLow (pow_nonneg hc0 n)
      _ ≤ |1 + deriv (fs n) (residualStack fs n x)| * |dA| :=
          mul_le_mul_of_nonneg_left hB (abs_nonneg _)

/-- **Survie du gradient (pile résiduelle)** : si chaque branche contracte la
dérivée (`|f'_k| ≤ c`, `c ≤ 1`), la dérivée de la pile de `n` blocs est
**minorée** par `(1 - c) ^ n` — le raccourci identité empêche l'évanouissement
exponentiel de la pile plain (`abs_deriv_plainStack_le`). -/
theorem abs_deriv_residualStack_ge (hc1 : c ≤ 1)
    (hf : ∀ k x, DifferentiableAt ℝ (fs k) x ∧ |deriv (fs k) x| ≤ c) (x : ℝ) (n : ℕ) :
    (1 - c) ^ n ≤ |deriv (residualStack fs n) x| := by
  obtain ⟨d, hA, hB⟩ := residualStack_deriv_bound fs c hc1 hf x n
  rw [hA.deriv]
  exact hB

/-- **Ancre numérique jumelle** (notebook `4.2-ConvNet-Profonde-Residuelles`,
§6) : à contraction de branche égale `c = 0,4`, la pile résiduelle laisse
passer au moins `0,6 ^ 20 ≈ 3,7e-5` — trois ordres de grandeur au-dessus de la
pile plain (`0,4 ^ 20 ≈ 1,1e-8`, voir `GradientFlow.two_fifths_pow_twenty_lt`). -/
theorem three_fifths_pow_twenty_gt : 3 / 10 ^ 5 < (3 / 5 : ℝ) ^ 20 := by norm_num

end GradientFlow
