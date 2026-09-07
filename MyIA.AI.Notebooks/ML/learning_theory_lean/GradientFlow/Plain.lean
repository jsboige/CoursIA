import Mathlib

/-!
# GradientFlow.Plain — évanouissement du gradient dans une pile « plain »

Sous-module de `GradientFlow` (digestion #13106, forme formalisation — cf pilote
CHSH #14858) : une pile de `n` blocs **sans raccourci** (« plain », l'empilement
d'études du notebook `4.2-ConvNet-Profonde-Residuelles`) est la composition
`f_{n-1} ∘ … ∘ f_0`. Si chaque bloc contracte la dérivée (`|f'_k| ≤ c`), la
règle de chaîne et une induction sur la profondeur donnent

    |(f_{n-1} ∘ … ∘ f_0)'| ≤ c ^ n,

et pour une contraction stricte `c < 1`, la borne `c ^ n` tend vers `0` : **le
gradient meurt exponentiellement vite avec la profondeur**. C'est exactement le
phénomène mesuré dans le notebook (§3) : facteur ≈ 0,4 par bloc, donc
`0,4 ^ 20 ≈ 1e-8` au bout de 20 blocs — un gradient cent million de fois plus
petit qu'en entrée. L'ancre numérique `two_fifths_pow_twenty_lt` verrouille cette
valeur du cours (`0,4 ^ 20 < 1e-7`).

Toutes les preuves sont **0-sorry** et élémentaires (règle de chaîne via
`HasDerivAt.comp`, puis monotonie du produit) : le contenu du module est le
théorème, pas les tactiques.
-/

namespace GradientFlow

variable (fs : ℕ → ℝ → ℝ) (c : ℝ)

/-- Pile « plain » de profondeur `n` : composition des blocs `0, …, n-1`, le bloc
`k` étant la fonction `fs k`. `plainStack fs 0 = id` et
`plainStack fs (n + 1) = fs n ∘ plainStack fs n`. -/
def plainStack (fs : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => id
  | n + 1 => fs n ∘ plainStack fs n

/-- **Lemme central** : par induction sur la profondeur, la pile plain dérive en
un produit de dérivées de blocs, de valeur absolue bornée par `c ^ n` dès que
chaque bloc dérive et contracte (`|f'_k| ≤ c`). La valeur dérivée est portée par
`HasDerivAt` pour que la récurrence reste syntaxique. -/
theorem plainStack_deriv_bound (hc : 0 ≤ c)
    (hf : ∀ k x, DifferentiableAt ℝ (fs k) x ∧ |deriv (fs k) x| ≤ c) (x : ℝ) :
    ∀ n, ∃ d : ℝ, HasDerivAt (plainStack fs n) d x ∧ |d| ≤ c ^ n := by
  intro n
  induction n with
  | zero =>
    refine ⟨1, ?_, ?_⟩
    · simpa [plainStack] using hasDerivAt_id x
    · simp
  | succ n ih =>
    obtain ⟨dA, hA, hB⟩ := ih
    have hfd := (hf n (plainStack fs n x)).1
    have hcomp := HasDerivAt.comp x hfd.hasDerivAt hA
    show ∃ d : ℝ, HasDerivAt (fs n ∘ plainStack fs n) d x ∧ |d| ≤ c ^ (n + 1)
    refine ⟨deriv (fs n) (plainStack fs n x) * dA, hcomp, ?_⟩
    have hFs : |deriv (fs n) (plainStack fs n x)| ≤ c := (hf n _).2
    rw [abs_mul, pow_succ, ← mul_comm c (c ^ n)]
    exact (mul_le_mul_of_nonneg_right hFs (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hB hc)

/-- **Évanouissement du gradient (pile plain)** : si chaque bloc contracte la
dérivée (`|f'_k| ≤ c`), la dérivée de la pile de `n` blocs est majorée par
`c ^ n`. Pour `c < 1`, `plainStack_gradient_vanishes` en tire la mort
exponentielle. -/
theorem abs_deriv_plainStack_le (hc : 0 ≤ c)
    (hf : ∀ k x, DifferentiableAt ℝ (fs k) x ∧ |deriv (fs k) x| ≤ c) (x : ℝ) (n : ℕ) :
    |deriv (plainStack fs n) x| ≤ c ^ n := by
  obtain ⟨d, hA, hB⟩ := plainStack_deriv_bound fs c hc hf x n
  rw [hA.deriv]
  exact hB

/-- **Évanouissement exponentiel** : pour une contraction stricte `c < 1`, la
borne `c ^ n` tend vers `0` — la profondeur tue le gradient à vitesse
géométrique, ce que le notebook 4.2-ConvNet mesure à `c ≈ 0,4` (pente droite en
échelle semilog). -/
theorem plainStack_gradient_vanishes (hc : 0 ≤ c) (h1 : c < 1) :
    Filter.Tendsto (fun n => c ^ n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by rwa [abs_of_nonneg hc])

/-- **Ancre numérique du cours** (notebook `4.2-ConvNet-Profonde-Residuelles`,
§3) : à facteur `0,4` par bloc, 20 blocs laissent passer moins d'un
dix-millionième du gradient — `0,4 ^ 20 ≈ 1,1e-8 < 1e-7`. -/
theorem two_fifths_pow_twenty_lt : (2 / 5 : ℝ) ^ 20 < 1 / 10 ^ 7 := by norm_num

end GradientFlow
