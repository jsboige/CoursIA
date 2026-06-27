import Mathlib
import PacLearning.Data
import PacLearning.Sample

/-!
# PacLearning.Concentration — espérance et inégalité de Markov (ℝ-weight)

Sous-module de `PacLearning` : la **brique 2a/3** d'iter-2. On définit l'**espérance**
d'une fonction `g : X → ℝ` sous la distribution `D`, puis l'**inégalité de Markov**
en ℝ-weight. Ces deux outils sont les fondations de la méthode de Chernoff
(Hoeffding-for-Bernoulli, brique 2b/3) puis de la borne `pac_finite_class_bound`
(brique 3/3).

On reste dans le style **ℝ-weight pédagogique** de `Data.lean` / `Sample.lean` :
l'espérance est la somme pondérée `∑ x, D.weight x * g x`, sans la machinerie
`ℝ≥0∞` / `Measure` / `Kernel` de Mathlib. Les *lemmes* Mathlib sont réutilisés
(`Finset.sum_*`, `log_le_sub_one_of_pos`, `convexOn_exp`) mais pas le *cadre*
`HasSubgaussianMGF` + `iIndepFun` — disproportionné pour le modèle discret.

## Espérance et lien avec `trueError`

L'erreur vraie `trueError D f h` se reformule comme espérance de l'indicateur de
mauvaise classification : `trueError D f h = expect D (fun x ↦ if h x ≠ f x then
1 else 0)`. C'est le pont entre le modèle de `Data.lean` et l'analyse de
concentration.
-/

namespace PacLearning

open Finset

variable {X : Type*} [Fintype X]
variable (D : Distribution X)

/-- **Espérance** de `g : X → ℝ` sous la distribution `D` : somme pondérée.
C'est le pendant discret de l'intégrale `∫ g dD`. -/
noncomputable def expect (g : X → ℝ) : ℝ :=
  ∑ x, D.weight x * g x

variable {D}

/-- L'espérance d'une fonction positive est positive : somme de poids positifs
(`≥ 0`) fois `g ≥ 0`. -/
theorem expect_nonneg {g : X → ℝ} (hg : ∀ x, 0 ≤ g x) : 0 ≤ expect D g := by
  dsimp only [expect]
  apply sum_nonneg
  intro x _
  exact mul_nonneg (D.nonneg x) (hg x)

/-- L'espérance est linéaire en `g` : `E[a·g + b] = a·E[g] + b` (car `∑` l'est). -/
theorem expect_linear {g₁ g₂ : X → ℝ} (a b : ℝ) : expect D (fun x ↦ a * g₁ x + b * g₂ x) =
    a * expect D g₁ + b * expect D g₂ := by
  dsimp only [expect]
  simp only [mul_add, Finset.sum_add_distrib]
  -- Facteur `a` (resp. `b`) ramené à gauche dans chaque produit scalaire pondéré,
  -- puis `← mul_sum` le sort de la somme : `∑ (a·(w·g)) = a·∑ (w·g)`.
  simp only [show ∀ x, D.weight x * (a * g₁ x) = a * (D.weight x * g₁ x) from fun _ => by ring,
             show ∀ x, D.weight x * (b * g₂ x) = b * (D.weight x * g₂ x) from fun _ => by ring]
  rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- L'espérance de la fonction constante `c` vaut `c` : `∑ x, D.weight x * c = c`
(car la masse totale vaut `1`). -/
theorem expect_const (c : ℝ) : expect D (fun _ ↦ c) = c := by
  dsimp only [expect]
  -- `∑ (w·c) = (∑ w)·c` (sum_mul inversé), puis `∑ w = 1` et `1·c = c`.
  rw [← Finset.sum_mul, D.sum_one, one_mul]

/-- **Lien avec `trueError`** : l'erreur vraie est l'espérance de l'indicateur
de mauvaise classification `if h x ≠ f x then 1 else 0`. C'est le pont entre le
modèle de `Data.lean` et l'analyse de concentration. -/
theorem trueError_eq_expect (f h : Hypothesis X) :
    trueError D f h = expect D (fun x ↦ if h x ≠ f x then (1 : ℝ) else 0) := by
  dsimp only [expect, trueError]
  apply sum_congr rfl
  intro x _
  by_cases hx : h x ≠ f x
  · simp only [if_pos hx, mul_one]
  · simp only [if_neg hx, mul_zero]

/-- **Inégalité de Markov** (ℝ-weight) : pour `g ≥ 0` et `t > 0`,
`D-weight { x | t ≤ g x } ≤ E[g] / t`. Preuve : sur le filtre `{x | t ≤ g x}`
(implémenté comme `Finset.filter` — l'adhésion via `Finset.mem_filter` est plus
robuste que le `Set`-comprehension `.toFinset` dont le `Fintype ↑s` laisse une
métavariable d'univers) on a `t ≤ g` point par point, donc `t · D.weight ≤
D.weight · g` (poids `≥ 0`), d'où `t · ∑_{filtre} ≤ ∑_{filtre} D.weight · g ≤
∑_{tout} D.weight · g = E[g]`, et on divise par `t > 0`. -/
theorem markov_ineq {g : X → ℝ} (hg : ∀ x, 0 ≤ g x) {t : ℝ} (ht : 0 < t) :
    ∑ x ∈ Finset.filter (fun x => t ≤ g x) (Finset.univ : Finset X), D.weight x ≤
      expect D g / t := by
  dsimp only [expect]
  -- `le_div_iff₀` donne `(∑_F w) · t ≤ E[g]`, puis `sum_mul` distribue le `t`.
  rw [le_div_iff₀ ht, Finset.sum_mul]
  -- Étape 1 : terme à terme `w·t ≤ w·g` sur le filtre (`t ≤ g`, `w ≥ 0`).
  have hF : ∑ x ∈ Finset.filter (fun x => t ≤ g x) Finset.univ, D.weight x * t ≤
            ∑ x ∈ Finset.filter (fun x => t ≤ g x) Finset.univ, D.weight x * g x := by
    apply sum_le_sum
    intro x hx
    exact mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hx).2 (D.nonneg x)
  -- Étape 2 : `∑_F w·t ≤ ∑_F w·g ≤ ∑_all w·g = E[g]`.
  calc ∑ x ∈ Finset.filter (fun x => t ≤ g x) Finset.univ, D.weight x * t
      ≤ ∑ x ∈ Finset.filter (fun x => t ≤ g x) Finset.univ, D.weight x * g x := hF
    _ ≤ ∑ x, D.weight x * g x :=
        sum_le_univ_sum_of_nonneg (fun x => mul_nonneg (D.nonneg x) (hg x))

end PacLearning
