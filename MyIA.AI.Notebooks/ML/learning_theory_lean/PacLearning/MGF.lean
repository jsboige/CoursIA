import Mathlib
import PacLearning.Data
import PacLearning.Sample
import PacLearning.Concentration

/-!
# PacLearning.MGF — fonction génératrice de moments de l'indicateur (brique 2c/3-hoeffding-2a/5)

Sous-module de `PacLearning` : outil analytique de la concentration de Hoeffding.
La chaîne Hoeffding pour la moyenne d'indicateurs i.i.d. repose sur la
**fonction génératrice de moments (MGF)** de l'indicateur centré :

    E_D [ exp (t · (ind(x) − μ)) ]   où  ind(x) = 𝟙{h(x) ≠ f(x)},  μ = trueError = E_D[ind].

Ce livrable pose la **réduction algébrique** (brique 2a/5) : on ramène cette MGF
discrète à une **forme fermée** ne dépendant que de `μ` et `t` :

    E_D [ exp (t · (ind − μ)) ] = μ · exp(t·(1−μ)) + (1−μ) · exp(−t·μ).

L'idée : `ind(x) ∈ {0,1}`, donc `exp(t·(ind−μ)) = exp(t(1−μ))·ind + exp(−tμ)·(1−ind)`
point par point (si `ind = 1`, on lit `exp(t(1−μ))` ; si `ind = 0`, `exp(−tμ)`). On
distribue ensuite l'espérance (`expect_linear`) : `E[ind] = μ` (`trueError_eq_expect`),
`E[1 − ind] = 1 − μ` (`expect_sub` + `expect_const` + `D.sum_one`).

C'est un ingrédient **algébrique** (0 analyse) préparant la **borne finale**
`bernoulli_mgf_le : μ·exp(t(1−μ)) + (1−μ)·exp(−tμ) ≤ exp(t²/8)` (lemme de Hoeffding,
brique 2b/5 — cœur d'analytique dur, cycle dédié). On reste en style **ℝ-weight
pédagogique** : la MGF est `expect D (fun x ↦ exp(t·(...)))`, somme pondérée sur `D`.
-/

namespace PacLearning

open Finset
open scoped Classical

variable {X : Type*} [Fintype X]
variable (D : Distribution X)
variable {D}

/-- **Espérance d'une différence point par point** : `E_D[g − ind] = E_D[g] − E_D[ind]`
(somme pondérée des différences = différence des sommes pondérées, via
`Finset.sum_sub_distrib`). Variante soustractive de `expect_linear`, réutilisée par
`expect_exp_centered_eq` pour `E_D[1 − ind] = 1 − trueError`. -/
theorem expect_sub (g₁ g₂ : X → ℝ) :
    expect D (fun x ↦ g₁ x - g₂ x) = expect D g₁ - expect D g₂ := by
  dsimp only [expect, expect]
  simp only [mul_sub]
  rw [← Finset.sum_sub_distrib]

/-- **Réduction algébrique de la MGF de l'indicateur centré** : pour `ind(x) = 𝟙{h≠f}`
et `μ = trueError`, la fonction génératrice de moments se ramène à une forme fermée.

    E_D [ exp (t · (ind(x) − μ)) ] = μ · exp(t·(1−μ)) + (1−μ) · exp(−t·μ).

C'est la **brique 2a/5** de la concentration de Hoeffding : purement algébrique
(Fubini sur la partition `{ind = 1}` / `{ind = 0}`), sans aucune analyse. C'est
l'ingrédient exact requis par la borne finale `bernoulli_mgf_le` (brique 2b/5, OPEN)
qui montrera que cette forme fermée est `≤ exp(t²/8)`.

Preuve : point par point, `exp(t·(ind−μ)) = exp(t(1−μ))·ind + exp(−tμ)·(1−ind)` (car
`ind ∈ {0,1}` : cas `ind = 1` ⟹ `exp(t(1−μ))` ; cas `ind = 0` ⟹ `exp(−tμ)`). On
distribue alors l'espérance (`expect_linear`) : `E[ind] = μ` (`trueError_eq_expect`) et
`E[1 − ind] = 1 − μ` (`expect_sub` + `expect_const`). -/
theorem expect_exp_centered_eq (f h : Hypothesis X) (t : ℝ) :
    expect D (fun x ↦ Real.exp (t * ((if h x ≠ f x then (1 : ℝ) else 0) - trueError D f h))) =
      trueError D f h * Real.exp (t * (1 - trueError D f h)) +
        (1 - trueError D f h) * Real.exp (-(t * trueError D f h)) := by
  set μ := trueError D f h
  -- (1) Identité point-par-point : `exp(t·(ind−μ)) = exp(t(1−μ))·ind + exp(−tμ)·(1−ind)`,
  -- car `ind ∈ {0,1}` (constante `exp(...)` à GAUCHE pour que `expect_linear` matche).
  -- Les arguments `exp` ne sont pas defeq entre branches (`t*(0−μ)` vs `−(t*μ)`), d'où
  -- le `congr 1; ring` final pour égaliser les arguments sous l'exponentielle.
  have hind : ∀ x : X,
      Real.exp (t * ((if h x ≠ f x then (1 : ℝ) else 0) - μ)) =
        Real.exp (t * (1 - μ)) * (if h x ≠ f x then (1 : ℝ) else 0) +
          Real.exp (-(t * μ)) * (1 - (if h x ≠ f x then (1 : ℝ) else 0)) := by
    intro x
    by_cases hx : h x ≠ f x
    · -- `ind x = 1` : `exp(t(1−μ))·1 + exp(−tμ)·0 = exp(t(1−μ))`.
      simp only [if_pos hx, mul_one, mul_zero, sub_self, add_zero]
    · -- `ind x = 0` : `exp(t(0−μ)) = exp(t(1−μ))·0 + exp(−tμ)·(1−0) = exp(−tμ)`.
      -- simp réduit ifs + algèbre ; `Real.exp` n'est pas traité par `ring`, d'où le
      -- `congr 1` (peel exp) puis `ring` sur l'argument `t*(0−μ) = −(t*μ)`.
      simp only [if_neg hx, mul_zero, mul_one, sub_zero, zero_add]
      congr 1
      ring
  -- (2) `E[ind] = μ` (l'espérance de l'indicateur est l'erreur vraie).
  have hind_exp : expect D (fun x ↦ if h x ≠ f x then (1 : ℝ) else 0) = μ :=
    (trueError_eq_expect (D := D) f h).symm
  -- (3) `E[1 − ind] = 1 − μ` (masse totale `1` moins la masse des erreurs).
  have hcompl_exp : expect D (fun x ↦ 1 - (if h x ≠ f x then (1 : ℝ) else 0)) = 1 - μ := by
    rw [expect_sub, expect_const, hind_exp]
  -- (4) Assemblage : identité point-par-point (`congr`+`ext`), puis `expect_linear`
  -- distribue chaque terme en un seul coup (constante à gauche), puis substitutions.
  calc expect D (fun x ↦ Real.exp (t * ((if h x ≠ f x then (1 : ℝ) else 0) - μ)))
      = expect D (fun x ↦
            Real.exp (t * (1 - μ)) * (if h x ≠ f x then (1 : ℝ) else 0) +
              Real.exp (-(t * μ)) * (1 - (if h x ≠ f x then (1 : ℝ) else 0))) := by
          congr 1; ext x; exact hind x
    _ = Real.exp (t * (1 - μ)) * expect D (fun x ↦ if h x ≠ f x then (1 : ℝ) else 0) +
          Real.exp (-(t * μ)) * expect D (fun x ↦ 1 - (if h x ≠ f x then (1 : ℝ) else 0)) := by
          rw [expect_linear]
    _ = Real.exp (t * (1 - μ)) * μ + Real.exp (-(t * μ)) * (1 - μ) := by
          rw [hind_exp, hcompl_exp]
    _ = μ * Real.exp (t * (1 - μ)) + (1 - μ) * Real.exp (-(t * μ)) := by
          rw [mul_comm (Real.exp (t * (1 - μ))) μ,
              mul_comm (Real.exp (-(t * μ))) (1 - μ)]

end PacLearning
