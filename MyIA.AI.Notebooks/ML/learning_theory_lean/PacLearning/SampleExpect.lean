import Mathlib
import PacLearning.Data
import PacLearning.Sample
import PacLearning.Concentration

/-!
# PacLearning.SampleExpect — espérance empirique sur l'espace des échantillons

Sous-module de `PacLearning` : la **brique 2b/3** d'iter-2. On prolonge le cadre
d'espérance de `Concentration.lean` (qui définissait `expect D g` sur `X`) vers
l'**espace des échantillons** `Fin n → X` muni de la distribution produit `D^m`
(voir `Sample.lean`). L'espérance empirique d'une fonction `g : (Fin n → X) → ℝ`
est la somme pondérée

    sampleExpect D g = ∑ S, sampleWeight D S · g S.

## Ce livrable (brique 2b/3) — le cadre d'espérance empirique

On pose `sampleExpect` et ses propriétés **élémentaires (entièrement prouvées)** : non-négativité
(`sampleExpect_nonneg`), linéarité (`sampleExpect_linear`), et surtout la
**normalisation** `sampleExpect_const` (`E_{S∼D^m}[constante c] = c`, via
`sampleWeight_sum_one` — `D^m` est bien une distribution de probabilité). Plus la
**monotonie** (`sampleExpect_mono`). C'est le prolongement naturel de `expect`
vers l'espace produit, cadre requis par toute inégalité de concentration sur
l'échantillon.

## Briques 2c/3 et 3/3 — OPEN (documentées comme travail futur, pas de stub)

Les résultats plus profonds nécessitent la **marginalisation d'une coordonnée**
sous le produit `D^m` (le bloc-clé), qu'on escompte via le lemme Mathlib
`Finset.sum_prod_piFinset` (`∑_{f ∈ piFinset} ∏_i g i (f i) = ∏_i ∑_j g i j`,
avec un `g` portant le facteur à la coordonnée d'intérêt) :

- **Marginalisation** `sampleExpect_coord` : `E_{S∼D^m}[g (S i)] = E_D[g]`.
- **Estimateur non-biaisé** `sampleExpect_empError_eq_trueError` :
  `E_{S∼D^m}[empError f h S] = trueError D f h` (par linéarité + marginalisation ;
  l'erreur empirique est centrée sur l'erreur vraie).
- **Hoeffding-for-Bernoulli** : `ℙ_S [ |empError − trueError| ≥ ε ] ≤
  2·exp(−2nε²)` (méthode Chernoff : Markov sur `exp(t·(X̄−μ))` + `log t ≤ t−1`).

Ces briques suivent en itérations dédiées (la formalisation de la
marginalisation coordonnée-par-coordonnée sur les types Pi est subtile). On
reste dans le style **ℝ-weight pédagogique** (pas de `ℝ≥0∞` / `Measure`).
-/

namespace PacLearning

open Finset

variable {X : Type*} [Fintype X]
variable (D : Distribution X)

/-- **Espérance empirique** de `g : (Fin n → X) → ℝ` sous la distribution produit
`D^m` : somme pondérée `∑ S, sampleWeight D S · g S`. C'est le prolongement de
`expect` (sur `X`) à l'espace des échantillons. -/
noncomputable def sampleExpect {n : ℕ} (g : (Fin n → X) → ℝ) : ℝ :=
  ∑ S : Fin n → X, sampleWeight D S * g S

variable {D}

/-- L'espérance empirique d'une fonction positive est positive : somme de poids
positifs (`sampleWeight ≥ 0`) fois `g ≥ 0`. -/
theorem sampleExpect_nonneg {n : ℕ} {g : (Fin n → X) → ℝ} (hg : ∀ S, 0 ≤ g S) :
    0 ≤ sampleExpect D g := by
  dsimp only [sampleExpect]
  apply sum_nonneg
  intro S _
  exact mul_nonneg (sampleWeight_nonneg (D := D) S) (hg S)

/-- L'espérance empirique est linéaire en `g` : `E[a·g₁ + b·g₂] = a·E[g₁] + b·E[g₂]`
(car `∑` l'est). Le facteur `a` (resp. `b`) est ramené à gauche dans chaque
produit scalaire pondéré, puis `← mul_sum` le sort de la somme. -/
theorem sampleExpect_linear {n : ℕ} {g₁ g₂ : (Fin n → X) → ℝ} (a b : ℝ) :
    sampleExpect D (fun S ↦ a * g₁ S + b * g₂ S) =
      a * sampleExpect D g₁ + b * sampleExpect D g₂ := by
  dsimp only [sampleExpect]
  simp only [mul_add, Finset.sum_add_distrib]
  simp only [show ∀ S, sampleWeight D S * (a * g₁ S) = a * (sampleWeight D S * g₁ S) from
               fun _ => by ring,
             show ∀ S, sampleWeight D S * (b * g₂ S) = b * (sampleWeight D S * g₂ S) from
               fun _ => by ring]
  rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- **Normalisation** : l'espérance empirique de la fonction constante `c` vaut
`c` (la masse totale des échantillons vaut `1` par `sampleWeight_sum_one`).
C'est le fait que `D^m` est une distribution de probabilité, transposé aux
espérances. -/
theorem sampleExpect_const (n : ℕ) (c : ℝ) :
    sampleExpect D (fun _ : Fin n → X ↦ c) = c := by
  dsimp only [sampleExpect]
  rw [← Finset.sum_mul, sampleWeight_sum_one n, one_mul]

/-- **Monotonie** de l'espérance empirique : si `g ≤ g'` point par point, alors
`E[g] ≤ E[g']` (somme pondérée de poids positifs). -/
theorem sampleExpect_mono {n : ℕ} {g g' : (Fin n → X) → ℝ}
    (h : ∀ S, g S ≤ g' S) : sampleExpect D g ≤ sampleExpect D g' := by
  dsimp only [sampleExpect]
  apply sum_le_sum
  intro S _
  exact mul_le_mul_of_nonneg_left (h S) (sampleWeight_nonneg (D := D) S)

end PacLearning
