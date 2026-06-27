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

## Ce livrable — marginalisation d'une coordonnée (brique 2c/3, partiel)

On prouve la **marginalisation d'une coordonnée** `sampleExpect_coord`
(`E_{S∼D^m}[g (S i)] = E_D[g]`), le **bloc-clé** de l'estimateur non-biaisé. Il
exprime que marginaliser une coordonnée d'un produit `D^m` redonne `D`. Preuve :
on « porte » `g` sur la coordonnée `i` via `g' j x = w x · (if j = i then g x
else 1)`, de sorte que `∏_j g' j (S j) = (∏_j w (S j)) · g (S i)`
(`Finset.prod_mul_distrib` sépare, `prod_eq_single_of_mem` réduit le produit des
`if` à son seul terme non-trivial). Le **produit de sommes** `Fintype.prod_sum`
(namespace `Fintype`, pas `Finset` — les deux `prod_sum` coexistent) donne alors
`∑_S ∏_j g' j (S j) = ∏_j ∑_x g' j x`, et ce produit vaut
`(∑_x w·g) · (∑_x w)^{n−1} = E_D[g] · 1` (`D.sum_one`).

## Briques restantes — OPEN (documentées comme travail futur, pas de stub)

- **Estimateur non-biaisé** `sampleExpect_empError_eq_trueError` :
  `E_{S∼D^m}[empError f h S] = trueError D f h` (par linéarité + `sampleExpect_coord`
  coordonnée-par-coordonnée ; l'erreur empirique est centrée sur l'erreur vraie).
- **Hoeffding-for-Bernoulli** : `ℙ_S [ |empError − trueError| ≥ ε ] ≤
  2·exp(−2nε²)` (méthode Chernoff : Markov sur `exp(t·(X̄−μ))` + `log t ≤ t−1`).

Ces briques suivent en itérations dédiées. On reste dans le style
**ℝ-weight pédagogique** (pas de `ℝ≥0∞` / `Measure`).
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

/-- **Marginalisation d'une coordonnée** : l'espérance (sous le produit `D^m`)
d'une fonction `g` qui ne dépend que d'une seule coordonnée `S i` égale son
espérance (sous `D`). C'est le **bloc-clé de l'estimateur non-biaisé** : il
exprime que marginaliser une coordonnée d'un produit `D^m` redonne `D`.

Preuve : on « porte » `g` sur la coordonnée `i` via `g' j x = w x · (if j = i
then g x else 1)`, de sorte que `∏_j g' j (S j) = (∏_j w (S j)) · g (S i)` (le
produit des `if` ne garde que le terme `j = i`). Le lemme Mathlib `Finset.prod_sum`
donne alors `∑_S ∏_j g' j (S j) = ∏_j ∑_x g' j x`, et ce produit vaut
`(∑_x w·g) · (∑_x w)^{n−1} = E_D[g] · 1`. -/
theorem sampleExpect_coord {n : ℕ} (g : X → ℝ) (i : Fin n) :
    sampleExpect D (fun S : Fin n → X ↦ g (S i)) = expect D g := by
  dsimp only [sampleExpect, sampleWeight]
  -- `g'` porte `g` sur la coordonnée `i`, ailleurs facteur neutre `1`.
  let g' : Fin n → X → ℝ := fun j x ↦ D.weight x * (if j = i then g x else 1)
  -- (1) `∏_j g' j (S j) = (∏_j w (S j)) * g (S i)` : `prod_mul_distrib` sépare les
  -- deux facteurs, puis `prod_eq_single_of_mem` réduit le produit des `if`
  -- (un seul terme non-trivial en `j = i`) à `g (S i)`.
  have hprod : ∀ S : Fin n → X, ∏ j, g' j (S j) = (∏ j, D.weight (S j)) * g (S i) := by
    intro S
    simp only [g', Finset.prod_mul_distrib]
    rw [Finset.prod_eq_single_of_mem i (Finset.mem_univ _) (fun b _ hb ↦ if_neg hb),
        if_pos rfl]
  -- (2) Le summand `(∏_j w (S j)) * g (S i)` coïncide point par point avec `∏_j g' j (S j)`.
  rw [Finset.sum_congr rfl (fun S _ ↦ (hprod S).symm)]
  -- (3) Produit de sommes = somme de produits (`Fintype.prod_sum`, namespace `Fintype`)
  -- : `∑_S ∏_j g' j (S j) = ∏_j ∑_x g' j x`.
  rw [← Fintype.prod_sum (κ := fun _ : Fin n ↦ X) g']
  -- (4) `∑_x g' j x` : `j = i` ⟹ `E_D[g]` (`∑ w·g`), sinon ⟹ `∑ w = 1` (`D.sum_one`).
  have hsum : ∀ j, ∑ x, g' j x = if j = i then expect D g else 1 := by
    intro j
    by_cases hj : j = i
    · simp only [g', expect, if_pos hj]
    · simp only [g', if_neg hj, mul_one, D.sum_one]
  simp only [hsum]
  -- (5) `∏_j (if j = i then expect D g else 1) = expect D g` : un seul non-trivial.
  rw [Finset.prod_eq_single_of_mem i (Finset.mem_univ _) (fun b _ hb ↦ if_neg hb),
      if_pos rfl]

end PacLearning

