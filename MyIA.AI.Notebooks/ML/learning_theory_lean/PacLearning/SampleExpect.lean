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

## Ce livrable — estimateur non-biaisé (brique 2c/3)

On prouve l'**estimateur non-biaisé** `sampleExpect_empError_eq_trueError`
(`E_{S∼D^m}[empError f h S] = trueError D f h`) : l'erreur empirique, moyennée sur
les tirages i.i.d., coïncide avec l'erreur vraie (elle est **centrée** dessus).
C'est le second pilier de la concentration de Hoeffding. Preuve : `empError S =
n⁻¹ · (∑_i ind(S_i))` (`ind = 1_{h≠f}`) ; on sort le scalaire (`sampleExpect_smul`),
on distribue la somme (`sampleExpect_sum`), puis chaque indicateur marginalise en
`E_D[ind] = trueError` via `sampleExpect_coord` + `trueError_eq_expect` ;
`∑_i trueError = n · trueError` (`sum_const`), et `field_simp` annule `n⁻¹·n`.

## Briques restantes — OPEN (documentées comme travail futur, pas de stub)

- **Hoeffding-for-Bernoulli** : `ℙ_S [ |empError − trueError| ≥ ε ] ≤
  2·exp(−2nε²)` (méthode Chernoff : Markov sur `exp(t·(X̄−μ))` + `log t ≤ t−1`).
- **Borne finale** `pac_finite_class_bound` (brique 3/3, union bound sur `H` fini).

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

/-- **Factorisation d'un produit (indépendance i.i.d.)** : l'espérance (sous le
produit `D^m`) d'une fonction de la forme `∏_i h (S i)` — produit de fonctions
une-coordonnée, i.i.d. par construction de la distribution produit `D^m` — se
factorise en le produit des espérances `∏_i E_D[h]`. C'est la **brique 3/5
d'Hoeffding** (indépendance produit) : pour `h = exp(t · ind)`, elle donne
`E_S[exp(t · ∑_i ind(S_i))] = E_S[∏_i exp(t·ind(S_i))] = ∏_i E_D[exp(t·ind)]`,
c.-à-d. la **MGF d'une somme = produit des MGFs** — ingrédient-clé de la
concentration bilatérale de Hoeffding.

Preuve : même squelette que `sampleExpect_coord` — on porte `h` sur chaque
coordonnée via `g' j x = w x · h x`, de sorte que
`∏_j g' j (S j) = (∏_j w (S j)) · (∏_j h (S j))` (`Finset.prod_mul_distrib`),
puis `Fintype.prod_sum` échange produit-de-sommes et somme-de-produits :
`∑_S ∏_j g' j (S j) = ∏_j ∑_x g' j x = ∏_j E_D[h]`. Plus simple que
`sampleExpect_coord` : sans `if` (toutes les coordonnées portent `h`), donc pas
de réduction `Finset.prod_eq_single_of_mem`. -/
theorem sampleExpect_prod_coord {n : ℕ} (h : X → ℝ) :
    sampleExpect D (fun S : Fin n → X ↦ ∏ i, h (S i)) = ∏ _ : Fin n, expect D h := by
  dsimp only [sampleExpect, sampleWeight]
  -- `g'` porte `h` sur chaque coordonnée : `g' j x = w x · h x`.
  let g' : Fin n → X → ℝ := fun j x ↦ D.weight x * h x
  -- (1) `∏_j g' j (S j) = (∏_j w (S j)) * ∏_j h (S j)` : `prod_mul_distrib` sépare.
  have hprod : ∀ S : Fin n → X,
      ∏ j, g' j (S j) = (∏ j, D.weight (S j)) * ∏ j, h (S j) := by
    intro S
    simp only [g', Finset.prod_mul_distrib]
  -- (2) Le summand `(∏_j w (S j)) * ∏_j h (S j)` coïncide point par point avec `∏_j g' j (S j)`.
  rw [Finset.sum_congr rfl (fun S _ ↦ (hprod S).symm)]
  -- (3) Produit de sommes = somme de produits (`Fintype.prod_sum`) :
  -- `∑_S ∏_j g' j (S j) = ∏_j ∑_x g' j x`.
  rw [← Fintype.prod_sum (κ := fun _ : Fin n ↦ X) g']
  -- (4) `∑_x g' j x = ∑_x w x · h x = E_D[h]` (indépendant de `j`).
  have hsum : ∀ j, ∑ x, g' j x = expect D h := by
    intro j
    simp only [g', expect]
  simp only [hsum]

/-- **Linéarité en une somme indicée** : l'espérance empirique d'une somme de
fonctions est la somme des espérances (Fubini discret : `∑_S w S · (∑_i F i S) =
∑_i ∑_S w S · F i S` via `Finset.mul_sum` puis `Finset.sum_comm`). Réutilisé par
l'estimateur non-biaisé `sampleExpect_empError_eq_trueError`. -/
theorem sampleExpect_sum {ι : Type*} [Fintype ι] {n : ℕ} (F : ι → ((Fin n → X) → ℝ)) :
    sampleExpect D (fun S ↦ ∑ i, F i S) = ∑ i, sampleExpect D (F i) := by
  dsimp only [sampleExpect]
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-- **Linéarité en un facteur scalaire** : `E[c · g] = c · E[g]` (le scalaire sort
de la somme pondérée via `Finset.mul_sum`). Réutilisé par l'estimateur non-biaisé
(pour sortir le facteur `1/n` de l'erreur empirique). -/
theorem sampleExpect_smul {n : ℕ} (c : ℝ) (g : (Fin n → X) → ℝ) :
    sampleExpect D (fun S ↦ c * g S) = c * sampleExpect D g := by
  dsimp only [sampleExpect]
  simp only [show ∀ S, sampleWeight D S * (c * g S) = c * (sampleWeight D S * g S) from
               fun _ ↦ by ring]
  rw [← Finset.mul_sum]

/-- **Estimateur non-biaisé** : l'espérance (sous `D^m`) de l'erreur empirique
égale l'erreur vraie. C'est le fait que `empError` est un estimateur **non-biaisé**
de `trueError` : en moyenne sur les tirages `S ∼ D^m`, l'erreur empirique coïncide
avec l'erreur vraie (elle est **centrée** sur `trueError`).

Preuve : `empError S = (∑_i 1_{h(S_i)≠f(S_i)}) / n = n⁻¹ · (∑_i ind (S i))`. Par
`sampleExpect_smul` (sortir le `n⁻¹`), `sampleExpect_sum` (linéarité), puis
`sampleExpect_coord` (chaque indicateur marginalise en `E_D[ind] = trueError` via
`trueError_eq_expect`), on obtient
`E_S[empError] = n⁻¹ · (∑_i trueError) = n⁻¹ · (n · trueError) = trueError`. -/
theorem sampleExpect_empError_eq_trueError {n : ℕ} (f h : Hypothesis X) (hn : 0 < n) :
    sampleExpect D (fun S : Fin n → X ↦ empError f h S) = trueError D f h := by
  -- Indicateur de mauvaise classification d'une instance.
  let ind : X → ℝ := fun x ↦ if h x ≠ f x then 1 else 0
  -- (1) `empError f h S = (n:ℝ)⁻¹ · (∑ i, ind (S i))` (réécriture du `1/n`).
  have h_emp : ∀ S : Fin n → X,
      empError f h S = (n : ℝ)⁻¹ * (∑ i : Fin n, ind (S i)) := by
    intro S
    dsimp only [empError, ind]
    field_simp
  -- (2) Per-coordinate marginal : `E_S[ind (S i)] = E_D[ind]` (sampleExpect_coord,
  -- D implicite → named arg `(D := D)` car D n'apparaît que dans le goal).
  have h_coord : ∀ i : Fin n, sampleExpect D (fun S ↦ ind (S i)) = expect D ind := by
    intro i
    exact sampleExpect_coord (D := D) ind i
  -- (3) `expect D ind = trueError D f h`.
  have h_true : expect D ind = trueError D f h := (trueError_eq_expect (D := D) f h).symm
  -- (4) `n > 0` (en ℝ) pour le field_simp final.
  have hnreal : (0 : ℝ) < n := mod_cast hn
  calc sampleExpect D (fun S : Fin n → X ↦ empError f h S)
      = sampleExpect D (fun S ↦ (n : ℝ)⁻¹ * (∑ i : Fin n, ind (S i))) := by
          simp only [h_emp]
    _ = (n : ℝ)⁻¹ * sampleExpect D (fun S ↦ ∑ i : Fin n, ind (S i)) := by
          rw [sampleExpect_smul]
    _ = (n : ℝ)⁻¹ * ∑ i : Fin n, sampleExpect D (fun S ↦ ind (S i)) := by
          rw [sampleExpect_sum]
    _ = (n : ℝ)⁻¹ * ∑ i : Fin n, expect D ind := by
          congr 1
          exact Finset.sum_congr rfl (fun i _ ↦ h_coord i)
    _ = (n : ℝ)⁻¹ * ∑ i : Fin n, trueError D f h := by rw [h_true]
    _ = (n : ℝ)⁻¹ * (n * trueError D f h) := by
          congr 1
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = trueError D f h := by
          field_simp

end PacLearning

