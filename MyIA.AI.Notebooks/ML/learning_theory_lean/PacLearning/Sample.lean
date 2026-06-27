import Mathlib
import PacLearning.Data

/-!
# PacLearning.Sample — distribution produit sur l'espace des échantillons

Sous-module de `PacLearning` : on munit l'espace des **échantillons**
`Fin n → X` (suites de `n` instances tirées i.i.d. selon `D`) d'une **distribution
produit** `D^m`, pendant discret du produit tensoriel de mesures. C'est le cadre
probabiliste requis par la borne de complexité d'échantillon
`pac_finite_class_bound` (itération 2+) : la concentration de l'erreur empirique
se démontre sur des tirages indépendants `S ∼ D^m`.

On reste dans le style **ℝ-weight pédagogique** (pas de `ℝ≥0∞` / `Measure`) :
le poids d'un échantillon `S` est le produit des poids de ses composantes,

    sampleWeight D S = ∏ i : Fin n, D.weight (S i),

et la **normalisation** `∑ S, sampleWeight D S = 1` (lemme `sampleWeight_sum_one`)
garantit que `D^m` est bien une distribution. La preuve = identité de Fubini
discrète `(∑ x, w x)^n = ∑ S, ∏ i, w (S i)`, disponible dans Mathlib comme
`sum_pow'` (développement multinomial : produit de sommes sur type fini).

Ce livrable est la **brique 1/3** d'iter-2 : le modèle d'échantillon + sa
distribution produit. La concentration de Hoeffding-for-Bernoulli (brique 2/3)
et la borne finale `pac_finite_class_bound` (brique 3/3) suivent.
-/

namespace PacLearning

open Finset

variable {X : Type*} [Fintype X]
variable (D : Distribution X)

/-- **Poids d'un échantillon** `S : Fin n → X` sous la distribution produit `D^m` :
produit des poids de ses composantes. C'est le pendant discret de la densité du
produit tensoriel `D ⊗ … ⊗ D`. -/
def sampleWeight {n : ℕ} (S : Fin n → X) : ℝ :=
  ∏ i : Fin n, D.weight (S i)

variable {D}

/-- Le poids d'un échantillon est positif : produit de poids positifs (`D.nonneg`).
Cas `n = 0` (échantillon vide) : produit vide = `1 ≥ 0`. -/
theorem sampleWeight_nonneg {n : ℕ} (S : Fin n → X) : 0 ≤ sampleWeight D S := by
  dsimp only [sampleWeight]
  apply prod_nonneg
  intro i _
  exact D.nonneg (S i)

/-- La masse totale des échantillons de taille `n` vaut `1` : `D^m` est une
distribution. Identité de Fubini discrète `(∑ x, D.weight x)^n = ∑ S, ∏ i,
D.weight (S i)` (lemme Mathlib `sum_pow'`), puis `D.sum_one`. -/
theorem sampleWeight_sum_one (n : ℕ) : ∑ S : Fin n → X, sampleWeight D S = 1 := by
  dsimp only [sampleWeight]
  -- Fubini discret : (∑ x, w x)^n = ∑ S, ∏ i, w (S i).
  have hfubini : (∑ x, D.weight x) ^ n = ∑ S : Fin n → X, ∏ i, D.weight (S i) := by
    have h := sum_pow' (univ : Finset X) D.weight n
    simpa using h
  rw [← hfubini, D.sum_one, one_pow]

end PacLearning
