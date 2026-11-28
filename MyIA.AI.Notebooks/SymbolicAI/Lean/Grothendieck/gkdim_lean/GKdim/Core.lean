/-
Dimension de Gelfand-Kirillov — lemmes de croissance jouables.

Compagnon du carnet GROTH-07. Ce fichier ne formalise pas le théorème du trou
de Smoktunowicz (ce serait un projet à part entière — cf. l'article de la
bibliographie) : il établit le cas élémentaire et jouable, sur lequel s'appuie
l'intuition du carnet. L'anneau polynomial à une variable, muni de sa
gradation standard par `ℕ`, croît exactement comme `n` ; sa dimension de
Gelfand-Kirillov est donc `1`.
-/
import Mathlib

open Nat

namespace GKdim

variable {K : Type*} [Field K]

/-- Fonction de Hilbert de `K[X]` (gradation standard par `ℕ`) : dimension du
sous-espace vectoriel des polynômes de degré total au plus `n`. En une variable,
les monômes de degré au plus `n` sont `1, X, …, X^n` : il y en a `n + 1`.

Ce n'est plus une suite choisie à la main : `hilbert_poly1_space_equiv` identifie
l'espace `K[X]_{< n + 1}` à `Fin (n+1) → K`, et `hilbert_poly1_eq_finrank` prouve
que `hilbert_poly1 n` est le rang fini de cet espace. La définition reste
**calculable** — le rang de Mathlib ne l'est pas — ce qui permet au carnet
d'évaluer la suite sur les premiers degrés. -/
def hilbert_poly1 (n : ℕ) : ℕ := n + 1

/-- L'espace `K[X]_{< n + 1}` des polynômes de degré strictement inférieur à
`n + 1` — c'est-à-dire de degré au plus `n` — est `K`-isomorphe à `Fin (n+1) → K` :
c'est l'identification `Polynomial.degreeLTEquiv` de Mathlib, qui lit les
coefficients. -/
noncomputable def hilbert_poly1_space_equiv (n : ℕ) :
    Polynomial.degreeLT K (n + 1) ≃ₗ[K] Fin (n + 1) → K :=
  Polynomial.degreeLTEquiv K (n + 1)

/-- La fonction de Hilbert est le rang fini de l'espace `K[X]_{< n + 1}` : par
l'isomorphisme ci-dessus et `Module.finrank_fin_fun`, ce rang vaut `n + 1`,
c'est-à-dire `hilbert_poly1 n`. C'est le lien formel qui manquait entre la suite
et l'espace vectoriel qu'elle annonce mesurer. -/
theorem hilbert_poly1_eq_finrank (n : ℕ) :
    Module.finrank K (Polynomial.degreeLT K (n + 1)) = hilbert_poly1 n := by
  rw [LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv K (n + 1))]
  rw [Module.finrank_fin_fun K]
  rfl

/-- Une suite `G : ℕ → ℕ` est de croissance polynomiale de degré **au plus**
`d` s'il existe une constante `C` et un seuil `n₀` tels que `G n ≤ C * n ^ d`
pour tout `n ≥ n₀`. -/
def growthAtMost (G : ℕ → ℕ) (d : ℕ) : Prop :=
  ∃ C n₀, ∀ n ≥ n₀, G n ≤ C * n ^ d

/-- ... et de degré **au moins** `d` s'il existe `c > 0` et un seuil `n₀` tels
que `G n ≥ c * n ^ d` pour tout `n ≥ n₀`. -/
def growthAtLeast (G : ℕ → ℕ) (d : ℕ) : Prop :=
  ∃ c n₀, 0 < c ∧ ∀ n ≥ n₀, G n ≥ c * n ^ d

/-- La croissance de `K[X]` est bornée au-dessus par un multiple de `n`. -/
theorem poly1_growthAtMost : growthAtMost hilbert_poly1 1 := by
  use 2, 1
  intro n hn
  simp only [hilbert_poly1, pow_one]
  omega

/-- ... et bornée en-dessous par `n` (le terme dominant). -/
theorem poly1_growthAtLeast : growthAtLeast hilbert_poly1 1 := by
  use 1, 1
  constructor
  · omega
  · intro n hn
    simp only [hilbert_poly1, pow_one, one_mul]
    omega

/-- L'énoncé jouable : la dimension de Gelfand-Kirillov de `K[X]` est `1`,
caractérisée par les deux bornes de croissance ci-dessus (croissance
exactement linéaire). -/
theorem poly1_gkdim_is_one :
    growthAtMost hilbert_poly1 1 ∧ growthAtLeast hilbert_poly1 1 :=
  ⟨poly1_growthAtMost, poly1_growthAtLeast⟩

end GKdim
