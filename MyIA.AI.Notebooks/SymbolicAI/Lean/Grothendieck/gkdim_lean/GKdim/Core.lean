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
les monômes de degré au plus `n` sont `1, X, …, X^n` : il y en a `n + 1`. -/
def hilbert_poly1 (n : ℕ) : ℕ := n + 1

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
