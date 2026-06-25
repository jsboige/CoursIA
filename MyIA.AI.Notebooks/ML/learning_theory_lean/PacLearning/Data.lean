import Mathlib

/-!
# PacLearning.Data — modèle PAC : espace d'instances, distribution, erreurs

Cadre **PAC** (Valiant 1984, *A theory of the learnable*) pour une classe
d'hypothèses finie. On pose le modèle probabiliste sur un type d'instances fini
`X` : une **distribution** (fonction de poids normalisée `D : X → ℝ`,
`∑ D x = 1`, `D ≥ 0`), un **concept cible** `f : X → Bool` et une **hypothèse**
`h : X → Bool`.

- **Erreur vraie** `trueError D f h := ∑ x, if h x ≠ f x then D.weight x else 0` —
  masse (sous `D`) des instances mal classées par `h` (vs le concept `f`).
- **Erreur empirique** `empError f h S` — proportion d'erreurs de `h` sur un
  échantillon `S : Fin n → X`.

On évite délibérément la machinerie `ℝ≥0∞` / `Measure` : pour un type d'instances
fini, la fonction de poids normalisée en `ℝ` suffit et garde le modèle lisible.
C'est le pendant discret de `PMF.toMeasure`, adapté à la pédagogie de la borne.

Ce premier livrable pose le **modèle** et les **propriétés élémentaires** des
erreurs (bornes `[0, 1]`, erreur nulle quand `h = f`). La **borne de complexité
d'échantillon** `pac_finite_class_bound` (Hoeffding sur l'erreur empirique +
union bound sur la classe finie ⟹ `m ≥ (1/ε)(ln|H| + ln(1/δ))`) est **itération 2+**
— documentée OPEN, pas sorry-backed.
-/

namespace PacLearning

open Finset

variable {X : Type*} [Fintype X]

/-- Une distribution de probabilité sur `X` (fini) : fonction de poids normalisée.
On évite la machinerie `ℝ≥0∞` / `Measure` pour garder le modèle pédagogique en `ℝ`. -/
structure Distribution (X : Type*) [Fintype X] where
  /-- Poids de chaque instance. -/
  weight : X → ℝ
  /-- Les poids sont positifs. -/
  nonneg : ∀ x, 0 ≤ weight x
  /-- La masse totale vaut 1. -/
  sum_one : ∑ x, weight x = 1

/-- Les hypothèses et le concept cible sont des fonctions `X → Bool`
(étiquettes binaires `±1`). -/
abbrev Hypothesis (X : Type*) := X → Bool

variable (D : Distribution X) (f h : Hypothesis X)

/-- **Erreur vraie** de `h` (vs concept `f`) sous la distribution `D` :
masse des instances mal classées (`h x ≠ f x`). -/
def trueError : ℝ :=
  ∑ x, if h x ≠ f x then D.weight x else 0

variable {D f h}

/-- L'erreur vraie est positive (somme de poids positifs et de zéros). -/
theorem trueError_nonneg : 0 ≤ trueError D f h := by
  dsimp only [trueError]
  apply sum_nonneg
  intro x _
  by_cases hx : h x ≠ f x
  · rw [if_pos hx]; exact D.nonneg x
  · rw [if_neg hx]

/-- Une hypothèse qui coïncide avec le concept (`h = f`) a une erreur vraie nulle. -/
theorem trueError_self : trueError D f f = 0 := by
  dsimp only [trueError]
  simp

/-- L'erreur vraie est au plus `1` (la masse totale de `D` vaut `1`). -/
theorem trueError_le_one : trueError D f h ≤ 1 := by
  dsimp only [trueError]
  calc (∑ x, if h x ≠ f x then D.weight x else 0)
      ≤ ∑ x, D.weight x := by
        apply sum_le_sum
        intro x _
        by_cases hx : h x ≠ f x
        · rw [if_pos hx]
        · rw [if_neg hx]; exact D.nonneg x
    _ = 1 := D.sum_one

/-- L'erreur vraie de `h` (vs `f`) égale celle de `f` (vs `h`) : la relation
« mal classé » est symétrique. -/
theorem trueError_comm : trueError D f h = trueError D h f := by
  dsimp only [trueError]
  apply congr_arg
  ext x
  by_cases hx : h x ≠ f x
  · rw [if_pos hx, if_pos (ne_comm.mp hx)]
  · rw [if_neg hx, if_neg (fun h' => hx (ne_comm.mp h'))]

section Empirical

/-- **Erreur empirique** de `h` sur l'échantillon `S : Fin n → X` : proportion
des `n` exemples mal classés. -/
noncomputable def empError (f h : Hypothesis X) {n : ℕ} (S : Fin n → X) : ℝ :=
  (∑ i : Fin n, if h (S i) ≠ f (S i) then (1 : ℝ) else 0) / n

/-- L'erreur empirique est positive (numerateur positif, dénominateur strictement
positif). -/
theorem empError_nonneg (f h : Hypothesis X) {n : ℕ} (S : Fin n → X) (hn : 0 < n) :
    0 ≤ empError f h S := by
  dsimp only [empError]
  apply div_nonneg
  · apply sum_nonneg
    intro i _
    by_cases hi : h (S i) ≠ f (S i)
    · rw [if_pos hi]; norm_num
    · rw [if_neg hi]
  · exact_mod_cast hn.le

end Empirical

end PacLearning
