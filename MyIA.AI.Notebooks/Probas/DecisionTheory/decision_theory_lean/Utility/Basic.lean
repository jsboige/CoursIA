import Mathlib

/-!
# Définitions de base — Loteries et espérance

Types fondamentaux de la théorie de la décision en univers risqué :
loteries (distributions de probabilité à support fini sur un espace
d'issues fini), espérance d'une fonction d'utilité, et mélanges convexes
de loteries.

Ces primitives servent de base aux axiomes de von Neumann–Morgenstern et
au théorème de représentation de l'utilité espérée (voir `Axioms` et
`Representation`).

Convention i18n (EPIC #4980, PR pilote #5303) : FR-first appliqué sur les
en-têtes et docstrings publics. Le code tactique et les commentaires
intra-preuve restent en anglais (références Mathlib, notation formelle).

Références croisées :
- Infer-14 (Infer.NET) : utilité espérée bayésienne sous incertitude sur la postérieure.
- PyMC-1 (PyMC) : estimation de l'utilité espérée par échantillonnage postérieur.
-/

namespace Utility

variable {α : Type*} [Fintype α]

/-- Une loterie est une attribution de poids non négatifs à chaque issue,
sommant à 1. De manière équivalente, une distribution de probabilité à
support fini sur le type d'issues `α`. -/
structure Lottery (α : Type*) [Fintype α] where
  /-- Poids de probabilité de chaque issue. -/
  probs : α → ℝ
  /-- Chaque poids est non négatif. -/
  nonneg : ∀ a : α, 0 ≤ probs a
  /-- Les poids somment à un (normalisation). -/
  sum_one : ∑ a : α, probs a = 1

/-- L'espérance d'une fonction `f` (typiquement une fonction d'utilité) sous
la distribution `p`. -/
def expectation (p : Lottery α) (f : α → ℝ) : ℝ :=
  ∑ a : α, p.probs a * f a

/-- Le mélange `t • p + (1 - t) • r` de deux loteries. Défini pour `t ∈ [0,1]`,
ce qui garantit que le mélange est à nouveau une loterie valide. -/
def mix (t : ℝ) (p r : Lottery α) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Lottery α where
  probs a := t * p.probs a + (1 - t) * r.probs a
  nonneg a := by
    refine add_nonneg ?_ ?_
    · exact mul_nonneg ht0 (p.nonneg a)
    · exact mul_nonneg (by linarith) (r.nonneg a)
  sum_one := by
    have key :
      ∑ a : α, (t * p.probs a + (1 - t) * r.probs a) =
        t * ∑ a : α, p.probs a + (1 - t) * ∑ a : α, r.probs a := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [key, p.sum_one, r.sum_one]
    ring

/-- Linéarité de l'espérance sous les mélanges : l'utilité espérée d'un mélange
est le mélange correspondant des utilités espérées. Cette identité affine est le
cœur algébrique de l'axiome d'indépendance. -/
theorem expectation_mix (t : ℝ) (p r : Lottery α) (f : α → ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    expectation (mix t p r ht0 ht1) f = t * expectation p f + (1 - t) * expectation r f := by
  simp only [expectation, mix]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun a _ => by ring)

/-- L'utilité espérée est additive en la fonction d'utilité. -/
theorem expectation_add (p : Lottery α) (f g : α → ℝ) :
    expectation p (fun a => f a + g a) = expectation p f + expectation p g := by
  simp only [expectation]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun a _ => by ring)

/-- L'utilité espérée est homogène en la fonction d'utilité. -/
theorem expectation_smul (c : ℝ) (p : Lottery α) (f : α → ℝ) :
    expectation p (fun a => c * f a) = c * expectation p f := by
  simp only [expectation]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun a _ => by ring)

/-- L'espérance d'une utilité constante est cette constante (les poids somment à un). -/
theorem expectation_const (p : Lottery α) (c : ℝ) :
    expectation p (fun _ => c) = c := by
  simp only [expectation]
  rw [← Finset.sum_mul, p.sum_one]
  ring

/-- L'espérance est affine en l'utilité : `E_p[a·u + b] = a·E_p[u] + b`. C'est
l'identité clé qui sous-tend l'unicité affine des représentations d'utilité. -/
theorem expectation_affine (p : Lottery α) (a b : ℝ) (u : α → ℝ) :
    expectation p (fun x => a * u x + b) = a * expectation p u + b := by
  rw [expectation_add p (fun x => a * u x) (fun _ => b), expectation_smul, expectation_const]

end Utility
