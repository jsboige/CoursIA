/-
# Le mémoire de 1859, face à Mathlib

Premier module du lake `riemann200_lean` (grain Lean n° 1 de l'EPIC #20403,
critère d'acceptation 2 : au moins un module avec `lake build SUCCESS` et
`distinct_code_sorry` nul).

Le mémoire de novembre 1859 — « Über die Anzahl der Primzahlen unter einer
gegebenen Größe », six pages — part de la fonction zêta d'Euler
`ζ(s) = Σ n⁻ˢ = Π (1 - p⁻ˢ)⁻¹` et lui donne trois destins : le prolongement
analytique, l'équation fonctionnelle, les zéros. Ce module rassemble ce que
Mathlib sait du **premier chapitre** — la série harmonique et son pôle en
`s = 1`, qui force le prolongement — et de sa moitié arithmétique : la
divergence de la somme des inverses des nombres premiers, le fait
d'Euler (1737) dont le mémoire hérite.

## Grounding mesuré (convention de la série)

- Mathlib **ne porte pas** la fonction ζ ni la ligne critique : aucun
  `RiemannZeta` dans l'arbre (v4.33.0, greppé au grain).
- Mathlib **porte** : les p-séries et le test de condensation
  (`Mathlib.Analysis.PSeries`) ; la divergence de la somme des inverses des
  premiers (`Mathlib.NumberTheory.SumPrimeReciprocals`).
- Le prolongement, l'équation fonctionnelle et les zéros restent hors
  Mathlib : ce sont les carnets R-01/R-02 de la série qui les rendent
  **calculables** (`mpmath.zetazero`), pas formels.
-/

import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.SumPrimeReciprocals

namespace Riemann200

/-- **Le pôle en s = 1.** La série harmonique `Σ 1/n` diverge : `ζ(1)`
n'existe pas comme somme, et c'est précisément ce trou que le prolongement
analytique du mémoire vient combler. Ré-export commenté du lemme Mathlib
`Real.not_summable_one_div_natCast` (voie p-séries : `summable_nat_pow_inv`
requiert `1 < p`). -/
theorem pole_en_s_un : ¬ Summable (fun n : ℕ => (1 : ℝ) / n) :=
  Real.not_summable_one_div_natCast

/-- **Euler, 1737 — la moitié arithmétique du produit eulérien.** La somme
des inverses des nombres premiers diverge : les premiers sont « assez
denses » pour que le logarithme du produit eulérien explose en `s = 1`.
C'est le fait dont le mémoire de 1859 hérite directement. Ré-export
commenté du lemme Mathlib `not_summable_one_div_on_primes`. -/
theorem euler_inverses_premiers :
    ¬ Summable (Set.indicator {p | p.Prime} (fun n : ℕ ↦ (1 : ℝ) / n)) :=
  not_summable_one_div_on_primes

/-- Corollaire d'échauffement : chaque somme partielle de la série
harmonique atteint au moins 1. La divergence n'est pas une affaire de
queue lointaine : elle est là dès le premier terme. -/
theorem harmonique_partielle_ge_un (N : ℕ) (hN : 0 < N) :
    1 ≤ ∑ n ∈ Finset.range (N + 1), (1 : ℝ) / (n + 1) := by
  have hsub : ({0} : Finset ℕ) ⊆ Finset.range (N + 1) := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact Finset.mem_range.mpr (by omega)
  calc (1 : ℝ)
      = ∑ n ∈ ({0} : Finset ℕ), (1 : ℝ) / (n + 1) := by
          norm_num [Finset.sum_singleton]
    _ ≤ ∑ n ∈ Finset.range (N + 1), (1 : ℝ) / (n + 1) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun x _ _ => div_nonneg zero_le_one (by positivity))

end Riemann200
