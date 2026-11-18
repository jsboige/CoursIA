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

Mesuré au pin Mathlib du lake (`db584cd6d4`, greppé dans
`.lake/packages/mathlib`) :

- Mathlib **porte** la fonction ζ, son prolongement et son équation
  fonctionnelle : `def riemannZeta := hurwitzZetaEven 0`
  (`Mathlib.NumberTheory.LSeries.RiemannZeta:121`),
  `differentiableAt_riemannZeta` hors de `s = 1` (l.139) et
  `riemannZeta_one_sub` (l.178), qui énonce
  `ζ(1 − s) = 2 · (2π)^(−s) · Γ(s) · cos(πs/2) · ζ(s)`.
- Mathlib **porte** un début de zérologie : les zéros triviaux
  (`riemannZeta_neg_two_mul_nat_add_one`, l.173) et l'ensemble
  `riemannZetaZeros`, fermé, discret, d'intersection finie avec tout compact
  (`Mathlib.NumberTheory.LSeries.ZetaZeros`, l.35-66). Elle **énonce**
  l'hypothèse de Riemann (`def RiemannHypothesis`, l.185) sans la prouver :
  la localisation des zéros sur la droite critique reste ouverte.
- Mathlib **porte** aussi : les p-séries et le test de condensation
  (`Mathlib.Analysis.PSeries`) ; la divergence de la somme des inverses des
  premiers (`Mathlib.NumberTheory.SumPrimeReciprocals`).
- Ce que ce module apporte n'est donc pas l'existence formelle de ζ : c'est
  le **fil du mémoire** — le pôle en `s = 1`, le fait d'Euler de 1737, et
  leurs ré-exports commentés. Les carnets R-01/R-02 rendent les zéros
  **calculables** (`mpmath.zetazero`) ; ils ne sont pas seuls à les rendre
  formels.
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
