/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapté à `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

Le source Dahia original vit dans le dépôt `gdahia/Komlos` (module
`Komlos/SignedSums.lean`, toolchain v4.34.0, cadre `Finsupp` sur `E →₀ ℝ`).
L'assemblage final — l'itération `induction n with` du Lemme 1.4 — s'y lit
l.37-58. Ce module du lake ouvre la distillation : la première brique
`sum_smul_inl` y est livrée générique, la carte de consommation des organes
est mesurée en tête de module, la décision de cadre (option (c),
arbitrée en k2.6a) y est consignée.
-/

import Discrepancy.Basic

/-!
# Sommes signées — assemblage du Lemme 1.4 (brique k2.6)

L'objectif de ce module est l'assemblage final de la voie élémentaire
(Karingula–Lovett) : l'itération `induction n with` de l'oracle
`gdahia/Komlos` (`SignedSums.lean` l.37-58) qui consomme
`mean_mem_convexHull` en base (l.42), `mean_split` + `sum_smul_inl`
au pas (l.53) et `pullback` en clôture (l.55).

## Carte de généricité (mesurée au 2026-10-06, k2.5 tip 87b4f35871)

L'induction de l'oracle ré-instancie ses organes à chaque niveau sur un
ambiant croissant `E → E × ℝ → (E × ℝ) × ℝ → …` — c'est la généralité de
`E` qui absorbe la croissance. Les organes k2.0–k2.5 du lake sont
monomorphes (`Fin d → ℤ`, hauteur `Bool`) :

| Organe oracle | Notre lake | État |
|---|---|---|
| `split : (E →₀ ℝ) → (E × ℝ →₀ ℝ)` | `Split.split` (`Fin d → ℤ`, `× Bool`) | monomorphe |
| `mean_split` (barycentre conservé) | `MeanSplit.mean_split_of_support` | monomorphe |
| `shiftDist_split_le` | acquis k1.6 | monomorphe |
| `splitBit_eq` | `SplitBit` | monomorphe |
| `pullback` (générique) | `Pullback.pullback` (`toReal`/`toRealProd`) | monomorphe |
| `mean_mem_convexHull` | `Distribution.mean_mem_convexHull` (k2.5) | monomorphe |
| `sum_smul_inl` | **absent — livré ci-dessous, générique** | ✓ k2.6 |
| convexHull (`add_smul`/`sum_smul`/`mem_convexHull'`) | `Pullback` l.150/189/213 | ✓ génériques |

L'écart d'architecture est **arbitré en k2.6a** (option (c) : l'espace
qui grandit est réalisé `Fin (d + k) → ℤ` par l'embedding `liftUp`, sans
re-généralisation des organes — la voie α est écartée, la voie β
(ping-pong deux espaces) est close par la mesure). `sum_smul_inl` reste
l'organe générique ℝ-modulaire, **complémentaire de `sum_smul_snoc`**
(k2.6a, forme lake côté grille) : consommable côté transport/hull, où
les moments vivent dans `ℝ`.
-/

namespace Discrepancy.Komlos

/-- La composante gauche d'une somme de vecteurs `ε i • (v i, 0)` est la
somme des composantes gauches — le pendant `Finset` du `sum_smul_inl` de
l'oracle (`split.lean` l.50), utilisé par la réécriture `rw [mean_split,
sum_smul_inl, …]` du pas inductif. Générique en `E` : c'est le seul
organe du pas que le lake n'avait pas, et il ne dépend pas de la grille. -/
lemma sum_smul_inl {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (ε : Fin n → ℝ) (v : Fin n → E) :
    (∑ i, ε i • (v i, (0 : ℝ))) = (∑ i, ε i • v i, (0 : ℝ)) := by
  refine Prod.ext ?_ ?_ <;> simp [Prod.smul_mk, Prod.fst_sum, Prod.snd_sum]

end Discrepancy.Komlos
