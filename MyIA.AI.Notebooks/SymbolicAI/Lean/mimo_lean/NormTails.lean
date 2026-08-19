import Mathlib
import SLT.GaussianLipConcen

/-!
# Grain 3 — Queues de normes ‖w‖, ‖hᵢ‖ (concentration de Lipschitz gaussienne)

Ce module prouve la **concentration des normes** du détecteur MIMO
(papier Papailiopoulos 2026, §11 — cf issue #11148, grain 3) : le bruit
`w` et chaque colonne `hᵢ` du canal (à entrées i.i.d. gaussiennes) sont
des vecteurs gaussiens standards de dimension `M`, et la norme euclidienne
est une fonction **1-Lipschitz** — le théorème de concentration
`gaussian_lipschitz_concentration` du lake externe
`YuanheZ/lean-stat-learning-theory` (SLT) donne donc, pour tout `t > 0`,

    P(|‖X‖ − E‖X‖| ≥ t) ≤ 2·exp(−t²/2).

C'est la **queue de norme** du §11 : elle borne uniformément les tailles
`‖w‖` et `‖hᵢ‖` qui apparaissent dans le score de flip
`s·‖hᵢ‖² + √s·⟪hᵢ,w⟫` (Phase 2, `mimo_flip_cost`) — les grains suivants
combinent ces queues par union bound sur les `N` colonnes. La route
Lipschitz est la version « légère » du §11 : la queue chi-carré de `‖w‖²`
via Hanson–Wright (`chisq_norm_concentration`, Converse.lean — issue
#11152) reste le marteau-pilon pour la forme quadratique, tandis qu'ici la
norme elle-même se concentre en sous-gaussienne avec constante `1`.

Architecture du fichier :

1. `norm_lipschitz_one` — la norme euclidienne sur `EuclideanSpace ℝ (Fin n)`
   est **1-Lipschitz** (inégalité triangulaire inverse, via
   `dist_norm_norm_le`) — le certificat `LipschitzWith` requis par SLT ;
2. `norm_concentration_one_sided` / `norm_concentration` — les théorèmes
   abstraits : concentration (unilatérale, puis bilatérale) de `‖X‖` autour
   de sa moyenne pour `X` gaussien standard de dimension `n`, instances
   directes de `gaussian_lipschitz_concentration(_one_sided)` avec `L = 1` ;
3. `noise_norm_tail_one_sided` / `noise_norm_tail` — instantiations MIMO :
   queue de `‖w‖` (bruit, `M` antennes) ;
4. `column_norm_tail` — instantiation MIMO : queue de `‖hᵢ‖` (une colonne
   du canal, `M` entrées i.i.d. `N(0,1)`).

Axiomes : les trois standards de Mathlib — zéro sorry.
-/

namespace Mimo

open MeasureTheory ProbabilityTheory GaussianMeasure GaussianLipConcen Real
open scoped BigOperators NNReal

/-! ## Brique A — la norme euclidienne est 1-Lipschitz -/

/-- La norme euclidienne sur `EuclideanSpace ℝ (Fin n)` est une fonction
**1-Lipschitz** : `|‖x‖ − ‖y‖| ≤ ‖x − y‖` (inégalité triangulaire inverse).
C'est le certificat `LipschitzWith` que consomme le théorème de concentration
de SLT — `dist_norm_norm_le` + `lipschitzWith_iff_dist_le_mul`. -/
lemma norm_lipschitz_one {n : ℕ} : LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa [dist_eq_norm] using dist_norm_norm_le x y

/-! ## Brique B — concentration de la norme d'un vecteur gaussien standard -/

/-- **Queue de norme unilatérale (forme abstraite).** Pour `X` gaussien
standard sur `EuclideanSpace ℝ (Fin n)` (`n > 0`) et `t > 0`,

    P(‖X‖ − E‖X‖ ≥ t) ≤ exp(−t²/2).

Instance directe de `gaussian_lipschitz_concentration_one_sided` (SLT) avec
`f = ‖·‖` et `L = 1` : `exp(−t²/(2·1²)) = exp(−t²/2)`. -/
theorem norm_concentration_one_sided {n : ℕ} (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    (stdGaussianE n {x : EuclideanSpace ℝ (Fin n) |
      t ≤ ‖x‖ - ∫ y, ‖y‖ ∂(stdGaussianE n)}).toReal ≤
      Real.exp (-(t ^ 2) / 2) := by
  simpa using gaussian_lipschitz_concentration_one_sided (n := n)
    (f := fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) (L := 1) hn (by norm_num)
    (norm_lipschitz_one (n := n)) t ht

/-- **Queue de norme (forme abstraite).** Pour `X` gaussien standard sur
`EuclideanSpace ℝ (Fin n)` (`n > 0`) et `t > 0`,

    P(|‖X‖ − E‖X‖| ≥ t) ≤ 2·exp(−t²/2).

Instance directe de `gaussian_lipschitz_concentration` (SLT) avec la fonction
`f = ‖·‖` et la constante de Lipschitz `L = 1` : la norme est 1-Lipschitz
(`norm_lipschitz_one`), donc la concentration sous-gaussienne s'applique
avec paramètre `1` — `2·exp(−t²/(2·1²)) = 2·exp(−t²/2)`. -/
theorem norm_concentration {n : ℕ} (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    (stdGaussianE n {x : EuclideanSpace ℝ (Fin n) |
      t ≤ |‖x‖ - ∫ y, ‖y‖ ∂(stdGaussianE n)|}).toReal ≤
      2 * Real.exp (-(t ^ 2) / 2) := by
  simpa using gaussian_lipschitz_concentration (n := n)
    (f := fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) (L := 1) hn (by norm_num)
    (norm_lipschitz_one (n := n)) t ht

/-! ## Brique C — instanciations MIMO -/

/-- **Queue unilatérale de la norme du bruit `‖w‖`.** Le bruit `w` du
détecteur MIMO est un vecteur gaussien standard de dimension `M` (une
coordonnée par antenne de mesure) : sa norme se concentre autour de sa
moyenne avec la queue `exp(−t²/2)`. Ceci borne la taille du résidu au point
de départ (`mimoObj_residual_from_zero`, Phase 4). -/
theorem noise_norm_tail_one_sided {M : ℕ} (hM : 0 < M) (t : ℝ) (ht : 0 < t) :
    (stdGaussianE M {w : EuclideanSpace ℝ (Fin M) |
      t ≤ ‖w‖ - ∫ y, ‖y‖ ∂(stdGaussianE M)}).toReal ≤
      Real.exp (-(t ^ 2) / 2) :=
  norm_concentration_one_sided hM t ht

/-- **Queue de la norme du bruit `‖w‖`.** Le bruit `w` du détecteur MIMO est
un vecteur gaussien standard de dimension `M` (une coordonnée par antenne de
mesure) : sa norme se concentre autour de sa moyenne avec la même queue
`2·exp(−t²/2)`. Ceci borne la taille du résidu au point de départ
(`mimoObj_residual_from_zero`, Phase 4). -/
theorem noise_norm_tail {M : ℕ} (hM : 0 < M) (t : ℝ) (ht : 0 < t) :
    (stdGaussianE M {w : EuclideanSpace ℝ (Fin M) |
      t ≤ |‖w‖ - ∫ y, ‖y‖ ∂(stdGaussianE M)|}).toReal ≤
      2 * Real.exp (-(t ^ 2) / 2) :=
  norm_concentration hM t ht

/-- **Queue de la norme d'une colonne `‖hᵢ‖`.** Pour un canal à entrées
i.i.d. `N(0,1)`, la colonne `hᵢ = A eᵢ` est un vecteur gaussien standard de
dimension `M` : sa norme se concentre autour de sa moyenne avec la même queue
`2·exp(−t²/2)`. Ceci borne uniformément les `‖hᵢ‖` du score de flip
`s·‖hᵢ‖² + √s·⟪hᵢ,w⟫` (Phase 2, `mimo_flip_cost`) — le grain suivant
combine ces queues par union bound sur les `N` colonnes. -/
theorem column_norm_tail {M : ℕ} (hM : 0 < M) (t : ℝ) (ht : 0 < t) :
    (stdGaussianE M {h : EuclideanSpace ℝ (Fin M) |
      t ≤ |‖h‖ - ∫ y, ‖y‖ ∂(stdGaussianE M)|}).toReal ≤
      2 * Real.exp (-(t ^ 2) / 2) :=
  norm_concentration hM t ht

end Mimo
