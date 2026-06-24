import Mathlib

/-!
# Minimax.ZeroSum — jeux à somme nulle finis : matrice, stratégies mixtes, payoff

Un jeu à somme nulle fini à deux joueurs : le joueur-ligne choisit une ligne `i`, le
joueur-colonne une colonne `j`, et le joueur-ligne reçoit le gain `A i j` (le
joueur-colonne reçoit `-A i j`). En **stratégie mixte**, chaque joueur tire selon une
distribution de probabilité ; l'espérance du gain du joueur-ligne est le **payoff
bilinéaire** `xᵀ A y = Σᵢⱼ xᵢ Aᵢⱼ yⱼ`, où `x` et `y` sont des points du simplexe
probabilité (`stdSimplex`).

Ce module pose les définitions et prouve la **bilinearité** du payoff (clé pour appliquer
Sion) : `payoff` est affine en chaque variable séparément, donc à la fois continu et
quasi-convexe/quasi-concave — exactement les hypothèses de `Sion.exists_isSaddlePointOn'`
(voir `Minimax.lean`).

Référence croisée : la série `GameTheory` (Nash existe déjà via `lean_game_defs/Nash.lean`,
dont ce lake est la spécialisation somme nulle). Voir issue #4054.
-/

namespace MinimaxLean

open Finset

variable {m n : Type*} [Fintype m] [Fintype n]

/-- La matrice de gains d'un jeu à somme nulle (lignes = joueur-ligne, colonnes =
    joueur-colonne). `A i j` = gain du joueur-ligne quand i joue ligne `i`, j joue
    colonne `j`. -/
abbrev PayoffMatrix (m n : Type*) := Matrix m n ℝ

/-- Le **payoff bilinéaire** espéré : `payoff A x y = Σᵢⱼ xᵢ · Aᵢⱼ · yⱼ` (somme sur le
    produit `m × n`). C'est l'espérance du gain du joueur-ligne sous les stratégies
    mixtes `x` (lignes) et `y` (colonnes). La représentation comme **somme unique sur le
    produit** rend la bilinéarité immédiate (`sum_add_distrib` / `sum_mul` en une
    étape). -/
def payoff (A : PayoffMatrix m n) (x : m → ℝ) (y : n → ℝ) : ℝ :=
  ∑ ij : m × n, x ij.1 * A ij.1 ij.2 * y ij.2

/-- **Additivité en `x`** : le payoff est additif en la stratégie du joueur-ligne
    (première moitié de la linéarité). -/
lemma payoff_add_in_x (A : PayoffMatrix m n) (x x' : m → ℝ) (y : n → ℝ) :
    payoff A (x + x') y = payoff A x y + payoff A x' y := by
  simp only [payoff, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- **Homogénéité en `x`** : le payoff est homogène en la stratégie du joueur-ligne
    (seconde moitié de la linéarité). -/
lemma payoff_smul_in_x (A : PayoffMatrix m n) (c : ℝ) (x : m → ℝ) (y : n → ℝ) :
    payoff A (c • x) y = c * payoff A x y := by
  simp only [payoff, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1 with ij
  ring

/-- **Additivité en `y`** : le payoff est additif en la stratégie du joueur-colonne
    (première moitié de la linéarité en `y`). -/
lemma payoff_add_in_y (A : PayoffMatrix m n) (x : m → ℝ) (y y' : n → ℝ) :
    payoff A x (y + y') = payoff A x y + payoff A x y' := by
  simp only [payoff, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- **Homogénéité en `y`** : le payoff est homogène en la stratégie du joueur-colonne
    (seconde moitié de la linéarité en `y`). -/
lemma payoff_smul_in_y (A : PayoffMatrix m n) (c : ℝ) (x : m → ℝ) (y : n → ℝ) :
    payoff A x (c • y) = c * payoff A x y := by
  simp only [payoff, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1 with ij
  ring

/-- Le payoff est **continu** (jointement) car somme finie de monômes continus. C'est le
    fait clé qui donne, par restriction, la semi-continuité supérieure et inférieure
    requise par Sion. -/
lemma continuous_payoff (A : PayoffMatrix m n) :
    Continuous (fun p : (m → ℝ) × (n → ℝ) => payoff A p.1 p.2) := by
  unfold payoff
  apply continuous_finsetSum
  intro ij _
  fun_prop

/-- Le payoff `payoff A · y` est **continu** en la stratégie du joueur-ligne (cas
    particulier de `continuous_payoff`, par restriction `y` = constante). -/
lemma continuous_payoff_in_x (A : PayoffMatrix m n) (y : n → ℝ) :
    Continuous (fun x : m → ℝ => payoff A x y) := by
  unfold payoff
  fun_prop

/-- Le payoff `payoff A x ·` est **continu** en la stratégie du joueur-colonne (cas
    particulier de `continuous_payoff`, par restriction `x` = constante). -/
lemma continuous_payoff_in_y (A : PayoffMatrix m n) (x : m → ℝ) :
    Continuous (fun y : n → ℝ => payoff A x y) := by
  unfold payoff
  fun_prop

end MinimaxLean
