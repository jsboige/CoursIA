import Mathlib.Tactic
import Hecke.HeckeOperator

/-!
# Δ, τ de Ramanujan et l'identité propre `T_p Δ = τ(p) Δ`

Ce module relie le discriminant modulaire Δ — la forme parabolique de
poids 12 — à l'opérateur de Hecke `T_p` formalisé dans `HeckeOperator.lean`.
Il réalise le « coefficient q de Δ » du grain 5 de l'Epic Langlands
(#17969) :

* la troncature du produit d'Euler Δ(q) = q ∏_{m ≥ 1} (1 - qᵐ)²⁴ est
  représentée par **convolution de listes de coefficients ℤ** — l'instance
  `Mul (Polynomial ℤ)` de Mathlib est `noncomputable` au pin de ce lake,
  ce qui interdit toute lecture `decide`/`#eval` via `Polynomial ℤ` ; la
  convolution sur listes est calculable et le noyau la réduit intégralement ;
* `tau n` : la valeur de Ramanujan τ(n), lue sur la troncature au degré 24
  via une table **vérifiée par le noyau** (`tau_values`) : aucune valeur
  n'est codée en dur sans preuve — le `decide` échoue si un seul
  coefficient est faux. Exacte pour `n ≤ 25` ;
* `heckeT_two_isEigen` / `heckeT_three_isEigen` : l'identité propre du
  discriminant `T_p Δ = τ(p) Δ`, vérifiée coefficient par coefficient sur
  les indices `n ≤ 12` (p = 2) et `n ≤ 8` (p = 3) via la lecture entière
  `coeffHeckeT_twelve_int`. La version non bornée exige la théorie des
  formes modulaires (Δ est une forme propre normalisée), hors périmètre
  de ce lake : le noyau vérifie ici ce que la théorie prédit.

**Ponts vers les notebooks** : τ et la lacunarité des puissances de η
sont calculées dans `SymbolicAI/Lean/Serre100/09-congruences-tau-lacunarite-delta.ipynb` ;
le parcours formes modulaires → Hecke → Moonshine vit dans
`SymbolicAI/Lean/Langlands/` (01 et 02). Ce module en est le versant
formel : mêmes nombres, preuve par le noyau.
-/

set_option autoImplicit false

namespace ModularForm

/-- Coefficient d'indice `i` du produit de deux polynômes donnés par
leurs listes de coefficients (convolution). -/
def prodCoeff (as bs : List ℤ) (i : ℕ) : ℤ :=
  (List.range (i + 1)).foldl (fun acc j => acc + as.getD j 0 * bs.getD (i - j) 0) 0

/-- Produit de deux polynômes, tronqué à `N` coefficients. -/
def mulTrunc (N : ℕ) (as bs : List ℤ) : List ℤ :=
  (List.range N).map (prodCoeff as bs)

/-- Coefficients de `(1 - Xᵐ)²⁴` tronqués à `N`, lus sur le binôme :
`C(24, i/m) (-1)^(i/m)` si `m ∣ i` et `i/m ≤ 24`, `0` sinon. -/
def etaFactor (N m : ℕ) : List ℤ :=
  (List.range N).map (fun i =>
    if m ∣ i ∧ i / m ≤ 24 then
      (Nat.choose 24 (i / m) : ℤ) * (if i / m % 2 = 0 then (1 : ℤ) else (-1 : ℤ))
    else 0)

/-- Coefficients de `∏_{1 ≤ m ≤ K} (1 - Xᵐ)²⁴`, tronqués à 26. Le facteur
`m` ne touche pas les degrés `< m` : la lecture est exacte aux indices
concernés dès que `K` est assez grand. -/
def etaProd (K : ℕ) : List ℤ :=
  ((List.range (K + 1)).tail).foldl (fun acc m => mulTrunc 26 acc (etaFactor 26 m)) [1]

/-- Coefficients de `Δ` tronqué : `X ∏_{1 ≤ m ≤ 24} (1 - Xᵐ)²⁴`. Le
décalage initial est le facteur `X` ; la lecture est exacte pour les
indices `≤ 25` (`deltaSeq_stable`). -/
def deltaSeq : List ℤ := 0 :: etaProd 24

/-- τ de Ramanujan : table des valeurs `τ(0..25)` lue sur `deltaSeq` et
**vérifiée par le noyau** (`tau_values` ci-dessous). La lecture retourne
0 au-delà de l'indice 25 : la table sert aux bornes de ce module, pas à
une définition générale de τ. -/
def tau : ℕ → ℤ := fun n =>
  [0, 1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920,
   534612, -370944, -577738, 401856, 1217160, 987136, -6905934, 2727432,
   10661420, -7109760, -4219488, -12830688, 18643272, 21288960,
   -25499225].getD n 0

set_option maxRecDepth 200000 in
/-- Exactitude de la troncature : passer de K = 24 à K = 36 facteurs ne
change aucun des 26 premiers coefficients — les facteurs ajoutés
commencent trop haut pour les toucher. -/
theorem deltaSeq_stable :
    (0 :: etaProd 24).take 26 = (0 :: etaProd 36).take 26 := by
  decide

set_option maxRecDepth 200000 in
/-- La table `tau` coïncide avec les coefficients du produit d'Euler
jusqu'à l'indice 25 : chaque valeur est approuvée par le noyau Lean. -/
theorem tau_values :
    (List.range 26).map tau = deltaSeq.take 26 := by
  decide

/-- Les premières valeurs de τ, telles que le noyau les lit sur le
produit : τ(1) = 1, τ(2) = -24, τ(3) = 252, τ(4) = -1472… -/
theorem tau_first_values :
    (List.range 13).map tau
      = [0, 1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643,
         -115920, 534612, -370944] := by
  decide

/-- Un cas particulier de la multiplicativité de τ sur les indices
premiers entre eux : τ(6) = τ(2) τ(3) = (-24) ⬝ 252 = -6048. -/
theorem tau_mult_two_three : tau 6 = tau 2 * tau 3 := by decide

/-- La lacunarité s'arrête aux portes de Δ (Serre 1985) : τ(25) ≠ 0,
contrairement aux puissances de η qu'il a classifiées lacunaires. -/
theorem tau_lacunarity_stops : tau 25 ≠ 0 := by decide

/-- Lecture entière de la formule des coefficients de Hecke au poids 12 :
appliquer `T_p` à une suite entière vue dans ℂ revient à la formule
combinatoire `a(np) + p¹¹ a(n/p)` sur ℤ. C'est le pont décidable entre
l'organe `coeffHeckeT` (sur ℂ) et les vérifications entières bornées. -/
theorem coeffHeckeT_twelve_int (p : ℕ) (a : ℕ → ℤ) (n : ℕ) :
    coeffHeckeT 12 p (fun m => (a m : ℂ)) n
      = ((a (n * p) + if p ∣ n then (p ^ 11 * a (n / p) : ℤ) else 0 : ℤ) : ℂ) := by
  simp only [coeffHeckeT]
  by_cases h : p ∣ n
  · rw [if_pos h, if_pos h]
    have hp : ((p : ℂ) ^ ((12 : ℤ) - 1)) = ((p ^ 11 : ℤ) : ℂ) := by norm_num
    rw [hp]
    push_cast
    ring
  · rw [if_neg h, if_neg h]
    push_cast
    ring

/-- Cœur entier de l'identité propre pour p = 2 : les douze premiers
coefficients de `T₂ τ` redonnent `τ(2) τ(n)`. -/
theorem hecke_two_eigen_core :
    ∀ n ∈ Finset.Icc 1 12,
      (tau (n * 2) + if (2 : ℕ) ∣ n then ((2 : ℕ) ^ 11 * tau (n / 2) : ℤ) else 0)
        = tau 2 * tau n := by
  decide

/-- **L'identité propre du discriminant, p = 2** : pour chaque indice
`1 ≤ n ≤ 12`, la formule des coefficients de `T₂` appliquée à τ redonne
`τ(2) ⬝ τ(n) = -24 τ(n)`. -/
theorem heckeT_two_isEigen :
    ∀ n ∈ Finset.Icc 1 12,
      coeffHeckeT 12 2 (fun m => (tau m : ℂ)) n = ((-24 : ℤ) : ℂ) * ((tau n : ℤ) : ℂ) := by
  intro n hn
  rw [coeffHeckeT_twelve_int, hecke_two_eigen_core n hn]
  have h2 : tau 2 = -24 := by decide
  rw [h2]
  push_cast
  ring

/-- Cœur entier de l'identité propre pour p = 3 (indices `n ≤ 8`). -/
theorem hecke_three_eigen_core :
    ∀ n ∈ Finset.Icc 1 8,
      (tau (n * 3) + if (3 : ℕ) ∣ n then ((3 : ℕ) ^ 11 * tau (n / 3) : ℤ) else 0)
        = tau 3 * tau n := by
  decide

/-- **L'identité propre du discriminant, p = 3** : pour chaque indice
`1 ≤ n ≤ 8`, `T₃ τ` redonne `τ(3) ⬝ τ(n) = 252 τ(n)`. -/
theorem heckeT_three_isEigen :
    ∀ n ∈ Finset.Icc 1 8,
      coeffHeckeT 12 3 (fun m => (tau m : ℂ)) n = ((252 : ℤ) : ℂ) * ((tau n : ℤ) : ℂ) := by
  intro n hn
  rw [coeffHeckeT_twelve_int, hecke_three_eigen_core n hn]
  have h3 : tau 3 = 252 := by decide
  rw [h3]
  push_cast
  ring

end ModularForm
