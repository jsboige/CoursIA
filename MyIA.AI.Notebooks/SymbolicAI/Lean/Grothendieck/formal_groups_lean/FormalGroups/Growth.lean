import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Croissance des algèbres graduées : les lemmes de comptage

Ce module formalise les lemmes de comptage sur lesquels repose le calcul de
la dimension de Gelfand–Kirillov mené par le carnet
`GROTH-05b-GelfandKirillov-Python.ipynb` (issue #27589) : la fonction de
Hilbert cumulée d'un anneau de polynômes, sa croissance stricte, le compte
des mots de l'algèbre libre, et le lemme de sous-multiplicativité qui force
la croissance exponentielle d'une algèbre graduée engendrée en degré un.

Ce module **ne définit pas** la dimension de Gelfand–Kirillov : Mathlib ne
la porte pas, et le carnet le dit. Il ne prouve pas non plus le théorème du
trou de Smoktunowicz ni l'asymptotique `log(dim A_n) / log n`. Il tient les
faits de comptage qu'un étudiant peut rejouer, à la frontière exacte que le
carnet désigne :

-  `hilbertCumule d n` : monômes de degré au plus `n` en `d` variables,
   `C(n + d, d)` ;
-  `hilbertCouche d n` : monômes de degré exactement `n`, `C(n + d - 1, d - 1)` ;
-  `motsLibres d n` : mots de longueur au plus `n` sur `d` lettres, `2^(n+1) - 1`
   pour `d = 2` ;
-  `hilbertCumule_deux_lt_motsLibres_deux` : dès le rang `2`, la croissance
   polynomiale de `k[x, y]` passe sous la croissance exponentielle de
   `k⟨x, y⟩` ;
-  `sous_multiplicative_le_pow` : une suite de dimensions sous-multiplicative
   est majorée par les puissances de son premier terme.

Les références bibliographiques du contexte sont celles du carnet, section
« Références » ; ce module ne dépend d'aucune publication.
-/

set_option autoImplicit false

namespace FormalGroups

/-! ### Fonction de Hilbert d'un anneau de polynômes -/

/-- Nombre de monômes de degré **au plus** `n` en `d` indéterminées : c'est
`dim A_n` pour `A = k[x_1, …, x_d]` gradué par le degré total. -/
def hilbertCumule (d n : ℕ) : ℕ := (n + d).choose d

/-- Nombre de monômes de degré **exactement** `n` en `d` indéterminées
(`d ≥ 1`) : la couche `A_n / A_{n-1}` de la filtration. -/
def hilbertCouche (d n : ℕ) : ℕ := (n + d - 1).choose (d - 1)

/-- En zéro indéterminée il n'y a qu'un monôme : la constante. -/
@[simp]
theorem hilbertCumule_zero_indet (n : ℕ) : hilbertCumule 0 n = 1 := by
  simp [hilbertCumule]

/-- En une indéterminée, `dim A_n = n + 1` : la croissance linéaire. -/
theorem hilbertCumule_one_indet (n : ℕ) : hilbertCumule 1 n = n + 1 := by
  simp [hilbertCumule]

/-- En deux indéterminées, `dim A_n = (n+1)(n+2)/2` : la croissance
quadratique, la valeur que le carnet mesure pour `k[x,y]`. -/
theorem hilbertCumule_two_indet (n : ℕ) :
    hilbertCumule 2 n = (n + 1) * (n + 2) / 2 := by
  have h : n + 2 - 1 = n + 1 := by omega
  simp only [hilbertCumule]
  rw [Nat.choose_two_right, h, Nat.mul_comm]

/-- La couche de degré `n + 1` complète la cumulée : c'est l'identité de
Pascal `C(n+1+d, d) = C(n+d, d) + C(n+d, d-1)`. -/
theorem hilbertCumule_succ (d n : ℕ) :
    hilbertCumule (d + 1) (n + 1) =
      hilbertCumule (d + 1) n + hilbertCouche (d + 1) (n + 1) := by
  have h1 : n + 1 + (d + 1) = n + d + 1 + 1 := by omega
  have h2 : n + (d + 1) = n + d + 1 := by omega
  have h3 : n + 1 + (d + 1) - 1 = n + d + 1 := by omega
  have h4 : d + 1 - 1 = d := by omega
  simp only [hilbertCumule, hilbertCouche]
  rw [h3, h4, h1, h2]
  simpa [Nat.add_comm] using Nat.choose_succ_succ' (n + d + 1) d

/-- La cumulée croît avec le degré : `dim A_n ≤ dim A_{n+1}`. -/
theorem hilbertCumule_monotone (d : ℕ) : Monotone (hilbertCumule d) := by
  intro m n hmn
  simp only [hilbertCumule]
  exact Nat.choose_le_choose (a := m + d) (b := n + d) d (by omega)

/-- Pour `d ≥ 1`, chaque couche est non vide : la croissance est stricte. -/
theorem hilbertCumule_lt_succ (d n : ℕ) (hd : 1 ≤ d) :
    hilbertCumule d n < hilbertCumule d (n + 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [hilbertCumule_succ]
  have hpos : 0 < hilbertCouche (e + 1) (n + 1) := by
    unfold hilbertCouche
    rw [show n + 1 + (e + 1) - 1 = n + e + 1 by omega,
      show e + 1 - 1 = e by omega]
    exact Nat.choose_pos (by omega)
  omega

/-- En deux indéterminées, la couche de degré `n` compte `n + 1` monômes :
`x^n, x^{n-1} y, …, y^n`. -/
theorem hilbertCouche_deux (n : ℕ) : hilbertCouche 2 n = n + 1 := by
  have h : hilbertCouche 2 n = (n + 2 - 1).choose 1 := rfl
  rw [h, Nat.choose_one_right]
  omega

/-- En deux indéterminées, l'identité de Pascal se lit
`dim A_{n+1} = dim A_n + (n + 2)` : l'anneau de polynômes grandit en ajoutant
une couche. -/
theorem hilbertCumule_deux_succ (n : ℕ) :
    hilbertCumule 2 (n + 1) = hilbertCumule 2 n + (n + 2) := by
  have h : hilbertCumule 2 (n + 1)
      = hilbertCumule 2 n + hilbertCouche 2 (n + 1) :=
    hilbertCumule_succ 1 n
  rw [h, hilbertCouche_deux]

/-- Dès le rang `2`, la couche du rang suivant ne dépasse pas la cumulée :
`n + 2 ≤ dim A_n` pour `A = k[x, y]`. -/
theorem hilbertCumule_deux_ge_add_two (n : ℕ) (hn : 2 ≤ n) :
    n + 2 ≤ hilbertCumule 2 n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 : hilbertCumule 2 (m + 2) = hilbertCumule 2 (m + 1) + (m + 3) :=
    hilbertCumule_deux_succ (m + 1)
  have h2 : hilbertCumule 2 (m + 1) = hilbertCumule 2 m + (m + 2) :=
    hilbertCumule_deux_succ m
  omega

/-! ### L'algèbre libre : le compte des mots -/

/-- Nombre de mots de longueur **au plus** `n` sur un alphabet de `d`
lettres — c'est `dim A_n` pour l'algèbre libre `k⟨x_1, …, x_d⟩`. La
définition est par récurrence (`motsLibres d (n+1) = motsLibres d n + d^(n+1)`) ;
elle compte la même chose que la somme des `d^k` pour `k` de `0` à `n`. -/
def motsLibres (d : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => motsLibres d n + d ^ (n + 1)

/-- Sur deux lettres, `1 + 2 + … + 2^n = 2^(n+1) - 1` : la valeur que le
carnet mesure pour l'algèbre libre `k⟨x,y⟩`. -/
theorem motsLibres_deux (n : ℕ) : motsLibres 2 n = 2 ^ (n + 1) - 1 := by
  induction n with
  | zero => simp [motsLibres]
  | succ n ih =>
      simp only [motsLibres]
      rw [ih, show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ]
      have hpos : 0 < 2 ^ (n + 1) := by positivity
      omega

/-- Conséquence : l'algèbre libre sur deux lettres a `dim A_n ≥ 2^n`, donc
aucune borne polynomiale — sa dimension de Gelfand–Kirillov est infinie. -/
theorem motsLibres_deux_ge_pow (n : ℕ) : 2 ^ n ≤ motsLibres 2 n := by
  rw [motsLibres_deux]
  have hpos : 0 < 2 ^ n := by positivity
  rw [pow_succ]
  omega

/-- Sur deux lettres, le passage au rang suivant double le compte des mots :
un mot non vide de longueur au plus `n + 1` est une lettre suivie d'un mot de
longueur au plus `n`, et il faut compter le mot vide. -/
theorem motsLibres_deux_succ (n : ℕ) :
    motsLibres 2 (n + 1) = 2 * motsLibres 2 n + 1 := by
  have hpos : 0 < 2 ^ (n + 1) := by positivity
  have h : motsLibres 2 n + 1 = 2 ^ (n + 1) := by
    rw [motsLibres_deux]
    omega
  simp only [motsLibres]
  omega

/-! ### Polynomiale contre exponentielle -/

/-- **Polynomiale contre exponentielle.** Dès le rang `2`, la fonction de
Hilbert cumulée de `k[x, y]` est strictement inférieure au compte des mots de
l'algèbre libre `k⟨x, y⟩` : la croissance polynomiale ne rattrape jamais la
croissance exponentielle. La preuve compare les deux récurrences — l'anneau de
polynômes ajoute une couche de `n + 2` monômes quand l'algèbre libre double
son compte. -/
theorem hilbertCumule_deux_lt_motsLibres_deux (n : ℕ) (hn : 2 ≤ n) :
    hilbertCumule 2 n < motsLibres 2 n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  induction m with
  | zero =>
      rw [hilbertCumule_two_indet, motsLibres_deux]
      norm_num
  | succ m ih =>
      rw [show m + 1 + 2 = m + 2 + 1 by omega]
      rw [hilbertCumule_deux_succ, motsLibres_deux_succ]
      have hle : m + 2 + 2 ≤ hilbertCumule 2 (m + 2) :=
        hilbertCumule_deux_ge_add_two (m + 2) (by omega)
      omega

/-- Aux rangs `0` et `1`, les deux comptes coïncident (la constante, puis le
mot vide et les deux lettres) : le rang `2` du théorème précédent est le
premier où l'algèbre libre dépasse l'anneau de polynômes. -/
theorem hilbertCumule_deux_eq_motsLibres_deux (n : ℕ) (hn : n < 2) :
    hilbertCumule 2 n = motsLibres 2 n := by
  interval_cases n
  · rw [hilbertCumule_two_indet, motsLibres_deux]
    norm_num
  · rw [hilbertCumule_two_indet, motsLibres_deux]
    norm_num

/-! ### Sous-multiplicativité : la croissance exponentielle est inévitable -/

/-- **Lemme de sous-multiplicativité.** Si les dimensions d'une algèbre
graduée vérifient `dim A_{m+n} ≤ dim A_m · dim A_n` — l'image du produit
`A_m ⊗ A_n → A_{m+n}` est tout `A_{m+n}` — et `dim A_0 = 1`, alors
`dim A_n ≤ (dim A_1)^n`. C'est la moitié facile du calcul de la dimension de
Gelfand–Kirillov : dès que `dim A_1 ≥ 2`, la croissance est au moins
exponentielle. -/
theorem sous_multiplicative_le_pow (a : ℕ → ℕ) (h0 : a 0 = 1)
    (h : ∀ m n : ℕ, a (m + n) ≤ a m * a n) : ∀ n : ℕ, a n ≤ a 1 ^ n
  | 0 => by simp [h0]
  | n + 1 => by
      have hstep : a (n + 1) ≤ a n * a 1 := by
        simpa [Nat.add_comm] using h n 1
      calc a (n + 1) ≤ a n * a 1 := hstep
        _ ≤ a 1 ^ n * a 1 :=
            Nat.mul_le_mul_right _ (sous_multiplicative_le_pow a h0 h n)
        _ = a 1 ^ (n + 1) := by rw [pow_succ]

/-- Le compte des mots de l'algèbre libre satisfait l'hypothèse du lemme,
et sa dimension de degré un vaut `2` : c'est l'exemple même où la croissance
exponentielle est forcée. -/
theorem motsLibres_sous_multiplicative (m n : ℕ) :
    motsLibres 2 (m + n) ≤ motsLibres 2 m * motsLibres 2 n := by
  rw [motsLibres_deux, motsLibres_deux, motsLibres_deux]
  have h1 : 0 < 2 ^ (m + n + 1) := by positivity
  have h2 : 0 < 2 ^ (m + 1) := by positivity
  have h3 : 0 < 2 ^ (n + 1) := by positivity
  zify [h1, h2, h3]
  rw [show (2 : ℤ) ^ (m + n + 1) = 2 ^ (m + 1) * 2 ^ n by
        rw [show m + n + 1 = (m + 1) + n by omega, pow_add]]
  rw [show (2 : ℤ) ^ (n + 1) = 2 ^ n * 2 by rw [pow_succ]]
  have hA : (2 : ℤ) ≤ 2 ^ (m + 1) := by
    rw [pow_succ]
    have hp : (0 : ℤ) < 2 ^ m := by positivity
    linarith
  have hB : (1 : ℤ) ≤ 2 ^ n := by
    have hp : (0 : ℤ) < 2 ^ n := by positivity
    linarith
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 ^ (m + 1) - 2 by linarith)
                      (show (0 : ℤ) ≤ 2 ^ n - 1 by linarith)]

end FormalGroups
