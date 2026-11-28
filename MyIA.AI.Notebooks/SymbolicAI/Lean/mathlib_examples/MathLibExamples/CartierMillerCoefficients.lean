import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import MathLibExamples.CartierMiller

/-!
# Les coefficients binomiaux du point de quart

Le module `CartierMiller` prouve le certificat de télescopage, l'identité préfixe et
l'identité du point de quart **sous** une récurrence locale reçue en hypothèse. Sur
`main`, cette récurrence n'est dischargee que par `decide`, sur les vingt-quatre
indices utiles de `p = 97`, et la base `j = 1728` est construite sans que la suite y
soit branchée. Ce module construit la suite elle-même — `a_i = C(2i,i)·8⁻ⁱ`,
équation (32) du manuscrit — et prouve sa récurrence **à tout indice, dans tout corps
où `8 ≠ 0`**. Les équations (34), (35) et (36) en découlent pour cette suite
explicite : (36) vaut donc en `ZMod p` pour tout premier `p ≡ 1 (mod 4)`, et non plus
seulement pour `p = 97`.

Établi ici : la récurrence, le certificat, l'identité préfixe et l'identité du point de
quart pour la suite binomiale, dans un corps arbitraire puis dans `ZMod p`.

Non établi ici, et à ne pas lire dans ces énoncés : l'identification de `U_p` à la
somme de coefficients de l'évaluation de Cartier–Miller, l'égalité de `a_n` avec la
trace de Frobenius de la courbe d'invariant `j = 1728`, et tout énoncé sur les courbes
elliptiques. Ces branchements sont la suite du plan de l'issue #19452.

Le manuscrit source est un *unrefereed draft* assisté par IA, épinglé à `37a9b72` ; les
énoncés cités sont transcrits des transcriptions du dépôt, et l'oracle numérique
(`scripts/cartier_miller/verify_quarter_point_identities.py`) est une corroboration
d'exécution, jamais une preuve.
-/

namespace CartierMillerCoefficients

open Finset

variable {F : Type*} [Field F]

/-! ### Les identités entières sur les coefficients centraux -/

/-- Identité centrale : `(i+1)·C(2i+1,i) = (2i+1)·C(2i,i)`, forme directe de
`Nat.choose_mul_succ_eq` aux arguments `(2i, i)`. -/
theorem succ_mul_central_choose (i : ℕ) :
    (i + 1) * Nat.choose (2 * i + 1) i = (2 * i + 1) * Nat.choose (2 * i) i := by
  have h := Nat.choose_mul_succ_eq (2 * i) i
  rw [show 2 * i + 1 - i = i + 1 from by omega] at h
  rw [mul_comm (i + 1) (Nat.choose (2 * i + 1) i),
    mul_comm (2 * i + 1) (Nat.choose (2 * i) i)]
  exact h.symm

/-- Pascal doublé : `C(2i+2,i+1) = 2·C(2i+1,i)`, par la symétrie du coefficient
central. -/
theorem central_choose_succ (i : ℕ) :
    Nat.choose (2 * i + 2) (i + 1) = 2 * Nat.choose (2 * i + 1) i := by
  have hsymm : Nat.choose (2 * i + 1) (i + 1) = Nat.choose (2 * i + 1) i := by
    have h := Nat.choose_symm (n := 2 * i + 1) (k := i + 1) (by omega)
    rw [show 2 * i + 1 - (i + 1) = i from by omega] at h
    exact h.symm
  rw [show 2 * i + 2 = 2 * i + 1 + 1 from by omega, Nat.choose_succ_succ', hsymm]
  ring

/-- Le pas entier, sans division : `4(i+1)·C(2i+2,i+1) = 8(2i+1)·C(2i,i)`. C'est le
squelette entier de la récurrence (32) de la suite `aᵢ`. -/
theorem central_binomial_step (i : ℕ) :
    4 * (i + 1) * Nat.choose (2 * (i + 1)) (i + 1) =
      8 * (2 * i + 1) * Nat.choose (2 * i) i := by
  have h2 : 2 * (i + 1) = 2 * i + 2 := by omega
  rw [h2, central_choose_succ]
  have hstep := succ_mul_central_choose i
  linear_combination 8 * hstep

/-! ### La suite `aᵢ = C(2i,i)·8⁻ⁱ` et sa récurrence -/

/-- La suite de l'équation (32), dans un corps arbitraire : `a_i = C(2i,i)·8⁻ⁱ`,
écrite comme puissance de l'inverse. -/
noncomputable def binomialSeq (i : ℕ) : F := (Nat.choose (2 * i) i : F) * 8⁻¹ ^ i

/-- La définition sous la forme du manuscrit : `a_i = C(2i,i) / 8ⁱ`. -/
theorem binomialSeq_eq_division (i : ℕ) :
    binomialSeq (F := F) i = (Nat.choose (2 * i) i : F) / 8 ^ i := by
  simp only [binomialSeq]
  rw [div_eq_mul_inv, ← inv_pow]

/-- Le premier terme, `a_0 = 1`, comme `t_0 = 1` dans (32). -/
theorem binomialSeq_zero : binomialSeq (F := F) 0 = 1 := by
  simp [binomialSeq]

/-- La récurrence locale (32) de la suite binomiale, à **tout** indice, dès que `8`
est inversible : `4(i+1)·a_{i+1} = (2i+1)·a_i`. -/
theorem binomialSeq_recurrence (i : ℕ) (h8 : (8 : F) ≠ 0) :
    4 * ((i : F) + 1) * binomialSeq (F := F) (i + 1) =
      (2 * (i : F) + 1) * binomialSeq (F := F) i := by
  have hnat : ((4 * (i + 1) * Nat.choose (2 * (i + 1)) (i + 1) : ℕ) : F) =
      ((8 * (2 * i + 1) * Nat.choose (2 * i) i : ℕ) : F) := by
    rw [central_binomial_step i]
  push_cast at hnat
  have hinv : (8 : F) * 8⁻¹ = 1 := mul_inv_cancel₀ h8
  simp only [binomialSeq, pow_succ]
  linear_combination (8⁻¹ ^ i * 8⁻¹) * hnat +
    ((2 * (i : F) + 1) * (Nat.choose (2 * i) i : F) * 8⁻¹ ^ i) * hinv

/-! ### Les trois équations du manuscrit, pour la suite explicite -/

/-- (34) : le certificat de télescopage, pour la suite binomiale et à tout indice. -/
theorem binomialSeq_certificate (i : ℕ) (h8 : (8 : F) ≠ 0) :
    ((2 * (i : F) + 1) ^ 2 - 8) * binomialSeq (F := F) i =
      -4 * ((i : F) + 1) * (2 * (i : F) + 7) * binomialSeq (F := F) (i + 1) +
        4 * (i : F) * (2 * (i : F) + 5) * binomialSeq (F := F) i :=
  CartierMiller.telescoping_certificate (binomialSeq i) (binomialSeq (i + 1)) (i : F)
    (binomialSeq_recurrence i h8)

/-- (35) : l'identité préfixe, pour la suite binomiale et à tout préfixe. -/
theorem binomialSeq_prefix (h : F) (L : ℕ) (h8 : (8 : F) ≠ 0) (half : 2 * h + 1 = 0) :
    (∑ i ∈ range L, (h + 1 + (i : F)) * ((2 * (i : F) + 1) * binomialSeq (F := F) i)) =
      4 * (∑ i ∈ range L, binomialSeq (F := F) i) -
        2 * (L : F) * (2 * (L : F) + 5) * binomialSeq (F := F) L :=
  CartierMiller.prefix_sum_identity binomialSeq h L half
    (fun i _ => binomialSeq_recurrence i h8)

/-- (36) : l'identité du point de quart, pour la suite binomiale, dans tout corps. -/
theorem binomialSeq_quarter_point (h : F) (n : ℕ) (h8 : (8 : F) ≠ 0)
    (half : 2 * h + 1 = 0) (quarter : 4 * (n : F) + 1 = 0) (four_ne : (4 : F) ≠ 0) :
    (∑ i ∈ range n, (h + 1 + (i : F)) * ((2 * (i : F) + 1) * binomialSeq (F := F) i)) =
      4 * (∑ i ∈ range n, binomialSeq (F := F) i) + (9 / 4 : F) * binomialSeq (F := F) n :=
  CartierMiller.quarter_point_identity binomialSeq h n half
    (fun i _ => binomialSeq_recurrence i h8) quarter four_ne

/-! ### Modulo un premier : `2`, `4` et `8` sont inversibles -/

/-- Un premier impair ne divise aucune puissance de deux. -/
theorem prime_odd_not_dvd_pow_two {p k : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    ¬ p ∣ 2 ^ k := by
  intro h
  have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h
  rw [Nat.dvd_prime Nat.prime_two] at h2
  rcases h2 with h1 | h2
  · exact hp.ne_one h1
  · exact hp2 h2

/-- Une puissance de deux est non nulle modulo un premier impair. -/
theorem pow_two_ne_zero_zmod (p k : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    ((2 ^ k : ℕ) : ZMod p) ≠ 0 :=
  fun h => prime_odd_not_dvd_pow_two hp hp2 ((ZMod.natCast_eq_zero_iff (2 ^ k) p).mp h)

/-- `2` est inversible modulo un premier impair. -/
theorem two_ne_zero_zmod (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  have h := pow_two_ne_zero_zmod p 1 hp hp2
  simpa using h

/-- `4` est inversible modulo un premier impair. -/
theorem four_ne_zero_zmod (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) : (4 : ZMod p) ≠ 0 := by
  have h := pow_two_ne_zero_zmod p 2 hp hp2
  simpa using h

/-- `8` est inversible modulo un premier impair. -/
theorem eight_ne_zero_zmod (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) : (8 : ZMod p) ≠ 0 := by
  have h := pow_two_ne_zero_zmod p 3 hp hp2
  simpa using h

/-- L'hypothèse `2h + 1 = 0` au point de quart : `h = (p-1)/2`. -/
theorem half_zmod (p : ℕ) (hp4 : p % 4 = 1) :
    (2 : ZMod p) * (((p - 1) / 2 : ℕ) : ZMod p) + 1 = 0 := by
  have h : 2 * ((p - 1) / 2) + 1 = p := by omega
  have hc := congrArg (fun n : ℕ => (n : ZMod p)) h
  push_cast at hc
  rw [ZMod.natCast_self] at hc
  exact hc

/-- L'hypothèse du point de quart : `4n + 1 = 0` pour `n = (p-1)/4`. -/
theorem quarter_zmod (p : ℕ) (hp4 : p % 4 = 1) :
    (4 : ZMod p) * (((p - 1) / 4 : ℕ) : ZMod p) + 1 = 0 := by
  have h : 4 * ((p - 1) / 4) + 1 = p := by omega
  have hc := congrArg (fun n : ℕ => (n : ZMod p)) h
  push_cast at hc
  rw [ZMod.natCast_self] at hc
  exact hc

/-- (36) en `ZMod p` : la congruence du point de quart pour la suite binomiale, pour
tout premier `p ≡ 1 (mod 4)`. Le manuscrit l'énonce sous `p = 4n + 1 ≥ 13` ; le calcul
algébrique n'utilise ni la borne `≥ 13`, ni la primalité au-delà de l'inversibilité de
`2`, `4` et `8`. -/
theorem quarter_point_congruence (p : ℕ) [Fact (Nat.Prime p)] (hp4 : p % 4 = 1) :
    (∑ i ∈ range ((p - 1) / 4),
        ((((p - 1) / 2 : ℕ) : ZMod p) + 1 + (i : ZMod p)) *
          ((2 * (i : ZMod p) + 1) * binomialSeq (F := ZMod p) i)) =
      4 * (∑ i ∈ range ((p - 1) / 4), binomialSeq (F := ZMod p) i) +
        (9 / 4 : ZMod p) * binomialSeq (F := ZMod p) ((p - 1) / 4) := by
  have hp : Nat.Prime p := Fact.out
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hp4
    norm_num at hp4
  exact binomialSeq_quarter_point (F := ZMod p) (((p - 1) / 2 : ℕ) : ZMod p) ((p - 1) / 4)
    (eight_ne_zero_zmod p hp hp2) (half_zmod p hp4) (quarter_zmod p hp4)
    (four_ne_zero_zmod p hp hp2)

/-- À `p = 97`, la suite générale coïncide avec l'oracle du dépôt : la valeur
`decide`-vérifiée sur `main` devient l'instance d'un théorème. -/
theorem binomialSeq_eq_oracle97 (i : ℕ) :
    binomialSeq (F := ZMod 97) i = CartierMiller.oracle97 i := by
  rw [binomialSeq_eq_division, CartierMiller.oracle97_binomial]

/-- Le cas chiffré du manuscrit (`p = 97`, `n = 24`) comme instance de la congruence
générale. -/
theorem quarter_point_congruence_97 :
    (∑ i ∈ range 24, (48 + 1 + (i : ZMod 97)) *
        ((2 * (i : ZMod 97) + 1) * binomialSeq (F := ZMod 97) i)) =
      4 * (∑ i ∈ range 24, binomialSeq (F := ZMod 97) i) +
        (9 / 4 : ZMod 97) * binomialSeq (F := ZMod 97) 24 := by
  have h := quarter_point_congruence 97 (by decide)
  simpa using h

end CartierMillerCoefficients
